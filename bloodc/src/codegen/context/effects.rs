//! Effects system codegen.
//!
//! This module handles compilation of:
//! - Perform expressions (effect operation invocations)
//! - Resume expressions (continuation resumption)
//! - Handle expressions (handler installation)
//!
//! Implementation follows:
//! - [Generalized Evidence Passing for Effect Handlers](https://dl.acm.org/doi/10.1145/3473576) (ICFP'21)
//! - [Zero-Overhead Lexical Effect Handlers](https://doi.org/10.1145/3763177) (OOPSLA'25)

use inkwell::values::BasicValueEnum;

use crate::hir::{self, Type, DefId};
use crate::diagnostics::Diagnostic;
use crate::span::Span;
use crate::ice_err;

use super::CodegenContext;

impl<'ctx, 'a> CodegenContext<'ctx, 'a> {
    /// Compile a perform expression: `perform Effect.op(args)`
    ///
    /// In the evidence passing model (ICFP'21), this becomes a call through
    /// the evidence vector via `blood_perform` runtime function.
    pub(super) fn compile_perform(
        &mut self,
        effect_id: DefId,
        op_index: u32,
        args: &[hir::Expr],
        result_ty: &Type,
    ) -> Result<Option<BasicValueEnum<'ctx>>, Vec<Diagnostic>> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        // Get blood_perform runtime function
        let perform_fn = self.module.get_function("blood_perform")
            .ok_or_else(|| vec![Diagnostic::error(
                "Runtime function blood_perform not found".to_string(),
                Span::dummy(),
            )])?;

        // Compile arguments and pack into an i64 array
        let mut compiled_args = Vec::with_capacity(args.len());
        for arg in args {
            if let Some(val) = self.compile_expr(arg)? {
                // Convert to i64 for uniform argument passing
                let i64_val = match val {
                    BasicValueEnum::IntValue(iv) => {
                        if iv.get_type().get_bit_width() == 64 {
                            iv
                        } else {
                            self.builder
                                .build_int_s_extend(iv, i64_type, "arg_ext")
                                .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
                        }
                    }
                    BasicValueEnum::FloatValue(fv) => {
                        // Bitcast float to i64 for passing through uniform interface
                        self.builder
                            .build_bit_cast(fv, i64_type, "float_as_i64")
                            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
                            .into_int_value()
                    }
                    BasicValueEnum::PointerValue(pv) => {
                        self.builder
                            .build_ptr_to_int(pv, i64_type, "ptr_as_i64")
                            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
                    }
                    other => {
                        return Err(vec![ice_err!(
                            arg.span,
                            "unsupported argument type in perform expression";
                            "type" => other.get_type(),
                            "expected" => "IntValue, FloatValue, or PointerValue"
                        )]);
                    }
                };
                compiled_args.push(i64_val);
            }
        }

        // Allocate stack space for arguments array
        let arg_count = compiled_args.len();
        let args_array = if arg_count > 0 {
            let array_type = i64_type.array_type(arg_count as u32);
            let args_alloca = self.builder
                .build_alloca(array_type, "perform_args")
                .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

            // Store each argument in the array
            let zero = i32_type.const_zero();
            for (i, arg_val) in compiled_args.iter().enumerate() {
                let idx = i32_type.const_int(i as u64, false);
                let gep = unsafe {
                    self.builder.build_gep(
                        args_alloca,
                        &[zero, idx],
                        &format!("arg_ptr_{}", i),
                    )
                }.map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

                self.builder
                    .build_store(gep, *arg_val)
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
            }

            // Get pointer to first element
            unsafe {
                self.builder.build_gep(
                    args_alloca,
                    &[zero, zero],
                    "args_ptr",
                )
            }.map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
        } else {
            // No arguments - pass null pointer
            i64_type.ptr_type(inkwell::AddressSpace::default()).const_null()
        };

        // Call blood_perform(effect_id, op_index, args, arg_count)
        let effect_id_val = i64_type.const_int(effect_id.index as u64, false);
        let op_index_val = i32_type.const_int(op_index as u64, false);
        let arg_count_val = i64_type.const_int(arg_count as u64, false);

        let call_result = self.builder
            .build_call(
                perform_fn,
                &[
                    effect_id_val.into(),
                    op_index_val.into(),
                    args_array.into(),
                    arg_count_val.into(),
                ],
                "perform_result",
            )
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

        // Get the result value and convert to appropriate type
        if result_ty.is_unit() {
            Ok(None)
        } else {
            let result_i64 = call_result.try_as_basic_value().left()
                .ok_or_else(|| vec![Diagnostic::error(
                    "blood_perform returned void unexpectedly".to_string(),
                    Span::dummy(),
                )])?;

            // Convert result from i64 to expected type
            let result_llvm_type = self.lower_type(result_ty);
            let converted_result = if result_llvm_type.is_int_type() {
                let result_int_type = result_llvm_type.into_int_type();
                if result_int_type.get_bit_width() == 64 {
                    result_i64
                } else {
                    self.builder
                        .build_int_truncate(result_i64.into_int_value(), result_int_type, "result_trunc")
                        .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
                        .into()
                }
            } else if result_llvm_type.is_float_type() {
                self.builder
                    .build_bit_cast(result_i64, result_llvm_type, "result_float")
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
            } else if result_llvm_type.is_pointer_type() {
                self.builder
                    .build_int_to_ptr(result_i64.into_int_value(), result_llvm_type.into_pointer_type(), "result_ptr")
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
                    .into()
            } else {
                result_i64
            };

            Ok(Some(converted_result))
        }
    }

    /// Compile a resume expression: `resume(value)`
    ///
    /// For tail-resumptive handlers, resume is a simple return.
    /// For general handlers, this requires continuation capture (Phase 2.3).
    pub(super) fn compile_resume(
        &mut self,
        value: Option<&hir::Expr>,
        _result_ty: &Type,
    ) -> Result<Option<BasicValueEnum<'ctx>>, Vec<Diagnostic>> {
        // Phase 2.1: Tail-resumptive optimization only
        //
        // For tail-resumptive handlers (State, Reader, Writer), resume at tail
        // position is just returning the value.

        // Get the current function's return type to properly convert the value
        let fn_value = self.current_fn.ok_or_else(|| vec![Diagnostic::error(
            "resume called outside of function".to_string(), Span::dummy()
        )])?;
        let fn_ret_ty = fn_value.get_type().get_return_type();
        let i64_type = self.context.i64_type();

        if let Some(val_expr) = value {
            let val = self.compile_expr(val_expr)?;
            if let Some(ret_val) = val {
                // Check if we need to convert to i64 (for handler operations)
                let converted_ret = if fn_ret_ty == Some(i64_type.into()) {
                    match ret_val {
                        BasicValueEnum::IntValue(iv) => {
                            if iv.get_type().get_bit_width() == 64 {
                                iv.into()
                            } else {
                                self.builder
                                    .build_int_s_extend(iv, i64_type, "resume_ext")
                                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
                                    .into()
                            }
                        }
                        BasicValueEnum::PointerValue(pv) => {
                            self.builder
                                .build_ptr_to_int(pv, i64_type, "resume_ptr_int")
                                .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
                                .into()
                        }
                        BasicValueEnum::StructValue(_sv) => {
                            // For unit type (empty struct), return 0
                            i64_type.const_zero().into()
                        }
                        other => other,
                    }
                } else {
                    ret_val
                };
                self.builder.build_return(Some(&converted_ret))
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
            } else {
                // No value - return 0 for i64 or void
                if fn_ret_ty == Some(i64_type.into()) {
                    self.builder.build_return(Some(&i64_type.const_zero()))
                        .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
                } else {
                    self.builder.build_return(None)
                        .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
                }
            }
        } else {
            // No value - return 0 for i64 or void
            if fn_ret_ty == Some(i64_type.into()) {
                self.builder.build_return(Some(&i64_type.const_zero()))
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
            } else {
                self.builder.build_return(None)
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
            }
        }

        // Resume doesn't produce a value (control flow transfers)
        Ok(None)
    }

    /// Compile a handle expression: `handle { body } with { handler }`
    ///
    /// This sets up the evidence vector and runs the body with the handler
    /// installed.
    pub(super) fn compile_handle(
        &mut self,
        body: &hir::Expr,
        handler_id: DefId,
        _handler_instance: &hir::Expr,
        result_ty: &Type,
    ) -> Result<Option<BasicValueEnum<'ctx>>, Vec<Diagnostic>> {
        // Phase 2.4: Evidence vector setup
        //
        // Note: This is the HIR codegen path. The MIR codegen path is preferred
        // and handles handler_instance properly for state setup.
        //
        // 1. Create evidence vector (or get existing one)
        // 2. Push handler onto evidence vector
        // 3. Compile body
        // 4. Pop handler from evidence vector
        // 5. Return result

        // Get runtime functions
        let ev_create = self.module.get_function("blood_evidence_create")
            .ok_or_else(|| vec![Diagnostic::error(
                "Runtime function blood_evidence_create not found".to_string(),
                Span::dummy(),
            )])?;
        let ev_push = self.module.get_function("blood_evidence_push")
            .ok_or_else(|| vec![Diagnostic::error(
                "Runtime function blood_evidence_push not found".to_string(),
                Span::dummy(),
            )])?;
        let ev_pop = self.module.get_function("blood_evidence_pop")
            .ok_or_else(|| vec![Diagnostic::error(
                "Runtime function blood_evidence_pop not found".to_string(),
                Span::dummy(),
            )])?;
        let ev_destroy = self.module.get_function("blood_evidence_destroy")
            .ok_or_else(|| vec![Diagnostic::error(
                "Runtime function blood_evidence_destroy not found".to_string(),
                Span::dummy(),
            )])?;

        // Create evidence vector
        let ev = self.builder.build_call(ev_create, &[], "evidence")
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| vec![Diagnostic::error(
                "blood_evidence_create returned void".to_string(),
                Span::dummy(),
            )])?;

        // Push handler ID onto evidence vector as i64
        let handler_ptr = self.context.i64_type().const_int(handler_id.index as u64, false);
        self.builder.build_call(ev_push, &[ev.into(), handler_ptr.into()], "")
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

        // Compile the body
        let result = self.compile_expr(body)?;

        // Pop handler from evidence vector
        self.builder.build_call(ev_pop, &[ev.into()], "")
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

        // Destroy evidence vector
        self.builder.build_call(ev_destroy, &[ev.into()], "")
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

        // Return result with proper type
        if result_ty.is_unit() {
            Ok(None)
        } else {
            Ok(result)
        }
    }
}
