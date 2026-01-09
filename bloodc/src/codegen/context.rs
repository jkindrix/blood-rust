//! Code generation context.
//!
//! This module provides the main code generation context which
//! coordinates LLVM code generation for a Blood program.

use std::collections::HashMap;

use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::builder::Builder;
use inkwell::values::{FunctionValue, BasicValueEnum, PointerValue};
use inkwell::types::{BasicTypeEnum, BasicType};
use inkwell::IntPredicate;
use inkwell::AddressSpace;

use crate::hir::{self, DefId, LocalId, Type, TypeKind, PrimitiveTy};
use crate::hir::def::{IntTy, UintTy};
use crate::diagnostics::Diagnostic;
use crate::span::Span;

/// The code generation context.
pub struct CodegenContext<'ctx, 'a> {
    /// The LLVM context.
    pub context: &'ctx Context,
    /// The LLVM module being built.
    pub module: &'a Module<'ctx>,
    /// The LLVM IR builder.
    pub builder: &'a Builder<'ctx>,
    /// Map from DefId to LLVM function.
    pub functions: HashMap<DefId, FunctionValue<'ctx>>,
    /// Map from LocalId to stack allocation (in current function).
    pub locals: HashMap<LocalId, PointerValue<'ctx>>,
    /// The current function being compiled.
    pub current_fn: Option<FunctionValue<'ctx>>,
    /// Errors encountered during codegen.
    pub errors: Vec<Diagnostic>,
    /// Struct definitions for type lowering.
    pub struct_defs: HashMap<DefId, Vec<Type>>,
}

impl<'ctx, 'a> CodegenContext<'ctx, 'a> {
    /// Create a new code generation context.
    pub fn new(
        context: &'ctx Context,
        module: &'a Module<'ctx>,
        builder: &'a Builder<'ctx>,
    ) -> Self {
        Self {
            context,
            module,
            builder,
            functions: HashMap::new(),
            locals: HashMap::new(),
            current_fn: None,
            errors: Vec::new(),
            struct_defs: HashMap::new(),
        }
    }

    /// Compile an entire HIR crate.
    pub fn compile_crate(&mut self, hir_crate: &hir::Crate) -> Result<(), Vec<Diagnostic>> {
        // First pass: collect struct definitions for type lowering
        for (def_id, item) in &hir_crate.items {
            if let hir::ItemKind::Struct(struct_def) = &item.kind {
                let field_types = match &struct_def.kind {
                    hir::StructKind::Record(fields) => {
                        fields.iter().map(|f| f.ty.clone()).collect()
                    }
                    hir::StructKind::Tuple(fields) => {
                        fields.iter().map(|f| f.ty.clone()).collect()
                    }
                    hir::StructKind::Unit => Vec::new(),
                };
                self.struct_defs.insert(*def_id, field_types);
            }
        }

        // Second pass: declare all functions
        for (def_id, item) in &hir_crate.items {
            if let hir::ItemKind::Fn(fn_def) = &item.kind {
                self.declare_function(*def_id, &item.name, fn_def)?;
            }
        }

        // Declare runtime functions
        self.declare_runtime_functions();

        // Second pass: compile function bodies
        for (def_id, item) in &hir_crate.items {
            if let hir::ItemKind::Fn(fn_def) = &item.kind {
                if let Some(body_id) = fn_def.body_id {
                    if let Some(body) = hir_crate.bodies.get(&body_id) {
                        self.compile_function_body(*def_id, body)?;
                    }
                }
            }
        }

        if self.errors.is_empty() {
            Ok(())
        } else {
            Err(std::mem::take(&mut self.errors))
        }
    }

    /// Declare a function (without body).
    fn declare_function(
        &mut self,
        def_id: DefId,
        name: &str,
        fn_def: &hir::FnDef,
    ) -> Result<(), Vec<Diagnostic>> {
        let fn_type = self.fn_type_from_sig(&fn_def.sig);
        // Rename "main" to "blood_main" for runtime linkage
        let llvm_name = if name == "main" { "blood_main" } else { name };
        let fn_value = self.module.add_function(llvm_name, fn_type, None);
        self.functions.insert(def_id, fn_value);
        Ok(())
    }

    /// Declare runtime support functions.
    fn declare_runtime_functions(&mut self) {
        // print_int(i32) -> void
        let i32_type = self.context.i32_type();
        let void_type = self.context.void_type();
        let print_int_type = void_type.fn_type(&[i32_type.into()], false);
        self.module.add_function("print_int", print_int_type, None);

        // print_str(*i8) -> void
        let i8_ptr_type = self.context.i8_type().ptr_type(AddressSpace::default());
        let print_str_type = void_type.fn_type(&[i8_ptr_type.into()], false);
        self.module.add_function("print_str", print_str_type, None);

        // println_int(i32) -> void
        self.module.add_function("println_int", print_int_type, None);

        // println_str(*i8) -> void
        self.module.add_function("println_str", print_str_type, None);
    }

    /// Compile a function body.
    fn compile_function_body(
        &mut self,
        def_id: DefId,
        body: &hir::Body,
    ) -> Result<(), Vec<Diagnostic>> {
        let fn_value = *self.functions.get(&def_id).ok_or_else(|| {
            vec![Diagnostic::error(
                "Internal error: function not declared",
                Span::dummy(),
            )]
        })?;

        self.current_fn = Some(fn_value);
        self.locals.clear();

        // Create entry block
        let entry = self.context.append_basic_block(fn_value, "entry");
        self.builder.position_at_end(entry);

        // Allocate space for parameters
        for (i, param) in body.params().enumerate() {
            let llvm_type = self.lower_type(&param.ty);
            let alloca = self.builder.build_alloca(llvm_type, &param.name.clone().unwrap_or_else(|| format!("arg{}", i)))
                .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

            // Store parameter value
            let param_value = fn_value.get_nth_param(i as u32)
                .ok_or_else(|| vec![Diagnostic::error("Parameter not found", Span::dummy())])?;
            self.builder.build_store(alloca, param_value)
                .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

            self.locals.insert(param.id, alloca);
        }

        // Compile body expression
        let result = self.compile_expr(&body.expr)?;

        // Build return
        if body.return_type().is_unit() {
            self.builder.build_return(None)
                .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
        } else if let Some(value) = result {
            self.builder.build_return(Some(&value))
                .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
        } else {
            self.builder.build_return(None)
                .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
        }

        self.current_fn = None;
        Ok(())
    }

    /// Lower an HIR type to an LLVM type.
    pub fn lower_type(&self, ty: &Type) -> BasicTypeEnum<'ctx> {
        match ty.kind() {
            TypeKind::Primitive(prim) => self.lower_primitive(prim),
            TypeKind::Tuple(types) if types.is_empty() => {
                // Unit type - use i8 as placeholder
                self.context.i8_type().into()
            }
            TypeKind::Tuple(types) => {
                let field_types: Vec<_> = types.iter()
                    .map(|t| self.lower_type(t))
                    .collect();
                self.context.struct_type(&field_types, false).into()
            }
            TypeKind::Array { element, size } => {
                let elem_type = self.lower_type(element);
                elem_type.array_type(*size as u32).into()
            }
            TypeKind::Ref { inner: _, .. } | TypeKind::Ptr { inner: _, .. } => {
                // All references/pointers become opaque pointers
                self.context.i8_type().ptr_type(AddressSpace::default()).into()
            }
            TypeKind::Never => {
                // Never type - can use any type, i8 works
                self.context.i8_type().into()
            }
            TypeKind::Adt { def_id, args: _ } => {
                // Look up the struct definition
                if let Some(field_types) = self.struct_defs.get(def_id) {
                    let llvm_fields: Vec<BasicTypeEnum> = field_types
                        .iter()
                        .map(|t| self.lower_type(t))
                        .collect();
                    self.context.struct_type(&llvm_fields, false).into()
                } else {
                    // Unknown ADT - default to i32
                    self.context.i32_type().into()
                }
            }
            TypeKind::Error | TypeKind::Infer(_) | TypeKind::Param(_) => {
                // Should not reach codegen with these
                self.context.i32_type().into()
            }
            TypeKind::Fn { .. } | TypeKind::Slice { .. } => {
                // Function and slice types - use pointer
                self.context.i8_type().ptr_type(AddressSpace::default()).into()
            }
        }
    }

    /// Lower a primitive type.
    fn lower_primitive(&self, prim: &PrimitiveTy) -> BasicTypeEnum<'ctx> {
        match prim {
            PrimitiveTy::Bool => self.context.bool_type().into(),
            PrimitiveTy::Char => self.context.i32_type().into(), // Unicode codepoint
            PrimitiveTy::Int(int_ty) => match int_ty {
                IntTy::I8 => self.context.i8_type().into(),
                IntTy::I16 => self.context.i16_type().into(),
                IntTy::I32 => self.context.i32_type().into(),
                IntTy::I64 => self.context.i64_type().into(),
                IntTy::I128 => self.context.i128_type().into(),
                IntTy::Isize => self.context.i64_type().into(), // Assume 64-bit
            },
            PrimitiveTy::Uint(uint_ty) => match uint_ty {
                UintTy::U8 => self.context.i8_type().into(),
                UintTy::U16 => self.context.i16_type().into(),
                UintTy::U32 => self.context.i32_type().into(),
                UintTy::U64 => self.context.i64_type().into(),
                UintTy::U128 => self.context.i128_type().into(),
                UintTy::Usize => self.context.i64_type().into(),
            },
            PrimitiveTy::Float(float_ty) => match float_ty {
                crate::hir::def::FloatTy::F32 => self.context.f32_type().into(),
                crate::hir::def::FloatTy::F64 => self.context.f64_type().into(),
            },
            PrimitiveTy::Str => {
                // String slice - pointer for now
                self.context.i8_type().ptr_type(AddressSpace::default()).into()
            }
        }
    }

    /// Create LLVM function type from HIR signature.
    fn fn_type_from_sig(&self, sig: &hir::FnSig) -> inkwell::types::FunctionType<'ctx> {
        let param_types: Vec<_> = sig.inputs.iter()
            .map(|t| self.lower_type(t).into())
            .collect();

        if sig.output.is_unit() {
            self.context.void_type().fn_type(&param_types, false)
        } else {
            let ret_type = self.lower_type(&sig.output);
            ret_type.fn_type(&param_types, false)
        }
    }

    /// Compile an expression.
    pub fn compile_expr(&mut self, expr: &hir::Expr) -> Result<Option<BasicValueEnum<'ctx>>, Vec<Diagnostic>> {
        use hir::ExprKind::*;

        match &expr.kind {
            Literal(lit) => self.compile_literal(lit).map(Some),
            Local(local_id) => self.compile_local_load(*local_id).map(Some),
            Binary { op, left, right } => self.compile_binary(op, left, right).map(Some),
            Unary { op, operand } => self.compile_unary(op, operand).map(Some),
            Call { callee, args } => self.compile_call(callee, args),
            Block { stmts, expr: tail_expr } => self.compile_block(stmts, tail_expr.as_deref()),
            If { condition, then_branch, else_branch } => {
                self.compile_if(condition, then_branch, else_branch.as_deref(), &expr.ty)
            }
            While { condition, body, .. } => {
                self.compile_while(condition, body)?;
                Ok(None)
            }
            Return(value) => {
                self.compile_return(value.as_deref())?;
                Ok(None)
            }
            Assign { target, value } => {
                self.compile_assign(target, value)?;
                Ok(None)
            }
            Tuple(exprs) => {
                // Empty tuple is unit type, return None
                if exprs.is_empty() {
                    return Ok(None);
                }
                // For non-empty tuples, compile all expressions and build a struct
                let values: Vec<_> = exprs.iter()
                    .filter_map(|e| self.compile_expr(e).ok().flatten())
                    .collect();
                if values.is_empty() {
                    Ok(None)
                } else if values.len() == 1 {
                    Ok(Some(values.into_iter().next().unwrap()))
                } else {
                    // Build a struct for the tuple
                    let types: Vec<BasicTypeEnum> = values.iter()
                        .map(|v| v.get_type())
                        .collect();
                    let struct_type = self.context.struct_type(&types, false);
                    let mut struct_val = struct_type.get_undef();
                    for (i, val) in values.into_iter().enumerate() {
                        struct_val = self.builder
                            .build_insert_value(struct_val, val, i as u32, "tuple")
                            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
                            .into_struct_value();
                    }
                    Ok(Some(struct_val.into()))
                }
            }
            Def(def_id) => {
                // Reference to a function - return the function pointer or look up value
                if let Some(fn_val) = self.functions.get(def_id) {
                    Ok(Some(fn_val.as_global_value().as_pointer_value().into()))
                } else {
                    // Might be a constant - for now return error
                    Ok(None)
                }
            }
            Struct { def_id: _, fields, base: _ } => {
                // Compile struct construction
                self.compile_struct_expr(&expr.ty, fields)
            }
            Field { base, field_idx } => {
                // Compile field access
                self.compile_field_access(base, *field_idx)
            }
            _ => {
                self.errors.push(Diagnostic::error(
                    format!("Unsupported expression kind: {:?}", std::mem::discriminant(&expr.kind)),
                    expr.span,
                ));
                Ok(None)
            }
        }
    }

    /// Compile a literal.
    fn compile_literal(&self, lit: &hir::LiteralValue) -> Result<BasicValueEnum<'ctx>, Vec<Diagnostic>> {
        match lit {
            hir::LiteralValue::Int(val) => {
                Ok(self.context.i32_type().const_int(*val as u64, true).into())
            }
            hir::LiteralValue::Uint(val) => {
                Ok(self.context.i32_type().const_int(*val as u64, false).into())
            }
            hir::LiteralValue::Float(val) => {
                Ok(self.context.f64_type().const_float(*val).into())
            }
            hir::LiteralValue::Bool(val) => {
                Ok(self.context.bool_type().const_int(*val as u64, false).into())
            }
            hir::LiteralValue::Char(val) => {
                Ok(self.context.i32_type().const_int(*val as u64, false).into())
            }
            hir::LiteralValue::String(s) => {
                // Create global string constant
                let global = self.builder.build_global_string_ptr(s, "str")
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
                Ok(global.as_pointer_value().into())
            }
        }
    }

    /// Load a local variable.
    fn compile_local_load(&self, local_id: LocalId) -> Result<BasicValueEnum<'ctx>, Vec<Diagnostic>> {
        let alloca = self.locals.get(&local_id)
            .ok_or_else(|| vec![Diagnostic::error(
                format!("Local variable {:?} not found", local_id),
                Span::dummy(),
            )])?;

        self.builder.build_load(*alloca, "load")
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])
    }

    /// Compile a binary operation.
    fn compile_binary(
        &mut self,
        op: &crate::ast::BinOp,
        left: &hir::Expr,
        right: &hir::Expr,
    ) -> Result<BasicValueEnum<'ctx>, Vec<Diagnostic>> {
        use crate::ast::BinOp::*;

        let lhs = self.compile_expr(left)?
            .ok_or_else(|| vec![Diagnostic::error("Expected value for binary op", left.span)])?;
        let rhs = self.compile_expr(right)?
            .ok_or_else(|| vec![Diagnostic::error("Expected value for binary op", right.span)])?;

        // Assume integer operations for now
        let lhs_int = lhs.into_int_value();
        let rhs_int = rhs.into_int_value();

        let result = match op {
            Add => self.builder.build_int_add(lhs_int, rhs_int, "add"),
            Sub => self.builder.build_int_sub(lhs_int, rhs_int, "sub"),
            Mul => self.builder.build_int_mul(lhs_int, rhs_int, "mul"),
            Div => self.builder.build_int_signed_div(lhs_int, rhs_int, "div"),
            Rem => self.builder.build_int_signed_rem(lhs_int, rhs_int, "rem"),
            Eq => self.builder.build_int_compare(IntPredicate::EQ, lhs_int, rhs_int, "eq"),
            Ne => self.builder.build_int_compare(IntPredicate::NE, lhs_int, rhs_int, "ne"),
            Lt => self.builder.build_int_compare(IntPredicate::SLT, lhs_int, rhs_int, "lt"),
            Le => self.builder.build_int_compare(IntPredicate::SLE, lhs_int, rhs_int, "le"),
            Gt => self.builder.build_int_compare(IntPredicate::SGT, lhs_int, rhs_int, "gt"),
            Ge => self.builder.build_int_compare(IntPredicate::SGE, lhs_int, rhs_int, "ge"),
            And => self.builder.build_and(lhs_int, rhs_int, "and"),
            Or => self.builder.build_or(lhs_int, rhs_int, "or"),
            BitAnd => self.builder.build_and(lhs_int, rhs_int, "bitand"),
            BitOr => self.builder.build_or(lhs_int, rhs_int, "bitor"),
            BitXor => self.builder.build_xor(lhs_int, rhs_int, "bitxor"),
            Shl => self.builder.build_left_shift(lhs_int, rhs_int, "shl"),
            Shr => self.builder.build_right_shift(lhs_int, rhs_int, true, "shr"),
            Pipe => {
                return Err(vec![Diagnostic::error(
                    "Pipe operator not supported in codegen",
                    Span::dummy(),
                )]);
            }
        };

        result
            .map(|v| v.into())
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])
    }

    /// Compile a unary operation.
    fn compile_unary(
        &mut self,
        op: &crate::ast::UnaryOp,
        operand: &hir::Expr,
    ) -> Result<BasicValueEnum<'ctx>, Vec<Diagnostic>> {
        use crate::ast::UnaryOp::*;

        let val = self.compile_expr(operand)?
            .ok_or_else(|| vec![Diagnostic::error("Expected value for unary op", operand.span)])?;

        match op {
            Neg => {
                let int_val = val.into_int_value();
                self.builder.build_int_neg(int_val, "neg")
                    .map(|v| v.into())
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])
            }
            Not => {
                let int_val = val.into_int_value();
                self.builder.build_not(int_val, "not")
                    .map(|v| v.into())
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])
            }
            _ => Err(vec![Diagnostic::error(
                format!("Unsupported unary operator: {:?}", op),
                Span::dummy(),
            )]),
        }
    }

    /// Compile a function call.
    fn compile_call(
        &mut self,
        callee: &hir::Expr,
        args: &[hir::Expr],
    ) -> Result<Option<BasicValueEnum<'ctx>>, Vec<Diagnostic>> {
        // Get function to call
        let fn_value = match &callee.kind {
            hir::ExprKind::Def(def_id) => {
                self.functions.get(def_id).copied()
                    .or_else(|| {
                        // Check for runtime functions by looking at def_id
                        None
                    })
            }
            _ => None,
        };

        let fn_value = fn_value.ok_or_else(|| vec![Diagnostic::error(
            "Cannot determine function to call",
            callee.span,
        )])?;

        // Compile arguments
        let mut compiled_args = Vec::new();
        for arg in args {
            if let Some(val) = self.compile_expr(arg)? {
                compiled_args.push(val.into());
            }
        }

        // Build call
        let call = self.builder
            .build_call(fn_value, &compiled_args, "call")
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

        Ok(call.try_as_basic_value().left())
    }

    /// Compile a block.
    fn compile_block(
        &mut self,
        stmts: &[hir::Stmt],
        tail_expr: Option<&hir::Expr>,
    ) -> Result<Option<BasicValueEnum<'ctx>>, Vec<Diagnostic>> {
        for stmt in stmts {
            match stmt {
                hir::Stmt::Let { local_id, init } => {
                    // Get the LLVM type from the init expression
                    let llvm_type = if let Some(init_expr) = init {
                        self.lower_type(&init_expr.ty)
                    } else {
                        // Default to i32 if no initializer
                        self.context.i32_type().into()
                    };

                    // Allocate local with correct type
                    let alloca = self.builder
                        .build_alloca(llvm_type, &format!("local_{}", local_id.index))
                        .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

                    if let Some(init_expr) = init {
                        if let Some(init_val) = self.compile_expr(init_expr)? {
                            self.builder.build_store(alloca, init_val)
                                .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
                        }
                    }

                    self.locals.insert(*local_id, alloca);
                }
                hir::Stmt::Expr(expr) => {
                    self.compile_expr(expr)?;
                }
                hir::Stmt::Item(_) => {
                    // Nested items handled separately
                }
            }
        }

        if let Some(tail) = tail_expr {
            self.compile_expr(tail)
        } else {
            Ok(None)
        }
    }

    /// Compile an if expression.
    fn compile_if(
        &mut self,
        condition: &hir::Expr,
        then_branch: &hir::Expr,
        else_branch: Option<&hir::Expr>,
        result_ty: &Type,
    ) -> Result<Option<BasicValueEnum<'ctx>>, Vec<Diagnostic>> {
        let fn_value = self.current_fn
            .ok_or_else(|| vec![Diagnostic::error("If outside function", Span::dummy())])?;

        let cond_val = self.compile_expr(condition)?
            .ok_or_else(|| vec![Diagnostic::error("Expected condition value", condition.span)])?;

        // Convert to i1 if needed
        let cond_bool = if cond_val.is_int_value() {
            let int_val = cond_val.into_int_value();
            if int_val.get_type().get_bit_width() == 1 {
                int_val
            } else {
                self.builder.build_int_compare(
                    IntPredicate::NE,
                    int_val,
                    int_val.get_type().const_zero(),
                    "tobool",
                ).map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
            }
        } else {
            return Err(vec![Diagnostic::error("Condition must be boolean", condition.span)]);
        };

        let then_bb = self.context.append_basic_block(fn_value, "then");
        let else_bb = self.context.append_basic_block(fn_value, "else");
        let merge_bb = self.context.append_basic_block(fn_value, "merge");

        self.builder.build_conditional_branch(cond_bool, then_bb, else_bb)
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

        // Compile then branch
        self.builder.position_at_end(then_bb);
        let then_val = self.compile_expr(then_branch)?;
        self.builder.build_unconditional_branch(merge_bb)
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
        let then_bb = self.builder.get_insert_block().unwrap();

        // Compile else branch
        self.builder.position_at_end(else_bb);
        let else_val = if let Some(else_expr) = else_branch {
            self.compile_expr(else_expr)?
        } else {
            None
        };
        self.builder.build_unconditional_branch(merge_bb)
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
        let else_bb = self.builder.get_insert_block().unwrap();

        // Merge
        self.builder.position_at_end(merge_bb);

        // If non-unit result type, create phi node
        if !result_ty.is_unit() {
            if let (Some(then_v), Some(else_v)) = (then_val, else_val) {
                let phi = self.builder.build_phi(self.lower_type(result_ty), "ifresult")
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
                phi.add_incoming(&[(&then_v, then_bb), (&else_v, else_bb)]);
                return Ok(Some(phi.as_basic_value()));
            }
        }

        Ok(None)
    }

    /// Compile a while loop.
    fn compile_while(
        &mut self,
        condition: &hir::Expr,
        body: &hir::Expr,
    ) -> Result<(), Vec<Diagnostic>> {
        let fn_value = self.current_fn
            .ok_or_else(|| vec![Diagnostic::error("While outside function", Span::dummy())])?;

        let cond_bb = self.context.append_basic_block(fn_value, "while.cond");
        let body_bb = self.context.append_basic_block(fn_value, "while.body");
        let end_bb = self.context.append_basic_block(fn_value, "while.end");

        // Jump to condition
        self.builder.build_unconditional_branch(cond_bb)
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

        // Compile condition
        self.builder.position_at_end(cond_bb);
        let cond_val = self.compile_expr(condition)?
            .ok_or_else(|| vec![Diagnostic::error("Expected condition value", condition.span)])?
            .into_int_value();

        // Ensure boolean
        let cond_bool = if cond_val.get_type().get_bit_width() == 1 {
            cond_val
        } else {
            self.builder.build_int_compare(
                IntPredicate::NE,
                cond_val,
                cond_val.get_type().const_zero(),
                "tobool",
            ).map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
        };

        self.builder.build_conditional_branch(cond_bool, body_bb, end_bb)
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

        // Compile body
        self.builder.position_at_end(body_bb);
        self.compile_expr(body)?;
        self.builder.build_unconditional_branch(cond_bb)
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

        // Continue after loop
        self.builder.position_at_end(end_bb);

        Ok(())
    }

    /// Compile a return statement.
    fn compile_return(&mut self, value: Option<&hir::Expr>) -> Result<(), Vec<Diagnostic>> {
        if let Some(val_expr) = value {
            if let Some(val) = self.compile_expr(val_expr)? {
                self.builder.build_return(Some(&val))
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
            } else {
                self.builder.build_return(None)
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
            }
        } else {
            self.builder.build_return(None)
                .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
        }
        Ok(())
    }

    /// Compile an assignment.
    fn compile_assign(&mut self, target: &hir::Expr, value: &hir::Expr) -> Result<(), Vec<Diagnostic>> {
        let val = self.compile_expr(value)?
            .ok_or_else(|| vec![Diagnostic::error("Expected value for assignment", value.span)])?;

        // Get target address
        match &target.kind {
            hir::ExprKind::Local(local_id) => {
                let alloca = self.locals.get(local_id)
                    .ok_or_else(|| vec![Diagnostic::error("Local not found", target.span)])?;
                self.builder.build_store(*alloca, val)
                    .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;
            }
            _ => {
                return Err(vec![Diagnostic::error(
                    "Cannot assign to this expression",
                    target.span,
                )]);
            }
        }

        Ok(())
    }

    /// Compile a struct construction expression.
    fn compile_struct_expr(
        &mut self,
        result_ty: &Type,
        fields: &[hir::FieldExpr],
    ) -> Result<Option<BasicValueEnum<'ctx>>, Vec<Diagnostic>> {
        // Get the LLVM type for the struct
        let struct_llvm_type = self.lower_type(result_ty);

        // Create an undefined struct value
        let struct_type = struct_llvm_type.into_struct_type();
        let mut struct_val = struct_type.get_undef();

        // Fill in each field
        for field in fields {
            let field_val = self.compile_expr(&field.value)?
                .ok_or_else(|| vec![Diagnostic::error(
                    "Expected value for struct field",
                    field.value.span,
                )])?;

            struct_val = self.builder
                .build_insert_value(struct_val, field_val, field.field_idx, "field")
                .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?
                .into_struct_value();
        }

        Ok(Some(struct_val.into()))
    }

    /// Compile a field access expression.
    fn compile_field_access(
        &mut self,
        base: &hir::Expr,
        field_idx: u32,
    ) -> Result<Option<BasicValueEnum<'ctx>>, Vec<Diagnostic>> {
        let base_val = self.compile_expr(base)?
            .ok_or_else(|| vec![Diagnostic::error("Expected struct value", base.span)])?;

        // Extract the field from the struct
        let struct_val = base_val.into_struct_value();
        let field_val = self.builder
            .build_extract_value(struct_val, field_idx, "field")
            .map_err(|e| vec![Diagnostic::error(format!("LLVM error: {}", e), Span::dummy())])?;

        Ok(Some(field_val))
    }
}
