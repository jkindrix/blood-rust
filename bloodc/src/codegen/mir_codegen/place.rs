//! MIR place code generation.
//!
//! This module handles compilation of MIR places (memory locations) to LLVM IR.
//! Places represent lvalues - locations that can be read from or written to.

use inkwell::values::{BasicValueEnum, PointerValue};
use inkwell::types::BasicType;

use crate::diagnostics::Diagnostic;
use crate::hir::{Type, TypeKind};
use crate::mir::body::MirBody;
use crate::mir::types::{Place, PlaceElem};
use crate::mir::{EscapeResults, EscapeState};

use super::CodegenContext;

/// Extension trait for MIR place compilation.
pub trait MirPlaceCodegen<'ctx, 'a> {
    /// Get a pointer to a MIR place.
    fn compile_mir_place(
        &mut self,
        place: &Place,
        body: &MirBody,
        escape_results: Option<&EscapeResults>,
    ) -> Result<PointerValue<'ctx>, Vec<Diagnostic>>;

    /// Load a value from a MIR place (with optional generation check).
    fn compile_mir_place_load(
        &mut self,
        place: &Place,
        body: &MirBody,
        escape_results: Option<&EscapeResults>,
    ) -> Result<BasicValueEnum<'ctx>, Vec<Diagnostic>>;

    /// Compute the effective type of a place after applying projections.
    fn compute_place_type(&self, base_ty: &Type, projections: &[PlaceElem]) -> Type;
}

impl<'ctx, 'a> MirPlaceCodegen<'ctx, 'a> for CodegenContext<'ctx, 'a> {
    fn compile_mir_place(
        &mut self,
        place: &Place,
        body: &MirBody,
        escape_results: Option<&EscapeResults>,
    ) -> Result<PointerValue<'ctx>, Vec<Diagnostic>> {
        let base_ptr = *self.locals.get(&place.local).ok_or_else(|| {
            vec![Diagnostic::error(
                format!("Local _{} not found", place.local.index),
                body.span,
            )]
        })?;

        // Track the current type as we process projections
        let local_info = body.locals.get(place.local.index as usize)
            .expect("ICE: MIR local not found in body during codegen");
        let base_ty = local_info.ty.clone();
        let mut current_ty = base_ty.clone();

        let mut current_ptr = base_ptr;
        // Track if we're inside an enum variant: (enum_def_id, variant_index)
        // This is needed to handle heterogeneous variant payloads correctly
        let mut variant_ctx: Option<(crate::hir::DefId, u32)> = None;

        // Check if this is a closure __env local with Field projections.
        // If so, we need to cast the i8* to the captures struct type first.
        let is_closure_env = local_info.name.as_deref() == Some("__env");
        let has_field_projections = place.projection.iter().any(|p| matches!(p, PlaceElem::Field(_)));

        if is_closure_env && has_field_projections {
            // Load the i8* from the alloca
            let env_i8_ptr = self.builder.build_load(current_ptr, "env_ptr")
                .map_err(|e| vec![Diagnostic::error(
                    format!("LLVM load error: {}", e), body.span
                )])?.into_pointer_value();

            // Get the captures struct type from the MIR type (which is a Tuple)
            let captures_llvm_ty = self.lower_type(&base_ty);
            let captures_ptr_ty = captures_llvm_ty.ptr_type(inkwell::AddressSpace::default());

            // Cast i8* to captures struct pointer
            current_ptr = self.builder.build_pointer_cast(env_i8_ptr, captures_ptr_ty, "env_captures_ptr")
                .map_err(|e| vec![Diagnostic::error(
                    format!("LLVM pointer cast error: {}", e), body.span
                )])?;
        }

        for elem in &place.projection {
            current_ptr = match elem {
                PlaceElem::Deref => {
                    // Save original type to check if this is a fat pointer (slice reference)
                    let original_ty = current_ty.clone();
                    let is_fat_ptr = match original_ty.kind() {
                        TypeKind::Ref { inner, .. } | TypeKind::Ptr { inner, .. } => {
                            matches!(inner.kind(), TypeKind::Slice { .. })
                        }
                        TypeKind::Slice { .. } => true,
                        _ => false,
                    };

                    // Update current_ty to the inner type (dereference the reference/pointer)
                    current_ty = match original_ty.kind() {
                        TypeKind::Ref { inner, .. } => inner.clone(),
                        TypeKind::Ptr { inner, .. } => inner.clone(),
                        _ => current_ty.clone(), // Keep as-is if not a reference type
                    };

                    // Load the pointer value
                    let loaded = self.builder.build_load(current_ptr, "deref")
                        .map_err(|e| vec![Diagnostic::error(
                            format!("LLVM load error: {}", e), body.span
                        )])?;

                    // Handle different loaded value types:
                    // - PointerValue: thin reference (normal case)
                    // - StructValue: fat reference (like &[T] or &str - contains ptr + metadata)
                    //                Only extract field 0 if this is actually a fat pointer type
                    // - IntValue: opaque pointer representation or enum variant data
                    use inkwell::values::BasicValueEnum;
                    let ptr_val = match loaded {
                        BasicValueEnum::PointerValue(ptr) => ptr,
                        BasicValueEnum::StructValue(sv) => {
                            if is_fat_ptr {
                                // Fat pointer (slice/str) - extract the data pointer from field 0
                                self.builder.build_extract_value(sv, 0, "fat_ptr_data")
                                    .map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM extract_value error: {}", e), body.span
                                    )])?
                                    .into_pointer_value()
                            } else {
                                // This is a struct value but NOT a fat pointer.
                                // This can happen when we have a Copy type stored by value.
                                // We need to store it to a temporary and return pointer to that.
                                let struct_ty = sv.get_type();
                                let tmp_alloca = self.builder.build_alloca(struct_ty, "deref_tmp")
                                    .map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM alloca error: {}", e), body.span
                                    )])?;
                                self.builder.build_store(tmp_alloca, sv)
                                    .map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM store error: {}", e), body.span
                                    )])?;
                                tmp_alloca
                            }
                        }
                        BasicValueEnum::IntValue(int_val) => {
                            // Opaque pointer as integer - convert to pointer type
                            let inner_ty = self.lower_type(&current_ty);
                            let ptr_ty = inner_ty.ptr_type(inkwell::AddressSpace::default());
                            self.builder.build_int_to_ptr(int_val, ptr_ty, "deref_int_to_ptr")
                                .map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM int_to_ptr error: {}", e), body.span
                                )])?
                        }
                        other => {
                            return Err(vec![Diagnostic::error(
                                format!("Expected pointer, struct (fat ptr), or integer for Deref, got {:?}", other),
                                body.span,
                            )]);
                        }
                    };

                    // Check if we should skip generation checks for this local.
                    // NoEscape locals are stack-allocated and safe by lexical scoping.
                    let should_skip_gen_check = escape_results
                        .map(|er| er.get(place.local) == EscapeState::NoEscape)
                        .unwrap_or(false);

                    // If this is a region-allocated pointer and the local escapes,
                    // validate generation before use
                    if !should_skip_gen_check {
                    if let Some(&gen_alloca) = self.local_generations.get(&place.local) {
                        let i32_ty = self.context.i32_type();
                        let i64_ty = self.context.i64_type();

                        // Load the expected generation
                        let expected_gen = self.builder.build_load(gen_alloca, "expected_gen")
                            .map_err(|e| vec![Diagnostic::error(
                                format!("LLVM load error: {}", e), body.span
                            )])?.into_int_value();

                        // Convert pointer to address for validation
                        let address = self.builder.build_ptr_to_int(ptr_val, i64_ty, "ptr_addr")
                            .map_err(|e| vec![Diagnostic::error(
                                format!("LLVM ptr_to_int error: {}", e), body.span
                            )])?;

                        // Call blood_validate_generation(address, expected_gen)
                        let validate_fn = self.module.get_function("blood_validate_generation")
                            .ok_or_else(|| vec![Diagnostic::error(
                                "blood_validate_generation not declared", body.span
                            )])?;

                        let result = self.builder.build_call(
                            validate_fn,
                            &[address.into(), expected_gen.into()],
                            "gen_check"
                        ).map_err(|e| vec![Diagnostic::error(
                            format!("LLVM call error: {}", e), body.span
                        )])?.try_as_basic_value()
                            .left()
                            .ok_or_else(|| vec![Diagnostic::error(
                                "blood_validate_generation returned void", body.span
                            )])?.into_int_value();

                        // Check if stale (result != 0)
                        let is_stale = self.builder.build_int_compare(
                            inkwell::IntPredicate::NE,
                            result,
                            i32_ty.const_int(0, false),
                            "is_stale"
                        ).map_err(|e| vec![Diagnostic::error(
                            format!("LLVM compare error: {}", e), body.span
                        )])?;

                        // Create blocks for valid and stale paths
                        let fn_value = self.current_fn.ok_or_else(|| {
                            vec![Diagnostic::error("No current function", body.span)]
                        })?;
                        let valid_bb = self.context.append_basic_block(fn_value, "gen_valid");
                        let stale_bb = self.context.append_basic_block(fn_value, "gen_stale");

                        self.builder.build_conditional_branch(is_stale, stale_bb, valid_bb)
                            .map_err(|e| vec![Diagnostic::error(
                                format!("LLVM branch error: {}", e), body.span
                            )])?;

                        // Stale path: abort
                        self.builder.position_at_end(stale_bb);
                        let panic_fn = self.module.get_function("blood_stale_reference_panic")
                            .ok_or_else(|| vec![Diagnostic::error(
                                "blood_stale_reference_panic not declared", body.span
                            )])?;
                        self.builder.build_call(
                            panic_fn,
                            &[expected_gen.into(), result.into()],
                            ""
                        ).map_err(|e| vec![Diagnostic::error(
                            format!("LLVM call error: {}", e), body.span
                        )])?;
                        self.builder.build_unreachable()
                            .map_err(|e| vec![Diagnostic::error(
                                format!("LLVM unreachable error: {}", e), body.span
                            )])?;

                        // Continue on valid path
                        self.builder.position_at_end(valid_bb);
                    }
                    }

                    ptr_val
                }

                PlaceElem::Field(idx) => {
                    // Check if we're accessing an enum variant field
                    if let Some((enum_def_id, variant_idx)) = variant_ctx {
                        // We're inside an enum variant - need special handling for heterogeneous payloads
                        // The enum layout is { i32 tag, largest_variant_payload... }
                        // But the actual variant's payload might be smaller/different type

                        // Get the enum's variant field types
                        if let Some(variants) = self.enum_defs.get(&enum_def_id) {
                            if let Some(variant_fields) = variants.get(variant_idx as usize) {
                                if let Some(variant_field_ty) = variant_fields.get(*idx as usize) {
                                    // Substitute type params if this is a generic enum
                                    let args = match current_ty.kind() {
                                        TypeKind::Adt { args, .. } => args.clone(),
                                        _ => Vec::new(),
                                    };
                                    let actual_field_ty = self.substitute_type_params(variant_field_ty, &args);

                                    // Get pointer to payload area (field 1 of enum struct)
                                    let payload_ptr = self.builder.build_struct_gep(current_ptr, 1, "payload_ptr")
                                        .map_err(|e| vec![Diagnostic::error(
                                            format!("LLVM GEP error: {}", e), body.span
                                        )])?;

                                    // Build the variant's actual payload struct type
                                    let variant_field_types: Vec<inkwell::types::BasicTypeEnum> = variant_fields.iter()
                                        .map(|f| {
                                            let substituted = self.substitute_type_params(f, &args);
                                            self.lower_type(&substituted)
                                        })
                                        .collect();
                                    let variant_struct_ty = self.context.struct_type(&variant_field_types, false);

                                    // Cast payload pointer to variant struct pointer
                                    let variant_ptr = self.builder.build_pointer_cast(
                                        payload_ptr,
                                        variant_struct_ty.ptr_type(inkwell::AddressSpace::default()),
                                        "variant_ptr"
                                    ).map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM pointer cast error: {}", e), body.span
                                    )])?;

                                    // GEP to the specific field within the variant
                                    let field_ptr = self.builder.build_struct_gep(variant_ptr, *idx, &format!("variant_field_{}", idx))
                                        .map_err(|e| vec![Diagnostic::error(
                                            format!("LLVM GEP error: {}", e), body.span
                                        )])?;

                                    // Clear variant context since we've accessed the field
                                    variant_ctx = None;
                                    current_ty = actual_field_ty;
                                    current_ptr = field_ptr;
                                    continue;
                                }
                            }
                        }
                        // Fall through to regular field access if lookup failed
                    }

                    // Regular field access (not inside variant, or variant lookup failed)
                    let actual_idx = if variant_ctx.is_some() {
                        *idx + 1  // Offset by 1 to skip the discriminant tag
                    } else {
                        *idx
                    };

                    // Check if this is a reference to a struct (MIR may not emit explicit Deref)
                    let is_ref_to_struct = matches!(
                        current_ty.kind(),
                        TypeKind::Ref { inner, .. } | TypeKind::Ptr { inner, .. }
                            if matches!(inner.kind(), TypeKind::Adt { .. } | TypeKind::Tuple(_))
                    );

                    // Update current_ty to the field type (handle both direct and through-reference)
                    let effective_ty = match current_ty.kind() {
                        TypeKind::Ref { inner, .. } | TypeKind::Ptr { inner, .. } => inner.clone(),
                        _ => current_ty.clone(),
                    };
                    current_ty = match effective_ty.kind() {
                        TypeKind::Tuple(fields) => {
                            fields.get(*idx as usize).cloned().unwrap_or(current_ty.clone())
                        }
                        TypeKind::Adt { def_id, args } => {
                            // Look up field type for ADT types
                            if Some(*def_id) == self.vec_def_id {
                                // Vec<T> layout: { ptr: *T, len: i64, capacity: i64 }
                                match idx {
                                    0 => {
                                        let elem_ty = args.first().cloned().unwrap_or(Type::unit());
                                        Type::new(TypeKind::Ptr { inner: elem_ty, mutable: true })
                                    }
                                    1 | 2 => Type::usize(),
                                    _ => current_ty.clone(),
                                }
                            } else if Some(*def_id) == self.option_def_id {
                                // Option<T> layout: { tag: i32, payload: T }
                                match idx {
                                    0 => Type::i32(),
                                    1 => args.first().cloned().unwrap_or(Type::unit()),
                                    _ => current_ty.clone(),
                                }
                            } else if Some(*def_id) == self.result_def_id {
                                // Result<T, E> layout: { tag: i32, payload: T or E }
                                match idx {
                                    0 => Type::i32(),
                                    1 => args.first().cloned().unwrap_or(Type::unit()),
                                    2 => args.get(1).cloned().unwrap_or(Type::unit()),
                                    _ => current_ty.clone(),
                                }
                            } else if let Some(field_types) = self.struct_defs.get(def_id) {
                                // Regular struct - look up field type
                                if let Some(field_ty) = field_types.get(*idx as usize) {
                                    self.substitute_type_params(field_ty, args)
                                } else {
                                    current_ty.clone()
                                }
                            } else {
                                // Unknown ADT or enum, keep type
                                current_ty.clone()
                            }
                        }
                        _ => current_ty.clone(),
                    };

                    // Get struct element pointer
                    if is_ref_to_struct {
                        // Reference to struct: load pointer then struct_gep
                        let loaded_val = self.builder.build_load(current_ptr, "struct_ptr")
                            .map_err(|e| vec![Diagnostic::error(
                                format!("LLVM load error: {}", e), body.span
                            )])?;

                        // Handle different loaded value types:
                        // - PointerValue: thin reference, use directly for struct_gep
                        // - StructValue: fat reference (like &[T]), GEP into the struct for the data pointer
                        // - IntValue: opaque pointer representation, convert to pointer
                        use inkwell::values::BasicValueEnum;
                        let struct_ptr = match loaded_val {
                            BasicValueEnum::PointerValue(ptr) => ptr,
                            BasicValueEnum::IntValue(int_val) => {
                                // Opaque pointer as integer - convert to pointer type
                                let struct_llvm_ty = self.lower_type(&effective_ty);
                                let ptr_ty = struct_llvm_ty.ptr_type(inkwell::AddressSpace::default());
                                self.builder.build_int_to_ptr(int_val, ptr_ty, "struct_ptr_cast")
                                    .map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM int_to_ptr error: {}", e), body.span
                                    )])?
                            }
                            BasicValueEnum::StructValue(_) => {
                                // Fat pointer or value type reference - the referenced data is
                                // already at current_ptr (it's the value, not a separate pointer).
                                // Use current_ptr directly for GEP since it points to the struct.
                                current_ptr
                            }
                            other => {
                                return Err(vec![Diagnostic::error(
                                    format!("Expected pointer, integer, or struct for reference, got {:?}", other),
                                    body.span,
                                )]);
                            }
                        };
                        self.builder.build_struct_gep(
                            struct_ptr,
                            actual_idx,
                            &format!("field_{}", idx)
                        ).map_err(|e| vec![Diagnostic::error(
                            format!("LLVM GEP error: {} (place={:?}, ty={:?})", e, place, effective_ty), body.span
                        )])?
                    } else {
                        self.builder.build_struct_gep(
                            current_ptr,
                            actual_idx,
                            &format!("field_{}", idx)
                        ).map_err(|e| vec![Diagnostic::error(
                            format!("LLVM GEP error: {} (place={:?}, ty={:?})", e, place, current_ty), body.span
                        )])?
                    }
                }

                PlaceElem::Index(idx_local) => {
                    let idx_ptr = self.locals.get(idx_local).ok_or_else(|| {
                        vec![Diagnostic::error(
                            format!("Index local _{} not found", idx_local.index),
                            body.span,
                        )]
                    })?;
                    let idx_val = self.builder.build_load(*idx_ptr, "idx")
                        .map_err(|e| vec![Diagnostic::error(
                            format!("LLVM load error: {}", e), body.span
                        )])?;

                    // Classify the indexable type:
                    // - Direct array [T; N]: ptr is [N x T]*, two-index GEP
                    // - Direct slice [T]: ptr is {T*, i64}* (fat pointer), extract data ptr, single-index GEP
                    // - Ref to array &[T; N]: ptr is [N x T]**, load to get [N x T]*, two-index GEP
                    // - Slice ref &[T]: ptr is {T*, i64}* (fat pointer), load struct, extract data ptr, single-index GEP
                    // - Ptr to elements *T: current_ptr is **T (e.g., Vec.data), load then single-index GEP
                    // - Vec<T>: current_ptr is Vec*, extract data ptr (field 0), load, then single-index GEP
                    enum IndexKind {
                        DirectArray,
                        DirectSlice,
                        RefToArray,
                        SliceRef,
                        PtrToElements,  // For Vec data pointer or similar
                        VecIndex,       // Direct indexing into Vec<T>
                        Other,
                    }

                    let index_kind = match current_ty.kind() {
                        TypeKind::Array { .. } => IndexKind::DirectArray,
                        TypeKind::Slice { .. } => IndexKind::DirectSlice,
                        TypeKind::Ref { inner, .. } | TypeKind::Ptr { inner, .. } => {
                            match inner.kind() {
                                TypeKind::Array { .. } => IndexKind::RefToArray,
                                TypeKind::Slice { .. } => IndexKind::SliceRef,
                                // Pointer to non-array/slice elements (e.g., Vec<T>.data is *T)
                                // After Field(0) on Vec, we have Ptr { inner: T }
                                // current_ptr is **T, need to load to get *T then GEP
                                _ => IndexKind::PtrToElements,
                            }
                        }
                        // Vec<T> indexing: need to extract data pointer and index into it
                        TypeKind::Adt { def_id, .. } if Some(*def_id) == self.vec_def_id => {
                            IndexKind::VecIndex
                        }
                        _ => IndexKind::Other,
                    };

                    // Update current_ty to element type
                    current_ty = match current_ty.kind() {
                        TypeKind::Array { element, .. } => element.clone(),
                        TypeKind::Slice { element } => element.clone(),
                        TypeKind::Ref { inner, .. } | TypeKind::Ptr { inner, .. } => {
                            match inner.kind() {
                                TypeKind::Array { element, .. } => element.clone(),
                                TypeKind::Slice { element } => element.clone(),
                                // For Ptr { inner: T } where T is not array/slice,
                                // indexing into *T gives T (the element type)
                                _ => inner.clone(),
                            }
                        }
                        // Vec<T> indexing gives element type T
                        TypeKind::Adt { def_id, args } if Some(*def_id) == self.vec_def_id => {
                            args.first().cloned().unwrap_or(current_ty.clone())
                        }
                        _ => current_ty.clone(),
                    };

                    unsafe {
                        match index_kind {
                            IndexKind::DirectArray => {
                                // Direct array: current_ptr is [N x T]*, use two-index GEP
                                let zero = self.context.i64_type().const_zero();
                                self.builder.build_in_bounds_gep(
                                    current_ptr,
                                    &[zero, idx_val.into_int_value()],
                                    "idx_gep"
                                ).map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                            }
                            IndexKind::DirectSlice => {
                                // Direct slice (fat pointer): current_ptr is {T*, i64}*
                                // Extract the data pointer (field 0), then single-index GEP
                                let data_ptr_ptr = self.builder.build_struct_gep(
                                    current_ptr,
                                    0,
                                    "slice_data_ptr_ptr"
                                ).map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?;
                                let data_ptr = self.builder.build_load(data_ptr_ptr, "slice_data_ptr")
                                    .map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM load error: {}", e), body.span
                                    )])?.into_pointer_value();
                                self.builder.build_in_bounds_gep(
                                    data_ptr,
                                    &[idx_val.into_int_value()],
                                    "idx_gep"
                                ).map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                            }
                            IndexKind::RefToArray => {
                                // Reference to array: current_ptr is [N x T]**, load to get [N x T]*
                                let array_ptr = self.builder.build_load(current_ptr, "array_ptr")
                                    .map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM load error: {}", e), body.span
                                    )])?.into_pointer_value();
                                let zero = self.context.i64_type().const_zero();
                                self.builder.build_in_bounds_gep(
                                    array_ptr,
                                    &[zero, idx_val.into_int_value()],
                                    "idx_gep"
                                ).map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                            }
                            IndexKind::SliceRef => {
                                // Slice reference (fat pointer): current_ptr is {T*, i64}*
                                // Load the fat pointer struct, extract data pointer (field 0), single-index GEP
                                let data_ptr_ptr = self.builder.build_struct_gep(
                                    current_ptr,
                                    0,
                                    "slice_data_ptr_ptr"
                                ).map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?;
                                let data_ptr = self.builder.build_load(data_ptr_ptr, "slice_data_ptr")
                                    .map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM load error: {}", e), body.span
                                    )])?.into_pointer_value();
                                self.builder.build_in_bounds_gep(
                                    data_ptr,
                                    &[idx_val.into_int_value()],
                                    "idx_gep"
                                ).map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                            }
                            IndexKind::PtrToElements => {
                                // Pointer to elements (e.g., Vec<T>.data which is *T)
                                // current_ptr is **T (pointer to the pointer field)
                                // Need to load the pointer value, then single-index GEP
                                let data_ptr = self.builder.build_load(current_ptr, "data_ptr")
                                    .map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM load error: {}", e), body.span
                                    )])?.into_pointer_value();
                                self.builder.build_in_bounds_gep(
                                    data_ptr,
                                    &[idx_val.into_int_value()],
                                    "ptr_idx_gep"
                                ).map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                            }
                            IndexKind::VecIndex => {
                                // Vec<T> direct indexing: current_ptr is Vec*, need to:
                                // 1. GEP to field 0 (data pointer field)
                                // 2. Load the data pointer (*T)
                                // 3. Index into the data with single-index GEP
                                // 4. Cast result to proper element type pointer for subsequent projections
                                let data_ptr_ptr = self.builder.build_struct_gep(current_ptr, 0, "vec_data_ptr_ptr")
                                    .map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM GEP error for Vec data pointer: {}", e), body.span
                                    )])?;
                                let data_ptr = self.builder.build_load(data_ptr_ptr, "vec_data_ptr")
                                    .map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM load error: {}", e), body.span
                                    )])?.into_pointer_value();
                                let elem_ptr = self.builder.build_in_bounds_gep(
                                    data_ptr,
                                    &[idx_val.into_int_value()],
                                    "vec_idx_gep"
                                ).map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?;

                                // Cast to proper element type pointer for subsequent Field projections
                                // current_ty has already been updated to the element type
                                let elem_llvm_ty = self.lower_type(&current_ty);
                                let elem_ptr_ty = elem_llvm_ty.ptr_type(inkwell::AddressSpace::default());
                                self.builder.build_pointer_cast(elem_ptr, elem_ptr_ty, "vec_elem_ptr")
                                    .map_err(|e| vec![Diagnostic::error(
                                        format!("LLVM pointer cast error: {}", e), body.span
                                    )])?
                            }
                            IndexKind::Other => {
                                // Other pointer type: single-index GEP
                                self.builder.build_in_bounds_gep(
                                    current_ptr,
                                    &[idx_val.into_int_value()],
                                    "idx_gep"
                                ).map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                            }
                        }
                    }
                }

                PlaceElem::ConstantIndex { offset, min_length: _, from_end } => {
                    // Check if this is a direct array or a reference to an array
                    let (is_direct_array, is_ref_to_array) = match current_ty.kind() {
                        TypeKind::Array { .. } | TypeKind::Slice { .. } => (true, false),
                        TypeKind::Ref { inner, .. } | TypeKind::Ptr { inner, .. } => {
                            (false, matches!(inner.kind(), TypeKind::Array { .. } | TypeKind::Slice { .. }))
                        }
                        _ => (false, false),
                    };

                    // Get the effective array type for from_end calculations
                    let effective_array_ty = match current_ty.kind() {
                        TypeKind::Array { .. } => current_ty.clone(),
                        TypeKind::Ref { inner, .. } | TypeKind::Ptr { inner, .. } => inner.clone(),
                        _ => current_ty.clone(),
                    };

                    let idx = if *from_end {
                        // For from_end, compute actual index as array_length - offset - 1
                        let array_len = match effective_array_ty.kind() {
                            TypeKind::Array { size, .. } => size.as_u64().ok_or_else(|| vec![Diagnostic::error(
                                "Array size must be concrete for indexing from end",
                                body.span,
                            )])?,
                            _ => {
                                return Err(vec![Diagnostic::error(
                                    format!("ConstantIndex from_end requires array type, got {:?}", current_ty),
                                    body.span,
                                )]);
                            }
                        };
                        // offset is the distance from the end, so index = array_len - 1 - offset
                        let actual_idx = array_len - 1 - *offset;
                        self.context.i64_type().const_int(actual_idx, false)
                    } else {
                        self.context.i64_type().const_int(*offset, false)
                    };

                    // Update current_ty to element type (handle both direct and through-reference)
                    current_ty = match current_ty.kind() {
                        TypeKind::Array { element, .. } => element.clone(),
                        TypeKind::Slice { element } => element.clone(),
                        TypeKind::Ref { inner, .. } | TypeKind::Ptr { inner, .. } => {
                            match inner.kind() {
                                TypeKind::Array { element, .. } => element.clone(),
                                TypeKind::Slice { element } => element.clone(),
                                _ => current_ty.clone(),
                            }
                        }
                        _ => current_ty.clone(),
                    };

                    unsafe {
                        if is_direct_array {
                            // Direct array: current_ptr is [N x T]*, use two-index GEP
                            let zero = self.context.i64_type().const_zero();
                            self.builder.build_in_bounds_gep(current_ptr, &[zero, idx], "const_idx")
                                .map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                        } else if is_ref_to_array {
                            // Reference to array: load pointer then two-index GEP
                            let array_ptr = self.builder.build_load(current_ptr, "array_ptr")
                                .map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM load error: {}", e), body.span
                                )])?.into_pointer_value();
                            let zero = self.context.i64_type().const_zero();
                            self.builder.build_in_bounds_gep(array_ptr, &[zero, idx], "const_idx")
                                .map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                        } else {
                            // Other type: single-index GEP
                            self.builder.build_in_bounds_gep(current_ptr, &[idx], "const_idx")
                                .map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                        }
                    }
                }

                PlaceElem::Subslice { from, to, from_end: _ } => {
                    // Check if this is a direct array or a reference to an array
                    let (is_direct_array, is_ref_to_array) = match current_ty.kind() {
                        TypeKind::Array { .. } | TypeKind::Slice { .. } => (true, false),
                        TypeKind::Ref { inner, .. } | TypeKind::Ptr { inner, .. } => {
                            (false, matches!(inner.kind(), TypeKind::Array { .. } | TypeKind::Slice { .. }))
                        }
                        _ => (false, false),
                    };

                    let idx = self.context.i64_type().const_int(*from, false);
                    let _ = to; // End index for slice length calculation

                    // For subslice, the type remains array/slice (just a different view)
                    // but the GEP behavior depends on whether we have an array pointer

                    unsafe {
                        if is_direct_array {
                            let zero = self.context.i64_type().const_zero();
                            self.builder.build_in_bounds_gep(current_ptr, &[zero, idx], "subslice")
                                .map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                        } else if is_ref_to_array {
                            // Reference to array: load pointer then two-index GEP
                            let array_ptr = self.builder.build_load(current_ptr, "array_ptr")
                                .map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM load error: {}", e), body.span
                                )])?.into_pointer_value();
                            let zero = self.context.i64_type().const_zero();
                            self.builder.build_in_bounds_gep(array_ptr, &[zero, idx], "subslice")
                                .map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                        } else {
                            self.builder.build_in_bounds_gep(current_ptr, &[idx], "subslice")
                                .map_err(|e| vec![Diagnostic::error(
                                    format!("LLVM GEP error: {}", e), body.span
                                )])?
                        }
                    }
                }

                PlaceElem::Downcast(variant_idx_val) => {
                    // Downcast is logically an assertion that we have the right variant.
                    // Set variant context so Field knows how to access variant-specific fields.
                    // This is needed for heterogeneous enum payloads (different sized variants).
                    if let TypeKind::Adt { def_id, .. } = current_ty.kind() {
                        variant_ctx = Some((*def_id, *variant_idx_val));
                    }
                    current_ptr  // Return the same pointer
                }
            };
        }

        Ok(current_ptr)
    }

    fn compile_mir_place_load(
        &mut self,
        place: &Place,
        body: &MirBody,
        escape_results: Option<&EscapeResults>,
    ) -> Result<BasicValueEnum<'ctx>, Vec<Diagnostic>> {
        let ptr = self.compile_mir_place(place, body, escape_results)?;

        // Generation checks for region-tier allocations are implemented in
        // compile_mir_place() for PlaceElem::Deref. When dereferencing a pointer
        // that was allocated via blood_alloc_or_abort (Region/Persistent tier),
        // the local_generations map contains the generation storage location.
        // The Deref handler validates via blood_validate_generation and panics
        // on stale reference detection.
        //
        // Stack tier (NoEscape) values skip generation checks entirely as they
        // are guaranteed safe by lexical scoping - escape_results is passed to
        // compile_mir_place which checks escape state before emitting gen checks.

        // Load value from pointer
        let loaded = self.builder.build_load(ptr, "load")
            .map_err(|e| vec![Diagnostic::error(
                format!("LLVM load error: {}", e), body.span
            )])?;

        Ok(loaded)
    }

    fn compute_place_type(&self, base_ty: &Type, projections: &[PlaceElem]) -> Type {
        let mut current_ty = base_ty.clone();

        for proj in projections {
            current_ty = match proj {
                PlaceElem::Deref => {
                    // Dereference: unwrap Ref, Ptr, or Box types
                    match current_ty.kind() {
                        TypeKind::Ref { inner, .. } => inner.clone(),
                        TypeKind::Ptr { inner, .. } => inner.clone(),
                        // For Box<T>, the inner type is T
                        TypeKind::Adt { def_id, args } if Some(*def_id) == self.box_def_id => {
                            args.first().cloned().unwrap_or(current_ty)
                        }
                        // For other types, keep the type (should not happen in valid MIR)
                        _ => current_ty,
                    }
                }
                PlaceElem::Field(idx) => {
                    // Field access: get the field type from struct/tuple/ADT
                    match current_ty.kind() {
                        TypeKind::Tuple(tys) => {
                            tys.get(*idx as usize).cloned().unwrap_or(current_ty)
                        }
                        TypeKind::Adt { def_id, args } => {
                            // Handle built-in types first
                            if Some(*def_id) == self.vec_def_id {
                                // Vec<T> layout: { ptr: *T, len: i64, capacity: i64 }
                                match idx {
                                    0 => {
                                        // Field 0 is the data pointer *T
                                        let elem_ty = args.first().cloned().unwrap_or(Type::unit());
                                        Type::new(TypeKind::Ptr { inner: elem_ty, mutable: true })
                                    }
                                    1 | 2 => Type::usize(), // len and capacity
                                    _ => current_ty,
                                }
                            } else if Some(*def_id) == self.option_def_id {
                                // Option<T> layout: { tag: i32, payload: T }
                                match idx {
                                    0 => Type::i32(), // discriminant tag
                                    1 => args.first().cloned().unwrap_or(Type::unit()), // payload
                                    _ => current_ty,
                                }
                            } else if Some(*def_id) == self.result_def_id {
                                // Result<T, E> layout: { tag: i32, payload: T or E }
                                match idx {
                                    0 => Type::i32(), // discriminant tag
                                    1 => args.first().cloned().unwrap_or(Type::unit()), // ok payload
                                    2 => args.get(1).cloned().unwrap_or(Type::unit()), // err payload
                                    _ => current_ty,
                                }
                            } else if let Some(field_types) = self.struct_defs.get(def_id) {
                                // Regular struct - look up field type
                                if let Some(field_ty) = field_types.get(*idx as usize) {
                                    // Substitute type parameters with actual args
                                    self.substitute_type_params(field_ty, args)
                                } else {
                                    current_ty
                                }
                            } else if let Some(_variants) = self.enum_defs.get(def_id) {
                                // Enum - field access on enum value (after Downcast)
                                // For now, return current type since Downcast should handle this
                                current_ty
                            } else {
                                // Unknown ADT, keep type
                                current_ty
                            }
                        }
                        // For other types, keep the type
                        _ => current_ty,
                    }
                }
                PlaceElem::Index(_) | PlaceElem::ConstantIndex { .. } => {
                    // Array/slice indexing: get the element type
                    match current_ty.kind() {
                        TypeKind::Array { element, .. } => element.clone(),
                        TypeKind::Slice { element } => element.clone(),
                        // For Vec<T>, indexing gives T
                        TypeKind::Adt { def_id, args } if Some(*def_id) == self.vec_def_id => {
                            args.first().cloned().unwrap_or(current_ty)
                        }
                        // For other types, keep the type
                        _ => current_ty,
                    }
                }
                PlaceElem::Subslice { .. } => {
                    // Subslice keeps the same slice type
                    current_ty
                }
                PlaceElem::Downcast(variant_idx) => {
                    // Downcast to a specific enum variant - keep the type
                    let _ = variant_idx;
                    current_ty
                }
            };
        }

        current_ty
    }
}
