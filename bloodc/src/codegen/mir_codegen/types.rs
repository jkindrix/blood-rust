//! MIR type-related code generation utilities.
//!
//! This module provides helper functions for type analysis and size computation
//! used in MIR code generation.

use inkwell::types::BasicTypeEnum;

use crate::hir::{Type, TypeKind};

use super::CodegenContext;

/// Extension trait for MIR type-related operations.
pub trait MirTypesCodegen<'ctx, 'a> {
    /// Get the size of an LLVM type in bytes.
    fn get_type_size_in_bytes(&self, ty: BasicTypeEnum<'ctx>) -> u64;
}

impl<'ctx, 'a> MirTypesCodegen<'ctx, 'a> for CodegenContext<'ctx, 'a> {
    fn get_type_size_in_bytes(&self, ty: BasicTypeEnum<'ctx>) -> u64 {
        match ty {
            BasicTypeEnum::IntType(t) => (t.get_bit_width() as u64).div_ceil(8),
            BasicTypeEnum::FloatType(t) => {
                // LLVM FloatType can be various sizes (16-bit half, 32-bit float, 64-bit double, etc.)
                // We compare against known types from the context to determine the size.
                let f32_ty = self.context.f32_type();
                let f64_ty = self.context.f64_type();
                let f128_ty = self.context.f128_type();
                let f16_ty = self.context.f16_type();

                if t == f64_ty {
                    8  // 64-bit double
                } else if t == f32_ty {
                    4  // 32-bit float
                } else if t == f128_ty {
                    16 // 128-bit quad precision
                } else if t == f16_ty {
                    2  // 16-bit half
                } else {
                    // Unknown float type - use target data layout as fallback
                    // For safety, assume 8 bytes (double) as conservative default
                    8
                }
            }
            BasicTypeEnum::PointerType(_) => 8, // 64-bit pointers
            BasicTypeEnum::ArrayType(t) => {
                let elem_size = self.get_type_size_in_bytes(t.get_element_type());
                elem_size * t.len() as u64
            }
            BasicTypeEnum::StructType(t) => {
                // Sum of field sizes (simplified - doesn't account for padding)
                let mut size = 0u64;
                for i in 0..t.count_fields() {
                    if let Some(field_ty) = t.get_field_type_at_index(i) {
                        size += self.get_type_size_in_bytes(field_ty);
                    }
                }
                size.max(1) // At least 1 byte for empty struct
            }
            BasicTypeEnum::VectorType(t) => {
                let elem_size = self.get_type_size_in_bytes(t.get_element_type());
                elem_size * t.get_size() as u64
            }
        }
    }
}

/// Check if a type may contain generational references.
///
/// Used to determine which locals need snapshot capture during
/// effect operations.
pub(super) fn type_may_contain_genref_impl(ty: &Type) -> bool {
    match &*ty.kind {
        // Pointer and reference types may contain generational references
        TypeKind::Ptr { .. } | TypeKind::Ref { .. } => true,

        // Arrays and slices may contain genrefs if their element type does
        TypeKind::Array { ref element, .. } => type_may_contain_genref_impl(element),
        TypeKind::Slice { ref element } => type_may_contain_genref_impl(element),

        // Tuples may contain genrefs if any element does
        TypeKind::Tuple(elems) => elems.iter().any(type_may_contain_genref_impl),

        // ADTs (structs, enums) might contain genrefs - be conservative
        TypeKind::Adt { .. } => true,

        // Functions might capture genrefs (as function pointers to closures)
        TypeKind::Fn { .. } => true,

        // Closures might capture genrefs in their environment
        TypeKind::Closure { .. } => true,

        // Range types may contain genrefs if their element type does
        TypeKind::Range { ref element, .. } => type_may_contain_genref_impl(element),

        // Primitives don't contain genrefs
        TypeKind::Primitive(_) => false,

        // Never and Error types don't contain genrefs
        TypeKind::Never | TypeKind::Error => false,

        // Trait objects may contain genrefs (data pointer)
        TypeKind::DynTrait { .. } => true,

        // Inference and type parameters - be conservative
        TypeKind::Infer(_) | TypeKind::Param(_) => true,

        // Records may contain genrefs if any field does
        TypeKind::Record { fields, .. } => fields.iter().any(|f| type_may_contain_genref_impl(&f.ty)),

        // Forall types may contain genrefs if body does
        TypeKind::Forall { body, .. } => type_may_contain_genref_impl(body),

        // Ownership-qualified types delegate to the inner type
        TypeKind::Ownership { inner, .. } => type_may_contain_genref_impl(inner),
    }
}
