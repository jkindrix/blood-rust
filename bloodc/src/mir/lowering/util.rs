//! Utility functions for MIR lowering.
//!
//! This module provides shared utility functions for HIR→MIR lowering.
//! These functions are used by both `FunctionLowering` and `ClosureLowering`
//! to avoid code duplication.
//!
//! ## Functions
//!
//! - [`convert_binop`]: Convert AST binary operator to MIR binary operator
//! - [`convert_unop`]: Convert AST unary operator to MIR unary operator
//! - [`lower_literal_to_constant`]: Convert HIR literal to MIR constant
//! - [`is_irrefutable_pattern`]: Check if a pattern always matches

use crate::ast::{BinOp, UnaryOp};
use crate::hir::{LiteralValue, Pattern, PatternKind, Type};
use crate::mir::types::{BinOp as MirBinOp, UnOp as MirUnOp, Constant, ConstantKind};

// ============================================================================
// Operator Conversion
// ============================================================================

/// Convert HIR binary op to MIR binary op.
pub fn convert_binop(op: BinOp) -> MirBinOp {
    match op {
        BinOp::Add => MirBinOp::Add,
        BinOp::Sub => MirBinOp::Sub,
        BinOp::Mul => MirBinOp::Mul,
        BinOp::Div => MirBinOp::Div,
        BinOp::Rem => MirBinOp::Rem,
        BinOp::BitAnd => MirBinOp::BitAnd,
        BinOp::BitOr => MirBinOp::BitOr,
        BinOp::BitXor => MirBinOp::BitXor,
        BinOp::Shl => MirBinOp::Shl,
        BinOp::Shr => MirBinOp::Shr,
        BinOp::Eq => MirBinOp::Eq,
        BinOp::Ne => MirBinOp::Ne,
        BinOp::Lt => MirBinOp::Lt,
        BinOp::Le => MirBinOp::Le,
        BinOp::Gt => MirBinOp::Gt,
        BinOp::Ge => MirBinOp::Ge,
        BinOp::And => MirBinOp::BitAnd, // Logical and
        BinOp::Or => MirBinOp::BitOr,   // Logical or
        BinOp::Pipe => MirBinOp::BitOr, // Pipe operator (placeholder)
    }
}

/// Convert HIR unary op to MIR unary op.
///
/// Returns `None` for operators that require special handling:
/// - `Deref`: Creates a dereferenced place projection
/// - `Ref`/`RefMut`: Creates a reference to a place
///
/// These operators are handled directly in the lowering code.
pub fn convert_unop(op: UnaryOp) -> Option<MirUnOp> {
    match op {
        UnaryOp::Neg => Some(MirUnOp::Neg),
        UnaryOp::Not => Some(MirUnOp::Not),
        // These require special place-based handling
        UnaryOp::Deref | UnaryOp::Ref | UnaryOp::RefMut => None,
    }
}

// ============================================================================
// Literal Conversion
// ============================================================================

/// Convert a literal value to a MIR constant.
///
/// This is a pure utility function used during expression lowering
/// to convert HIR literal values into MIR constants.
pub fn lower_literal_to_constant(lit: &LiteralValue, ty: &Type) -> Constant {
    let kind = match lit {
        LiteralValue::Int(v) => ConstantKind::Int(*v),
        LiteralValue::Uint(v) => ConstantKind::Int(*v as i128),
        LiteralValue::Float(v) => ConstantKind::Float(*v),
        LiteralValue::Bool(v) => ConstantKind::Bool(*v),
        LiteralValue::Char(v) => ConstantKind::Char(*v),
        LiteralValue::String(v) => ConstantKind::String(v.clone()),
    };
    Constant::new(ty.clone(), kind)
}

// ============================================================================
// Pattern Analysis
// ============================================================================

/// Check if a pattern is irrefutable (always matches).
///
/// An irrefutable pattern is one that will match any value of its type.
/// This includes:
/// - Wildcard patterns (`_`)
/// - Simple bindings (`x`)
/// - Tuple patterns with all irrefutable sub-patterns
/// - Reference patterns with irrefutable inner patterns
/// - Struct patterns with all irrefutable field patterns
/// - Slice patterns with a rest element (`..`)
///
/// Refutable patterns (which may not match) include:
/// - Literal patterns (`1`, `"hello"`)
/// - Or patterns (`a | b`)
/// - Variant patterns (`Some(x)`)
/// - Range patterns (`1..10`)
pub fn is_irrefutable_pattern(pattern: &Pattern) -> bool {
    match &pattern.kind {
        PatternKind::Wildcard => true,
        PatternKind::Binding { subpattern, .. } => {
            subpattern.as_ref().map_or(true, |p| is_irrefutable_pattern(p))
        }
        PatternKind::Tuple(pats) => pats.iter().all(is_irrefutable_pattern),
        PatternKind::Ref { inner, .. } => is_irrefutable_pattern(inner),
        // These patterns are refutable (may not match)
        PatternKind::Literal(_) => false,
        PatternKind::Or(_) => false,
        PatternKind::Variant { .. } => false,
        PatternKind::Range { .. } => false,
        // Struct patterns are irrefutable if all field patterns are irrefutable
        PatternKind::Struct { fields, .. } => {
            fields.iter().all(|f| is_irrefutable_pattern(&f.pattern))
        }
        // Slice patterns with a rest element (..) are irrefutable
        PatternKind::Slice { prefix, slice, suffix } => {
            slice.is_some() &&
            prefix.iter().all(is_irrefutable_pattern) &&
            suffix.iter().all(is_irrefutable_pattern)
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::{DefId, FieldPattern, LocalId as HirLocalId};
    use crate::span::Span;

    #[test]
    fn test_convert_binop() {
        assert_eq!(convert_binop(BinOp::Add), MirBinOp::Add);
        assert_eq!(convert_binop(BinOp::Sub), MirBinOp::Sub);
        assert_eq!(convert_binop(BinOp::Eq), MirBinOp::Eq);
        assert_eq!(convert_binop(BinOp::And), MirBinOp::BitAnd);
        assert_eq!(convert_binop(BinOp::Or), MirBinOp::BitOr);
    }

    #[test]
    fn test_convert_unop() {
        assert_eq!(convert_unop(UnaryOp::Neg), Some(MirUnOp::Neg));
        assert_eq!(convert_unop(UnaryOp::Not), Some(MirUnOp::Not));
        // Special operators return None
        assert_eq!(convert_unop(UnaryOp::Deref), None);
        assert_eq!(convert_unop(UnaryOp::Ref), None);
        assert_eq!(convert_unop(UnaryOp::RefMut), None);
    }

    #[test]
    fn test_lower_literal_to_constant() {
        let int_lit = LiteralValue::Int(42);
        let int_const = lower_literal_to_constant(&int_lit, &Type::i64());
        assert!(matches!(int_const.kind, ConstantKind::Int(42)));

        let bool_lit = LiteralValue::Bool(true);
        let bool_const = lower_literal_to_constant(&bool_lit, &Type::bool());
        assert!(matches!(bool_const.kind, ConstantKind::Bool(true)));

        let string_lit = LiteralValue::String("hello".to_string());
        let string_const = lower_literal_to_constant(&string_lit, &Type::string());
        assert!(matches!(string_const.kind, ConstantKind::String(ref s) if s == "hello"));
    }

    fn make_pattern(kind: PatternKind) -> Pattern {
        Pattern {
            kind,
            ty: Type::i64(),
            span: Span::dummy(),
        }
    }

    #[test]
    fn test_is_irrefutable_wildcard() {
        let pat = make_pattern(PatternKind::Wildcard);
        assert!(is_irrefutable_pattern(&pat));
    }

    #[test]
    fn test_is_irrefutable_binding() {
        // Simple binding is irrefutable
        let pat = make_pattern(PatternKind::Binding {
            local_id: HirLocalId::new(1),
            mutable: false,
            subpattern: None,
        });
        assert!(is_irrefutable_pattern(&pat));

        // Binding with irrefutable subpattern is irrefutable
        let subpat = Box::new(make_pattern(PatternKind::Wildcard));
        let pat = make_pattern(PatternKind::Binding {
            local_id: HirLocalId::new(2),
            mutable: false,
            subpattern: Some(subpat),
        });
        assert!(is_irrefutable_pattern(&pat));

        // Binding with refutable subpattern is refutable
        let subpat = Box::new(make_pattern(PatternKind::Literal(LiteralValue::Int(42))));
        let pat = make_pattern(PatternKind::Binding {
            local_id: HirLocalId::new(3),
            mutable: false,
            subpattern: Some(subpat),
        });
        assert!(!is_irrefutable_pattern(&pat));
    }

    #[test]
    fn test_is_irrefutable_tuple() {
        // Empty tuple is irrefutable
        let pat = make_pattern(PatternKind::Tuple(vec![]));
        assert!(is_irrefutable_pattern(&pat));

        // Tuple with all irrefutable patterns is irrefutable
        let pat = make_pattern(PatternKind::Tuple(vec![
            make_pattern(PatternKind::Wildcard),
            make_pattern(PatternKind::Binding {
                local_id: HirLocalId::new(1),
                mutable: false,
                subpattern: None,
            }),
        ]));
        assert!(is_irrefutable_pattern(&pat));

        // Tuple with any refutable pattern is refutable
        let pat = make_pattern(PatternKind::Tuple(vec![
            make_pattern(PatternKind::Wildcard),
            make_pattern(PatternKind::Literal(LiteralValue::Int(42))),
        ]));
        assert!(!is_irrefutable_pattern(&pat));
    }

    #[test]
    fn test_is_refutable_literal() {
        let pat = make_pattern(PatternKind::Literal(LiteralValue::Int(42)));
        assert!(!is_irrefutable_pattern(&pat));
    }

    #[test]
    fn test_is_refutable_variant() {
        let pat = make_pattern(PatternKind::Variant {
            def_id: DefId::new(1),
            variant_idx: 0,
            fields: vec![],
        });
        assert!(!is_irrefutable_pattern(&pat));
    }

    #[test]
    fn test_is_irrefutable_struct() {
        // Struct with all irrefutable field patterns is irrefutable
        let pat = make_pattern(PatternKind::Struct {
            def_id: DefId::new(1),
            fields: vec![
                FieldPattern {
                    field_idx: 0,
                    pattern: make_pattern(PatternKind::Wildcard),
                },
            ],
        });
        assert!(is_irrefutable_pattern(&pat));

        // Struct with refutable field pattern is refutable
        let pat = make_pattern(PatternKind::Struct {
            def_id: DefId::new(1),
            fields: vec![
                FieldPattern {
                    field_idx: 0,
                    pattern: make_pattern(PatternKind::Literal(LiteralValue::Int(42))),
                },
            ],
        });
        assert!(!is_irrefutable_pattern(&pat));
    }

    #[test]
    fn test_is_irrefutable_slice() {
        // Slice with rest element is irrefutable
        let pat = make_pattern(PatternKind::Slice {
            prefix: vec![make_pattern(PatternKind::Wildcard)],
            slice: Some(Box::new(make_pattern(PatternKind::Wildcard))),
            suffix: vec![],
        });
        assert!(is_irrefutable_pattern(&pat));

        // Slice without rest element is refutable (must match exact length)
        let pat = make_pattern(PatternKind::Slice {
            prefix: vec![make_pattern(PatternKind::Wildcard)],
            slice: None,
            suffix: vec![],
        });
        assert!(!is_irrefutable_pattern(&pat));
    }

    // ============================================================================
    // Property Tests for MIR Lowering Correctness (FUZZ-004)
    // ============================================================================
    //
    // These property tests verify structural invariants of MIR lowering utilities.
    // They complement the unit tests above by testing algebraic properties rather
    // than specific examples.

    use proptest::prelude::*;

    // ------------------------------------------------------------------------
    // Binary Operator Property Tests
    // ------------------------------------------------------------------------

    /// Generate all AST binary operators.
    fn all_ast_binops() -> Vec<BinOp> {
        vec![
            BinOp::Add, BinOp::Sub, BinOp::Mul, BinOp::Div, BinOp::Rem,
            BinOp::Eq, BinOp::Ne, BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge,
            BinOp::And, BinOp::Or,
            BinOp::BitAnd, BinOp::BitOr, BinOp::BitXor, BinOp::Shl, BinOp::Shr,
            BinOp::Pipe,
        ]
    }

    /// Generate all MIR binary operators (for validation).
    fn all_mir_binops() -> Vec<MirBinOp> {
        vec![
            MirBinOp::Add, MirBinOp::Sub, MirBinOp::Mul, MirBinOp::Div, MirBinOp::Rem,
            MirBinOp::BitAnd, MirBinOp::BitOr, MirBinOp::BitXor,
            MirBinOp::Shl, MirBinOp::Shr,
            MirBinOp::Eq, MirBinOp::Ne, MirBinOp::Lt, MirBinOp::Le, MirBinOp::Gt, MirBinOp::Ge,
            MirBinOp::Offset,
        ]
    }

    // PROPERTY: BinOp conversion is total - every AST BinOp maps to some MIR BinOp
    #[test]
    fn test_property_binop_conversion_total() {
        for ast_op in all_ast_binops() {
            let mir_op = convert_binop(ast_op);
            // Verify result is a valid MIR binop (it compiles, so it's valid)
            // This ensures we don't panic and always produce a result
            let _ = mir_op;
        }
    }

    // PROPERTY: BinOp conversion produces valid MIR operators
    #[test]
    fn test_property_binop_conversion_valid_output() {
        let valid_mir_ops = all_mir_binops();
        for ast_op in all_ast_binops() {
            let mir_op = convert_binop(ast_op);
            assert!(
                valid_mir_ops.contains(&mir_op),
                "convert_binop({:?}) produced invalid MIR operator: {:?}",
                ast_op, mir_op
            );
        }
    }

    // PROPERTY: Arithmetic operators map to arithmetic MIR operators
    #[test]
    fn test_property_arithmetic_binop_preservation() {
        let arithmetic_pairs = vec![
            (BinOp::Add, MirBinOp::Add),
            (BinOp::Sub, MirBinOp::Sub),
            (BinOp::Mul, MirBinOp::Mul),
            (BinOp::Div, MirBinOp::Div),
            (BinOp::Rem, MirBinOp::Rem),
        ];
        for (ast_op, expected_mir_op) in arithmetic_pairs {
            assert_eq!(
                convert_binop(ast_op), expected_mir_op,
                "Arithmetic operator {:?} should map to {:?}", ast_op, expected_mir_op
            );
        }
    }

    // PROPERTY: Comparison operators map to comparison MIR operators
    #[test]
    fn test_property_comparison_binop_preservation() {
        let comparison_pairs = vec![
            (BinOp::Eq, MirBinOp::Eq),
            (BinOp::Ne, MirBinOp::Ne),
            (BinOp::Lt, MirBinOp::Lt),
            (BinOp::Le, MirBinOp::Le),
            (BinOp::Gt, MirBinOp::Gt),
            (BinOp::Ge, MirBinOp::Ge),
        ];
        for (ast_op, expected_mir_op) in comparison_pairs {
            assert_eq!(
                convert_binop(ast_op), expected_mir_op,
                "Comparison operator {:?} should map to {:?}", ast_op, expected_mir_op
            );
        }
    }

    // PROPERTY: Bitwise operators map to bitwise MIR operators
    #[test]
    fn test_property_bitwise_binop_preservation() {
        let bitwise_pairs = vec![
            (BinOp::BitAnd, MirBinOp::BitAnd),
            (BinOp::BitOr, MirBinOp::BitOr),
            (BinOp::BitXor, MirBinOp::BitXor),
            (BinOp::Shl, MirBinOp::Shl),
            (BinOp::Shr, MirBinOp::Shr),
        ];
        for (ast_op, expected_mir_op) in bitwise_pairs {
            assert_eq!(
                convert_binop(ast_op), expected_mir_op,
                "Bitwise operator {:?} should map to {:?}", ast_op, expected_mir_op
            );
        }
    }

    // ------------------------------------------------------------------------
    // Unary Operator Property Tests
    // ------------------------------------------------------------------------

    /// Generate all AST unary operators.
    fn all_ast_unops() -> Vec<UnaryOp> {
        vec![UnaryOp::Neg, UnaryOp::Not, UnaryOp::Deref, UnaryOp::Ref, UnaryOp::RefMut]
    }

    // PROPERTY: UnaryOp conversion is total - every AST UnaryOp either maps to
    // Some(MirUnOp) or None (for place-based operations)
    #[test]
    fn test_property_unop_conversion_total() {
        for ast_op in all_ast_unops() {
            // This should never panic
            let _ = convert_unop(ast_op);
        }
    }

    // PROPERTY: Simple unary operators (Neg, Not) always produce Some
    #[test]
    fn test_property_simple_unop_produces_some() {
        assert!(convert_unop(UnaryOp::Neg).is_some(), "Neg should map to Some");
        assert!(convert_unop(UnaryOp::Not).is_some(), "Not should map to Some");
    }

    // PROPERTY: Place-based unary operators (Deref, Ref, RefMut) always produce None
    #[test]
    fn test_property_place_unop_produces_none() {
        assert!(convert_unop(UnaryOp::Deref).is_none(), "Deref should map to None");
        assert!(convert_unop(UnaryOp::Ref).is_none(), "Ref should map to None");
        assert!(convert_unop(UnaryOp::RefMut).is_none(), "RefMut should map to None");
    }

    // PROPERTY: UnaryOp conversion preserves operator semantics
    #[test]
    fn test_property_unop_semantic_preservation() {
        assert_eq!(convert_unop(UnaryOp::Neg), Some(MirUnOp::Neg));
        assert_eq!(convert_unop(UnaryOp::Not), Some(MirUnOp::Not));
    }

    // ------------------------------------------------------------------------
    // Literal Conversion Property Tests
    // ------------------------------------------------------------------------

    // PROPERTY: Integer literal conversion preserves value
    proptest! {
        #[test]
        fn test_property_int_literal_value_preserved(value in any::<i64>()) {
            let lit = LiteralValue::Int(value as i128);
            let constant = lower_literal_to_constant(&lit, &Type::i64());
            match constant.kind {
                ConstantKind::Int(v) => assert_eq!(v, value as i128),
                _ => panic!("Expected Int constant"),
            }
        }
    }

    // PROPERTY: Unsigned literal conversion preserves value (within range)
    proptest! {
        #[test]
        fn test_property_uint_literal_value_preserved(value in 0u64..=i128::MAX as u64) {
            let lit = LiteralValue::Uint(value as u128);
            let constant = lower_literal_to_constant(&lit, &Type::u64());
            match constant.kind {
                ConstantKind::Int(v) => assert_eq!(v, value as i128),
                _ => panic!("Expected Int constant"),
            }
        }
    }

    // PROPERTY: Float literal conversion preserves value
    proptest! {
        #[test]
        fn test_property_float_literal_value_preserved(value in any::<f64>().prop_filter("not NaN", |v| !v.is_nan())) {
            let lit = LiteralValue::Float(value);
            let constant = lower_literal_to_constant(&lit, &Type::f64());
            match constant.kind {
                ConstantKind::Float(v) => {
                    if value.is_infinite() {
                        assert!(v.is_infinite() && v.signum() == value.signum());
                    } else {
                        assert_eq!(v, value);
                    }
                }
                _ => panic!("Expected Float constant"),
            }
        }
    }

    // PROPERTY: Boolean literal conversion preserves value
    proptest! {
        #[test]
        fn test_property_bool_literal_value_preserved(value in any::<bool>()) {
            let lit = LiteralValue::Bool(value);
            let constant = lower_literal_to_constant(&lit, &Type::bool());
            match constant.kind {
                ConstantKind::Bool(v) => assert_eq!(v, value),
                _ => panic!("Expected Bool constant"),
            }
        }
    }

    // PROPERTY: Char literal conversion preserves value
    proptest! {
        #[test]
        fn test_property_char_literal_value_preserved(value in any::<char>()) {
            let lit = LiteralValue::Char(value);
            let constant = lower_literal_to_constant(&lit, &Type::char());
            match constant.kind {
                ConstantKind::Char(v) => assert_eq!(v, value),
                _ => panic!("Expected Char constant"),
            }
        }
    }

    // PROPERTY: String literal conversion preserves value
    proptest! {
        #[test]
        fn test_property_string_literal_value_preserved(value in ".*") {
            let lit = LiteralValue::String(value.clone());
            let constant = lower_literal_to_constant(&lit, &Type::string());
            match &constant.kind {
                ConstantKind::String(v) => assert_eq!(v, &value),
                _ => panic!("Expected String constant"),
            }
        }
    }

    // PROPERTY: Literal conversion preserves type
    #[test]
    fn test_property_literal_type_preserved() {
        let test_cases: Vec<(LiteralValue, Type)> = vec![
            (LiteralValue::Int(42), Type::i32()),
            (LiteralValue::Int(-100), Type::i64()),
            (LiteralValue::Uint(42), Type::u32()),
            (LiteralValue::Float(3.14), Type::f32()),
            (LiteralValue::Float(2.718), Type::f64()),
            (LiteralValue::Bool(true), Type::bool()),
            (LiteralValue::Char('x'), Type::char()),
            (LiteralValue::String("hello".to_string()), Type::string()),
        ];

        for (lit, ty) in test_cases {
            let constant = lower_literal_to_constant(&lit, &ty);
            assert_eq!(
                constant.ty, ty,
                "Type should be preserved for literal {:?}", lit
            );
        }
    }

    // ------------------------------------------------------------------------
    // Pattern Irrefutability Property Tests
    // ------------------------------------------------------------------------

    // PROPERTY: Wildcard is always irrefutable
    #[test]
    fn test_property_wildcard_always_irrefutable() {
        let pat = make_pattern(PatternKind::Wildcard);
        assert!(is_irrefutable_pattern(&pat), "Wildcard must always be irrefutable");
    }

    // PROPERTY: Simple binding without subpattern is always irrefutable
    proptest! {
        #[test]
        fn test_property_simple_binding_always_irrefutable(
            local_id in 0u32..1000,
            mutable in any::<bool>()
        ) {
            let pat = make_pattern(PatternKind::Binding {
                local_id: HirLocalId::new(local_id),
                mutable,
                subpattern: None,
            });
            assert!(is_irrefutable_pattern(&pat), "Simple binding must be irrefutable");
        }
    }

    // PROPERTY: Literal patterns are always refutable
    #[test]
    fn test_property_literal_always_refutable() {
        let literals = vec![
            LiteralValue::Int(0),
            LiteralValue::Int(42),
            LiteralValue::Int(-1),
            LiteralValue::Uint(0),
            LiteralValue::Float(0.0),
            LiteralValue::Bool(true),
            LiteralValue::Bool(false),
            LiteralValue::Char('a'),
            LiteralValue::String("".to_string()),
        ];

        for lit in literals {
            let pat = make_pattern(PatternKind::Literal(lit.clone()));
            assert!(!is_irrefutable_pattern(&pat), "Literal {:?} must be refutable", lit);
        }
    }

    // PROPERTY: Variant patterns are always refutable
    proptest! {
        #[test]
        fn test_property_variant_always_refutable(
            def_id in 0u32..1000,
            variant_idx in 0u32..100
        ) {
            let pat = make_pattern(PatternKind::Variant {
                def_id: DefId::new(def_id),
                variant_idx,
                fields: vec![],
            });
            assert!(!is_irrefutable_pattern(&pat), "Variant pattern must be refutable");
        }
    }

    // PROPERTY: Or patterns are always refutable (by design choice)
    #[test]
    fn test_property_or_pattern_always_refutable() {
        // Even Or(wildcard, wildcard) is considered refutable in this implementation
        let pat = make_pattern(PatternKind::Or(vec![
            make_pattern(PatternKind::Wildcard),
            make_pattern(PatternKind::Wildcard),
        ]));
        assert!(!is_irrefutable_pattern(&pat), "Or pattern must be refutable");
    }

    // PROPERTY: Range patterns are always refutable
    #[test]
    fn test_property_range_pattern_always_refutable() {
        let pat = make_pattern(PatternKind::Range {
            start: None,
            end: None,
            inclusive: true,
        });
        assert!(!is_irrefutable_pattern(&pat), "Range pattern must be refutable");
    }

    // PROPERTY: Empty tuple is irrefutable
    #[test]
    fn test_property_empty_tuple_irrefutable() {
        let pat = make_pattern(PatternKind::Tuple(vec![]));
        assert!(is_irrefutable_pattern(&pat), "Empty tuple must be irrefutable");
    }

    // PROPERTY: Tuple of wildcards is irrefutable
    proptest! {
        #[test]
        fn test_property_tuple_of_wildcards_irrefutable(n in 0usize..10) {
            let pats: Vec<Pattern> = (0..n)
                .map(|_| make_pattern(PatternKind::Wildcard))
                .collect();
            let pat = make_pattern(PatternKind::Tuple(pats));
            assert!(is_irrefutable_pattern(&pat), "Tuple of wildcards must be irrefutable");
        }
    }

    // PROPERTY: Tuple with any literal element is refutable
    proptest! {
        #[test]
        fn test_property_tuple_with_literal_refutable(
            n in 1usize..5,
            lit_pos in 0usize..5
        ) {
            let lit_pos = lit_pos % n;  // Ensure lit_pos is valid
            let pats: Vec<Pattern> = (0..n)
                .map(|i| {
                    if i == lit_pos {
                        make_pattern(PatternKind::Literal(LiteralValue::Int(42)))
                    } else {
                        make_pattern(PatternKind::Wildcard)
                    }
                })
                .collect();
            let pat = make_pattern(PatternKind::Tuple(pats));
            assert!(!is_irrefutable_pattern(&pat), "Tuple with literal must be refutable");
        }
    }

    // PROPERTY: Ref pattern preserves irrefutability of inner pattern
    #[test]
    fn test_property_ref_preserves_irrefutability() {
        // Ref of wildcard is irrefutable
        let irrefutable_ref = make_pattern(PatternKind::Ref {
            mutable: false,
            inner: Box::new(make_pattern(PatternKind::Wildcard)),
        });
        assert!(is_irrefutable_pattern(&irrefutable_ref), "Ref of wildcard must be irrefutable");

        // Ref of literal is refutable
        let refutable_ref = make_pattern(PatternKind::Ref {
            mutable: true,
            inner: Box::new(make_pattern(PatternKind::Literal(LiteralValue::Int(42)))),
        });
        assert!(!is_irrefutable_pattern(&refutable_ref), "Ref of literal must be refutable");
    }

    // PROPERTY: Struct with all wildcard fields is irrefutable
    #[test]
    fn test_property_struct_all_wildcards_irrefutable() {
        let pat = make_pattern(PatternKind::Struct {
            def_id: DefId::new(1),
            fields: vec![
                FieldPattern {
                    field_idx: 0,
                    pattern: make_pattern(PatternKind::Wildcard),
                },
                FieldPattern {
                    field_idx: 1,
                    pattern: make_pattern(PatternKind::Wildcard),
                },
            ],
        });
        assert!(is_irrefutable_pattern(&pat), "Struct with all wildcards must be irrefutable");
    }

    // PROPERTY: Empty struct (no fields) is irrefutable
    #[test]
    fn test_property_empty_struct_irrefutable() {
        let pat = make_pattern(PatternKind::Struct {
            def_id: DefId::new(1),
            fields: vec![],
        });
        assert!(is_irrefutable_pattern(&pat), "Empty struct must be irrefutable");
    }

    // PROPERTY: Slice with rest element and irrefutable prefix/suffix is irrefutable
    #[test]
    fn test_property_slice_with_rest_irrefutable() {
        let pat = make_pattern(PatternKind::Slice {
            prefix: vec![
                make_pattern(PatternKind::Wildcard),
                make_pattern(PatternKind::Binding {
                    local_id: HirLocalId::new(1),
                    mutable: false,
                    subpattern: None,
                }),
            ],
            slice: Some(Box::new(make_pattern(PatternKind::Wildcard))),
            suffix: vec![make_pattern(PatternKind::Wildcard)],
        });
        assert!(is_irrefutable_pattern(&pat), "Slice with rest and irrefutable elements must be irrefutable");
    }

    // PROPERTY: Slice without rest element is always refutable
    proptest! {
        #[test]
        fn test_property_slice_without_rest_refutable(n in 0usize..5) {
            let pats: Vec<Pattern> = (0..n)
                .map(|_| make_pattern(PatternKind::Wildcard))
                .collect();
            let pat = make_pattern(PatternKind::Slice {
                prefix: pats,
                slice: None,
                suffix: vec![],
            });
            assert!(!is_irrefutable_pattern(&pat), "Slice without rest must be refutable");
        }
    }

    // PROPERTY: Binding with irrefutable subpattern is irrefutable
    #[test]
    fn test_property_binding_subpattern_irrefutability() {
        // Binding with wildcard subpattern is irrefutable
        let irrefutable = make_pattern(PatternKind::Binding {
            local_id: HirLocalId::new(1),
            mutable: false,
            subpattern: Some(Box::new(make_pattern(PatternKind::Wildcard))),
        });
        assert!(is_irrefutable_pattern(&irrefutable), "Binding @ _ must be irrefutable");

        // Binding with literal subpattern is refutable
        let refutable = make_pattern(PatternKind::Binding {
            local_id: HirLocalId::new(2),
            mutable: false,
            subpattern: Some(Box::new(make_pattern(PatternKind::Literal(LiteralValue::Int(0))))),
        });
        assert!(!is_irrefutable_pattern(&refutable), "Binding @ 0 must be refutable");
    }

    // PROPERTY: Deeply nested irrefutable patterns are irrefutable
    #[test]
    fn test_property_deeply_nested_irrefutable() {
        // (((_,), _), _) should be irrefutable
        let inner_tuple = make_pattern(PatternKind::Tuple(vec![
            make_pattern(PatternKind::Wildcard),
        ]));
        let middle_tuple = make_pattern(PatternKind::Tuple(vec![
            inner_tuple,
            make_pattern(PatternKind::Wildcard),
        ]));
        let outer_tuple = make_pattern(PatternKind::Tuple(vec![
            middle_tuple,
            make_pattern(PatternKind::Wildcard),
        ]));
        assert!(is_irrefutable_pattern(&outer_tuple), "Deeply nested wildcards must be irrefutable");
    }

    // PROPERTY: Single refutable element in deep nesting makes whole pattern refutable
    #[test]
    fn test_property_deeply_nested_single_refutable() {
        // (((42,), _), _) should be refutable because of the 42
        let inner_tuple = make_pattern(PatternKind::Tuple(vec![
            make_pattern(PatternKind::Literal(LiteralValue::Int(42))),
        ]));
        let middle_tuple = make_pattern(PatternKind::Tuple(vec![
            inner_tuple,
            make_pattern(PatternKind::Wildcard),
        ]));
        let outer_tuple = make_pattern(PatternKind::Tuple(vec![
            middle_tuple,
            make_pattern(PatternKind::Wildcard),
        ]));
        assert!(!is_irrefutable_pattern(&outer_tuple), "Deeply nested literal makes pattern refutable");
    }
}
