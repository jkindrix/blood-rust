//! Type unification for Blood.
//!
//! This module implements unification for type inference. The algorithm
//! is based on Hindley-Milner with some extensions for Blood's type system.
//!
//! # Algorithm
//!
//! Unification finds a substitution that makes two types equal:
//!
//! ```text
//! unify(?T, i32)     => ?T = i32
//! unify(?T, ?U)      => ?T = ?U (or vice versa)
//! unify(i32, String) => ERROR
//! ```
//!
//! The algorithm uses a union-find structure for efficient variable resolution.

use std::collections::HashMap;

use crate::hir::{Type, TypeKind, TyVarId};

use super::error::{TypeError, TypeErrorKind};
use crate::span::Span;

/// The unifier maintains type variable substitutions.
#[derive(Debug, Clone)]
pub struct Unifier {
    /// Type variable substitutions.
    /// Maps type variable ID to its resolved type (or another variable).
    substitutions: HashMap<TyVarId, Type>,
    /// The next type variable ID to assign.
    next_var: u32,
}

impl Unifier {
    /// Create a new unifier.
    pub fn new() -> Self {
        Self {
            substitutions: HashMap::new(),
            next_var: 0,
        }
    }

    /// Create a fresh type variable.
    pub fn fresh_var(&mut self) -> Type {
        let id = TyVarId::new(self.next_var);
        self.next_var += 1;
        Type::infer(id)
    }

    /// Create multiple fresh type variables.
    pub fn fresh_vars(&mut self, count: usize) -> Vec<Type> {
        (0..count).map(|_| self.fresh_var()).collect()
    }

    /// Unify two types, recording substitutions.
    ///
    /// Returns Ok(()) if unification succeeds, Err if types are incompatible.
    pub fn unify(&mut self, t1: &Type, t2: &Type, span: Span) -> Result<(), TypeError> {
        // Resolve any existing substitutions
        let t1 = self.resolve(t1);
        let t2 = self.resolve(t2);

        match (t1.kind(), t2.kind()) {
            // Same primitive types
            (TypeKind::Primitive(p1), TypeKind::Primitive(p2)) if p1 == p2 => Ok(()),

            // Same ADT with unifiable arguments
            (TypeKind::Adt { def_id: d1, args: a1 }, TypeKind::Adt { def_id: d2, args: a2 })
                if d1 == d2 =>
            {
                if a1.len() != a2.len() {
                    return Err(TypeError::new(
                        TypeErrorKind::Mismatch {
                            expected: t1.clone(),
                            found: t2.clone(),
                        },
                        span,
                    ));
                }
                for (arg1, arg2) in a1.iter().zip(a2.iter()) {
                    self.unify(arg1, arg2, span)?;
                }
                Ok(())
            }

            // Tuples with same length
            (TypeKind::Tuple(ts1), TypeKind::Tuple(ts2)) if ts1.len() == ts2.len() => {
                for (t1, t2) in ts1.iter().zip(ts2.iter()) {
                    self.unify(t1, t2, span)?;
                }
                Ok(())
            }

            // Arrays with same size
            (
                TypeKind::Array { element: e1, size: s1 },
                TypeKind::Array { element: e2, size: s2 },
            ) if s1 == s2 => self.unify(e1, e2, span),

            // Slices
            (TypeKind::Slice { element: e1 }, TypeKind::Slice { element: e2 }) => {
                self.unify(e1, e2, span)
            }

            // References with same mutability
            (
                TypeKind::Ref { inner: i1, mutable: m1 },
                TypeKind::Ref { inner: i2, mutable: m2 },
            ) if m1 == m2 => self.unify(i1, i2, span),

            // Pointers with same mutability
            (
                TypeKind::Ptr { inner: i1, mutable: m1 },
                TypeKind::Ptr { inner: i2, mutable: m2 },
            ) if m1 == m2 => self.unify(i1, i2, span),

            // Functions
            (
                TypeKind::Fn { params: p1, ret: r1 },
                TypeKind::Fn { params: p2, ret: r2 },
            ) if p1.len() == p2.len() => {
                for (param1, param2) in p1.iter().zip(p2.iter()) {
                    self.unify(param1, param2, span)?;
                }
                self.unify(r1, r2, span)
            }

            // Never type unifies with anything
            (TypeKind::Never, _) | (_, TypeKind::Never) => Ok(()),

            // Error type unifies with anything (for error recovery)
            (TypeKind::Error, _) | (_, TypeKind::Error) => Ok(()),

            // Inference variable - bind it
            (TypeKind::Infer(id), _) => {
                self.bind(*id, t2.clone(), span)
            }
            (_, TypeKind::Infer(id)) => {
                self.bind(*id, t1.clone(), span)
            }

            // Type parameter - for now, treat as error (needs constraint solving)
            (TypeKind::Param(id1), TypeKind::Param(id2)) if id1 == id2 => Ok(()),

            // No match
            _ => Err(TypeError::new(
                TypeErrorKind::Mismatch {
                    expected: t1.clone(),
                    found: t2.clone(),
                },
                span,
            )),
        }
    }

    /// Bind a type variable to a type.
    fn bind(&mut self, var: TyVarId, ty: Type, span: Span) -> Result<(), TypeError> {
        // Occurs check: prevent infinite types like ?T = List<?T>
        if self.occurs_in(var, &ty) {
            return Err(TypeError::new(TypeErrorKind::InfiniteType, span));
        }

        self.substitutions.insert(var, ty);
        Ok(())
    }

    /// Check if a type variable occurs in a type.
    fn occurs_in(&self, var: TyVarId, ty: &Type) -> bool {
        let ty = self.resolve(ty);
        match ty.kind() {
            TypeKind::Infer(id) => *id == var,
            TypeKind::Tuple(tys) => tys.iter().any(|t| self.occurs_in(var, t)),
            TypeKind::Array { element, .. } => self.occurs_in(var, element),
            TypeKind::Slice { element } => self.occurs_in(var, element),
            TypeKind::Ref { inner, .. } | TypeKind::Ptr { inner, .. } => {
                self.occurs_in(var, inner)
            }
            TypeKind::Fn { params, ret } => {
                params.iter().any(|t| self.occurs_in(var, t)) || self.occurs_in(var, ret)
            }
            TypeKind::Adt { args, .. } => args.iter().any(|t| self.occurs_in(var, t)),
            _ => false,
        }
    }

    /// Resolve a type by following substitutions.
    pub fn resolve(&self, ty: &Type) -> Type {
        match ty.kind() {
            TypeKind::Infer(id) => {
                if let Some(substituted) = self.substitutions.get(id) {
                    self.resolve(substituted)
                } else {
                    ty.clone()
                }
            }
            TypeKind::Tuple(tys) => {
                Type::tuple(tys.iter().map(|t| self.resolve(t)).collect())
            }
            TypeKind::Array { element, size } => {
                Type::array(self.resolve(element), *size)
            }
            TypeKind::Slice { element } => Type::slice(self.resolve(element)),
            TypeKind::Ref { inner, mutable } => {
                Type::reference(self.resolve(inner), *mutable)
            }
            TypeKind::Ptr { inner, mutable } => {
                Type::new(TypeKind::Ptr {
                    inner: self.resolve(inner),
                    mutable: *mutable,
                })
            }
            TypeKind::Fn { params, ret } => Type::function(
                params.iter().map(|t| self.resolve(t)).collect(),
                self.resolve(ret),
            ),
            TypeKind::Adt { def_id, args } => Type::adt(
                *def_id,
                args.iter().map(|t| self.resolve(t)).collect(),
            ),
            _ => ty.clone(),
        }
    }

    /// Check if a type is fully resolved (no inference variables).
    pub fn is_resolved(&self, ty: &Type) -> bool {
        let ty = self.resolve(ty);
        !ty.has_type_vars()
    }

    /// Get all substitutions.
    pub fn substitutions(&self) -> &HashMap<TyVarId, Type> {
        &self.substitutions
    }
}

impl Default for Unifier {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unify_primitives() {
        let mut u = Unifier::new();
        let span = Span::dummy();

        // Same primitives should unify
        assert!(u.unify(&Type::i32(), &Type::i32(), span).is_ok());
        assert!(u.unify(&Type::bool(), &Type::bool(), span).is_ok());

        // Different primitives should not unify
        assert!(u.unify(&Type::i32(), &Type::bool(), span).is_err());
    }

    #[test]
    fn test_unify_variable() {
        let mut u = Unifier::new();
        let span = Span::dummy();

        let var = u.fresh_var();
        assert!(u.unify(&var, &Type::i32(), span).is_ok());

        // Variable should now resolve to i32
        let resolved = u.resolve(&var);
        assert_eq!(resolved, Type::i32());
    }

    #[test]
    fn test_unify_tuples() {
        let mut u = Unifier::new();
        let span = Span::dummy();

        let t1 = Type::tuple(vec![Type::i32(), Type::bool()]);
        let t2 = Type::tuple(vec![Type::i32(), Type::bool()]);
        assert!(u.unify(&t1, &t2, span).is_ok());

        // Different lengths should fail
        let t3 = Type::tuple(vec![Type::i32()]);
        assert!(u.unify(&t1, &t3, span).is_err());
    }

    #[test]
    fn test_occurs_check() {
        let mut u = Unifier::new();
        let span = Span::dummy();

        let var = u.fresh_var();
        // Try to create infinite type: ?T = (?T,)
        let tuple = Type::tuple(vec![var.clone()]);
        assert!(u.unify(&var, &tuple, span).is_err());
    }
}
