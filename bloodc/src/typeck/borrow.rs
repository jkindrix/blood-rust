//! Borrow checking for Blood.
//!
//! This module implements basic borrow checking to enforce:
//! - No double mutable borrows of the same variable
//! - No mutable borrow while immutable borrow exists (and vice versa)
//!
//! The checker runs after type checking to analyze borrow patterns.
//!
//! # Limitations
//!
//! This is a simplified borrow checker that uses scope-based lifetime analysis.
//! It does not implement Rust's full non-lexical lifetimes (NLL) system.

use std::collections::HashMap;

use crate::ast::UnaryOp;
use crate::hir::{self, LocalId};
use crate::span::Span;
use crate::typeck::error::{TypeError, TypeErrorKind};

/// Tracks an active borrow of a variable.
#[derive(Debug, Clone)]
struct ActiveBorrow {
    /// The span where the borrow was created.
    span: Span,
    /// Whether this is a mutable borrow (stored for future use in error messages).
    #[allow(dead_code)]
    mutable: bool,
}

/// Tracks borrow state for a local variable.
#[derive(Debug, Clone, Default)]
struct BorrowState {
    /// Mutable borrows of this variable.
    mutable_borrows: Vec<ActiveBorrow>,
    /// Immutable borrows of this variable.
    immutable_borrows: Vec<ActiveBorrow>,
}

impl BorrowState {
    fn is_mutably_borrowed(&self) -> bool {
        !self.mutable_borrows.is_empty()
    }

    fn is_immutably_borrowed(&self) -> bool {
        !self.immutable_borrows.is_empty()
    }

    fn first_mutable_borrow(&self) -> Option<Span> {
        self.mutable_borrows.first().map(|b| b.span)
    }

    fn first_immutable_borrow(&self) -> Option<Span> {
        self.immutable_borrows.first().map(|b| b.span)
    }
}

/// Borrow checker context.
pub struct BorrowChecker<'hir> {
    /// Map from local ID to borrow state.
    borrows: HashMap<LocalId, BorrowState>,
    /// Map from local ID to variable name (for error messages).
    local_names: HashMap<LocalId, String>,
    /// Errors accumulated during checking.
    errors: Vec<TypeError>,
    /// HIR crate reference.
    #[allow(dead_code)]
    hir_crate: &'hir hir::Crate,
}

impl<'hir> BorrowChecker<'hir> {
    /// Create a new borrow checker.
    pub fn new(hir_crate: &'hir hir::Crate) -> Self {
        Self {
            borrows: HashMap::new(),
            local_names: HashMap::new(),
            errors: Vec::new(),
            hir_crate,
        }
    }

    /// Check borrows for a function body.
    pub fn check_body(&mut self, body: &hir::Body) -> Vec<TypeError> {
        // Register all local names for error messages
        for local in &body.locals {
            if let Some(name) = &local.name {
                self.local_names.insert(local.id, name.clone());
            }
        }

        // Walk the expression tree to track borrows
        self.check_expr(&body.expr);

        std::mem::take(&mut self.errors)
    }

    /// Get the name of a local for error messages.
    fn local_name(&self, local_id: LocalId) -> String {
        self.local_names
            .get(&local_id)
            .cloned()
            .unwrap_or_else(|| format!("_local{}", local_id.index()))
    }

    /// Check an expression for borrow violations.
    fn check_expr(&mut self, expr: &hir::Expr) {
        match &expr.kind {
            // Borrow expression - check for conflicts (explicit Borrow variant)
            hir::ExprKind::Borrow { expr: inner, mutable } => {
                self.check_borrow(inner, *mutable, expr.span);
                self.check_expr(inner);
            }

            // Unary Ref/RefMut - also a borrow (from AST unary operator path)
            hir::ExprKind::Unary { op: UnaryOp::Ref, operand } => {
                self.check_borrow(operand, false, expr.span);
                self.check_expr(operand);
            }
            hir::ExprKind::Unary { op: UnaryOp::RefMut, operand } => {
                self.check_borrow(operand, true, expr.span);
                self.check_expr(operand);
            }

            // Block - check all statements and final expression
            hir::ExprKind::Block { stmts, expr: tail }
            | hir::ExprKind::Region { stmts, expr: tail, .. } => {
                // Save borrow state at block entry
                let saved_state = self.borrows.clone();

                for stmt in stmts {
                    self.check_stmt(stmt);
                }
                if let Some(e) = tail {
                    self.check_expr(e);
                }

                // Restore borrow state when leaving block
                // (borrows created in the block go out of scope)
                self.borrows = saved_state;
            }

            // If expression - check all branches
            hir::ExprKind::If { condition, then_branch, else_branch } => {
                self.check_expr(condition);
                let saved_state = self.borrows.clone();
                self.check_expr(then_branch);
                self.borrows = saved_state.clone();
                if let Some(else_expr) = else_branch {
                    self.check_expr(else_expr);
                }
                self.borrows = saved_state;
            }

            // Match expression - check all arms
            hir::ExprKind::Match { scrutinee, arms } => {
                self.check_expr(scrutinee);
                let saved_state = self.borrows.clone();
                for arm in arms {
                    self.borrows = saved_state.clone();
                    if let Some(guard) = &arm.guard {
                        self.check_expr(guard);
                    }
                    self.check_expr(&arm.body);
                }
                self.borrows = saved_state;
            }

            // Loop expressions
            hir::ExprKind::Loop { body, .. } => {
                let saved_state = self.borrows.clone();
                self.check_expr(body);
                self.borrows = saved_state;
            }

            hir::ExprKind::While { condition, body, .. } => {
                let saved_state = self.borrows.clone();
                self.check_expr(condition);
                self.check_expr(body);
                self.borrows = saved_state;
            }

            // Binary operations
            hir::ExprKind::Binary { left, right, .. } => {
                self.check_expr(left);
                self.check_expr(right);
            }

            // Unary operations
            hir::ExprKind::Unary { operand, .. } => {
                self.check_expr(operand);
            }

            // Call expressions
            hir::ExprKind::Call { callee, args } => {
                self.check_expr(callee);
                for arg in args {
                    self.check_expr(arg);
                }
            }

            // Method calls
            hir::ExprKind::MethodCall { receiver, args, .. } => {
                self.check_expr(receiver);
                for arg in args {
                    self.check_expr(arg);
                }
            }

            // Field access
            hir::ExprKind::Field { base, .. } => {
                self.check_expr(base);
            }

            // Index access
            hir::ExprKind::Index { base, index } => {
                self.check_expr(base);
                self.check_expr(index);
            }

            // Tuple/array literals
            hir::ExprKind::Tuple(exprs) | hir::ExprKind::Array(exprs) => {
                for e in exprs {
                    self.check_expr(e);
                }
            }

            // Array repeat
            hir::ExprKind::Repeat { value, .. } => {
                self.check_expr(value);
            }

            // Struct literal
            hir::ExprKind::Struct { fields, base, .. } => {
                for field in fields {
                    self.check_expr(&field.value);
                }
                if let Some(base_expr) = base {
                    self.check_expr(base_expr);
                }
            }

            // Record literal
            hir::ExprKind::Record { fields } => {
                for field in fields {
                    self.check_expr(&field.value);
                }
            }

            // Variant construction
            hir::ExprKind::Variant { fields, .. } => {
                for field in fields {
                    self.check_expr(field);
                }
            }

            // AddrOf (raw pointer)
            hir::ExprKind::AddrOf { expr, .. } => {
                self.check_expr(expr);
            }

            // Dereference
            hir::ExprKind::Deref(inner) => {
                self.check_expr(inner);
            }

            // Cast
            hir::ExprKind::Cast { expr, .. } => {
                self.check_expr(expr);
            }

            // Return/break with value
            hir::ExprKind::Return(Some(e)) | hir::ExprKind::Break { value: Some(e), .. } => {
                self.check_expr(e);
            }

            // Closure
            hir::ExprKind::Closure { .. } => {
                // Closure bodies are checked separately
            }

            // Perform expression
            hir::ExprKind::Perform { args, .. } => {
                for arg in args {
                    self.check_expr(arg);
                }
            }

            // Handle expressions
            hir::ExprKind::Handle { body, handler_instance, .. } => {
                self.check_expr(body);
                self.check_expr(handler_instance);
            }

            hir::ExprKind::InlineHandle { body, handlers, .. } => {
                self.check_expr(body);
                for handler in handlers {
                    self.check_expr(&handler.body);
                }
            }

            // Assign expression
            hir::ExprKind::Assign { target, value } => {
                self.check_expr(target);
                self.check_expr(value);
            }

            // Let expression
            hir::ExprKind::Let { init, .. } => {
                self.check_expr(init);
            }

            // Unsafe block
            hir::ExprKind::Unsafe(inner) => {
                self.check_expr(inner);
            }

            // Resume with value
            hir::ExprKind::Resume { value: Some(v) } => {
                self.check_expr(v);
            }

            // Range expression
            hir::ExprKind::Range { start, end, .. } => {
                if let Some(s) = start {
                    self.check_expr(s);
                }
                if let Some(e) = end {
                    self.check_expr(e);
                }
            }

            // Macro expansion
            hir::ExprKind::MacroExpansion { args, named_args, .. } => {
                for arg in args {
                    self.check_expr(arg);
                }
                for (_, arg) in named_args {
                    self.check_expr(arg);
                }
            }

            // Vec literal
            hir::ExprKind::VecLiteral(exprs) => {
                for e in exprs {
                    self.check_expr(e);
                }
            }

            // Vec repeat
            hir::ExprKind::VecRepeat { value, count } => {
                self.check_expr(value);
                self.check_expr(count);
            }

            // Assert expression
            hir::ExprKind::Assert { condition, message } => {
                self.check_expr(condition);
                if let Some(msg) = message {
                    self.check_expr(msg);
                }
            }

            // Debug expression
            hir::ExprKind::Dbg(inner) => {
                self.check_expr(inner);
            }

            // Slice/Vec length
            hir::ExprKind::SliceLen(inner) | hir::ExprKind::VecLen(inner) => {
                self.check_expr(inner);
            }

            // Array to slice coercion
            hir::ExprKind::ArrayToSlice { expr, .. } => {
                self.check_expr(expr);
            }

            // Leaf nodes - no sub-expressions to check
            hir::ExprKind::Literal(_)
            | hir::ExprKind::Local(_)
            | hir::ExprKind::Def(_)
            | hir::ExprKind::Return(None)
            | hir::ExprKind::Break { value: None, .. }
            | hir::ExprKind::Continue { .. }
            | hir::ExprKind::Error
            | hir::ExprKind::MethodFamily { .. }
            | hir::ExprKind::ConstParam(_)
            | hir::ExprKind::Resume { value: None }
            | hir::ExprKind::Default => {}
        }
    }

    /// Check a statement for borrow violations.
    fn check_stmt(&mut self, stmt: &hir::Stmt) {
        match stmt {
            hir::Stmt::Let { init, local_id, .. } => {
                if let Some(init_expr) = init {
                    // IMPORTANT: Check for conflicts FIRST, then record the borrow.
                    // 1. Check the init expression for borrow conflicts
                    self.check_expr(init_expr);
                    // 2. If the init is a borrow, record it as active
                    self.record_borrow(*local_id, init_expr);
                }
            }
            hir::Stmt::Expr(expr) => {
                self.check_expr(expr);
            }
            hir::Stmt::Item(_) => {
                // Item declarations don't involve borrows
            }
        }
    }

    /// Record a borrow from a let binding's initializer.
    /// This should be called AFTER checking for conflicts.
    fn record_borrow(&mut self, _local_id: LocalId, init: &hir::Expr) {
        // If the init is a borrow expression, record it as an active borrow
        // Handle both explicit Borrow and Unary Ref/RefMut representations
        let (inner, mutable) = match &init.kind {
            hir::ExprKind::Borrow { expr: inner, mutable } => (Some(inner.as_ref()), *mutable),
            hir::ExprKind::Unary { op: UnaryOp::Ref, operand } => (Some(operand.as_ref()), false),
            hir::ExprKind::Unary { op: UnaryOp::RefMut, operand } => (Some(operand.as_ref()), true),
            _ => (None, false),
        };

        if let Some(inner) = inner {
            // Record that this local holds a borrow
            if let hir::ExprKind::Local(borrowed_id) = &inner.kind {
                let state = self.borrows.entry(*borrowed_id).or_default();
                let borrow = ActiveBorrow {
                    span: init.span,
                    mutable,
                };
                if mutable {
                    state.mutable_borrows.push(borrow);
                } else {
                    state.immutable_borrows.push(borrow);
                }
            }
        }
    }

    /// Check a borrow expression for conflicts.
    fn check_borrow(&mut self, inner: &hir::Expr, mutable: bool, span: Span) {
        // Only check borrows of local variables for now
        if let hir::ExprKind::Local(local_id) = &inner.kind {
            let name = self.local_name(*local_id);

            if let Some(state) = self.borrows.get(local_id) {
                if mutable {
                    // Trying to create a mutable borrow
                    if state.is_mutably_borrowed() {
                        // Already mutably borrowed - error!
                        self.errors.push(TypeError::new(
                            TypeErrorKind::DoubleMutableBorrow {
                                name,
                                first_borrow: state.first_mutable_borrow().unwrap(),
                                second_borrow: span,
                            },
                            span,
                        ));
                    } else if state.is_immutably_borrowed() {
                        // Already immutably borrowed - error!
                        self.errors.push(TypeError::new(
                            TypeErrorKind::MutableBorrowWhileImmutable {
                                name,
                                immutable_borrow: state.first_immutable_borrow().unwrap(),
                                mutable_borrow: span,
                            },
                            span,
                        ));
                    }
                } else {
                    // Trying to create an immutable borrow
                    if state.is_mutably_borrowed() {
                        // Already mutably borrowed - error!
                        self.errors.push(TypeError::new(
                            TypeErrorKind::ImmutableBorrowWhileMutable {
                                name,
                                mutable_borrow: state.first_mutable_borrow().unwrap(),
                                immutable_borrow: span,
                            },
                            span,
                        ));
                    }
                    // Multiple immutable borrows are allowed
                }
            }
        }
    }
}

/// Check borrows for all bodies in a crate.
pub fn check_crate_borrows(krate: &hir::Crate) -> Vec<TypeError> {
    let mut errors = Vec::new();

    for body in krate.bodies.values() {
        let mut checker = BorrowChecker::new(krate);
        errors.extend(checker.check_body(body));
    }

    errors
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_borrow_check_basic() {
        // Test will be implemented with actual HIR construction
        // For now, just verify the module compiles
        let krate = hir::Crate::new();
        let checker = BorrowChecker::new(&krate);
        assert!(checker.errors.is_empty());
    }
}
