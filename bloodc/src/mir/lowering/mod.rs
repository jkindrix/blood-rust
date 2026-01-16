//! # HIR to MIR Lowering
//!
//! This module implements the translation from HIR (High-level IR) to
//! MIR (Mid-level IR).
//!
//! ## Lowering Process
//!
//! The lowering process transforms:
//! - Nested expressions → flat statements with temporaries
//! - Implicit control flow → explicit CFG edges
//! - Pattern matching → switch + goto
//! - Loops → CFG cycles
//!
//! ## Design References
//!
//! - [Rust MIR Lowering](https://rustc-dev-guide.rust-lang.org/mir/construction.html)
//! - Blood HIR in `hir/` module
//!
//! ## Example Lowering
//!
//! ```text
//! // HIR (nested)
//! let x = if cond { a + b } else { c };
//!
//! // MIR (flat CFG)
//! bb0:
//!     _1 = cond
//!     switchInt(_1) -> [true: bb1, false: bb2]
//! bb1:
//!     _2 = a
//!     _3 = b
//!     _4 = Add(_2, _3)
//!     _0 = _4
//!     goto -> bb3
//! bb2:
//!     _0 = c
//!     goto -> bb3
//! bb3:
//!     // continue...
//! ```

mod closure;
mod function;
mod util;

use std::collections::HashMap;

use crate::hir::{
    self, Body, Crate as HirCrate, DefId, ItemKind, Type,
};
use crate::diagnostics::Diagnostic;

use super::body::MirBody;
use super::types::BasicBlockId;

/// Information about an inline handler operation body needed for codegen.
///
/// This stores the HIR expression for inline handler bodies (try/with) so they
/// can be compiled to LLVM functions during code generation.
#[derive(Debug, Clone)]
pub struct InlineHandlerBody {
    /// The effect being handled.
    pub effect_id: DefId,
    /// The operation name.
    pub op_name: String,
    /// The operation index within the effect.
    pub op_index: u32,
    /// Parameter local IDs for binding operation parameters.
    pub params: Vec<hir::LocalId>,
    /// Parameter types.
    pub param_types: Vec<Type>,
    /// Return type of the operation.
    pub return_type: Type,
    /// The handler body expression.
    pub body: hir::Expr,
}

/// Map from synthetic DefId to inline handler body info.
pub type InlineHandlerBodies = HashMap<DefId, InlineHandlerBody>;

pub use closure::ClosureLowering;
pub use function::FunctionLowering;
pub use util::{convert_binop, convert_unop, lower_literal_to_constant, is_irrefutable_pattern, ExprLowering, LoopContextInfo};

// ============================================================================
// MIR Lowering Pass
// ============================================================================

/// Lowers HIR to MIR.
#[derive(Debug)]
pub struct MirLowering<'hir> {
    /// The HIR crate being lowered.
    hir: &'hir HirCrate,
    /// Lowered MIR bodies.
    bodies: HashMap<DefId, MirBody>,
    /// Collected diagnostics.
    diagnostics: Vec<Diagnostic>,
    /// Counter for generating synthetic closure DefIds.
    closure_counter: u32,
    /// Pending closure bodies to be lowered (body_id, synthetic def_id, captures with types).
    pending_closures: Vec<(hir::BodyId, DefId, Vec<(hir::Capture, Type)>)>,
    /// Inline handler bodies collected during lowering.
    /// Maps synthetic DefId to the handler body info for codegen.
    inline_handler_bodies: InlineHandlerBodies,
}

impl<'hir> MirLowering<'hir> {
    /// Create a new MIR lowering pass.
    pub fn new(hir: &'hir HirCrate) -> Self {
        Self {
            hir,
            bodies: HashMap::new(),
            diagnostics: Vec::new(),
            closure_counter: 0,
            pending_closures: Vec::new(),
            inline_handler_bodies: HashMap::new(),
        }
    }

    /// Lower all functions in the crate.
    ///
    /// Returns a tuple of:
    /// - MIR bodies for all functions and closures
    /// - Inline handler bodies for codegen (try/with blocks)
    pub fn lower_crate(&mut self) -> Result<(HashMap<DefId, MirBody>, InlineHandlerBodies), Vec<Diagnostic>> {
        // First pass: lower all top-level functions
        for (&def_id, item) in &self.hir.items {
            match &item.kind {
                ItemKind::Fn(fn_def) => {
                    if let Some(body_id) = fn_def.body_id {
                        if let Some(body) = self.hir.get_body(body_id) {
                            let mir_body = self.lower_function(def_id, &fn_def.sig, body)?;
                            self.bodies.insert(def_id, mir_body);
                        }
                    }
                }
                _ => {
                    // Skip non-function items for now
                }
            }
        }

        // Second pass: lower any pending closures discovered during first pass
        // Process iteratively since closures can contain nested closures
        while !self.pending_closures.is_empty() {
            let pending = std::mem::take(&mut self.pending_closures);
            for (body_id, closure_def_id, captures) in pending {
                if let Some(body) = self.hir.get_body(body_id) {
                    let mir_body = self.lower_closure_body(closure_def_id, body, &captures)?;
                    self.bodies.insert(closure_def_id, mir_body);
                }
            }
        }

        if self.diagnostics.is_empty() {
            Ok((std::mem::take(&mut self.bodies), std::mem::take(&mut self.inline_handler_bodies)))
        } else {
            Err(std::mem::take(&mut self.diagnostics))
        }
    }

    /// Lower a closure body to MIR.
    fn lower_closure_body(
        &mut self,
        def_id: DefId,
        body: &Body,
        captures: &[(hir::Capture, Type)],
    ) -> Result<MirBody, Vec<Diagnostic>> {
        // Closure bodies are lowered similarly to functions
        // The captures become implicit parameters accessed via the environment
        let builder = ClosureLowering::new(
            def_id,
            body,
            captures,
            self.hir,
            &mut self.pending_closures,
            &mut self.closure_counter,
            &mut self.inline_handler_bodies,
        );
        builder.lower()
    }

    /// Lower a single function.
    fn lower_function(
        &mut self,
        def_id: DefId,
        sig: &hir::FnSig,
        body: &Body,
    ) -> Result<MirBody, Vec<Diagnostic>> {
        let builder = FunctionLowering::new(
            def_id,
            sig,
            body,
            self.hir,
            &mut self.pending_closures,
            &mut self.closure_counter,
            &mut self.inline_handler_bodies,
        );
        builder.lower()
    }
}

/// Context for a loop (for break/continue handling).
#[derive(Debug, Clone)]
pub(super) struct LoopContext {
    /// Block to jump to on break.
    pub break_block: BasicBlockId,
    /// Block to jump to on continue.
    pub continue_block: BasicBlockId,
    /// Label for labeled breaks.
    pub label: Option<hir::LoopId>,
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mir_lowering_new() {
        let hir = HirCrate::new();
        let lowering = MirLowering::new(&hir);
        assert!(lowering.bodies.is_empty());
    }
}
