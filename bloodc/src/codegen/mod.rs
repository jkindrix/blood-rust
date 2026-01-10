//! Code generation for Blood.
//!
//! This module generates LLVM IR from the HIR representation.
//! The code generator uses inkwell as a safe wrapper around LLVM.
//!
//! # Architecture
//!
//! ```text
//! HIR -> CodeGenerator -> LLVM IR -> Object Code
//! ```
//!
//! The code generator handles:
//! - Type lowering (HIR types to LLVM types)
//! - Function compilation
//! - Expression evaluation
//! - Control flow
//! - Memory management
//!
//! # Phase 1 Scope
//!
//! Phase 1 focuses on:
//! - Integer types (i32)
//! - Basic arithmetic
//! - Function calls
//! - If/else
//! - While loops
//! - Print support via runtime

pub mod context;
pub mod types;
pub mod expr;
pub mod runtime;

pub use context::CodegenContext;

use inkwell::context::Context;
use inkwell::targets::{Target, TargetMachine, InitializationConfig, CodeModel, RelocMode, FileType};
use inkwell::OptimizationLevel;

use std::collections::HashMap;
use std::path::Path;

use crate::hir::{self, DefId};
use crate::mir::EscapeResults;
use crate::diagnostics::Diagnostic;

/// Type alias for escape analysis results per function.
pub type EscapeAnalysisMap = HashMap<DefId, EscapeResults>;

/// Compile HIR to an object file.
pub fn compile_to_object(
    hir_crate: &hir::Crate,
    output_path: &Path,
) -> Result<(), Vec<Diagnostic>> {
    let context = Context::create();
    let module = context.create_module("blood_program");
    let builder = context.create_builder();

    let mut codegen = CodegenContext::new(&context, &module, &builder);

    // Generate code for all items
    codegen.compile_crate(hir_crate)?;

    // Verify the module
    if let Err(err) = module.verify() {
        return Err(vec![Diagnostic::error(
            format!("LLVM verification failed: {}", err.to_string()),
            crate::span::Span::dummy(),
        )]);
    }

    // Get target machine
    let target_machine = get_native_target_machine()
        .map_err(|e| vec![Diagnostic::error(e, crate::span::Span::dummy())])?;

    // Write object file
    target_machine
        .write_to_file(&module, FileType::Object, output_path)
        .map_err(|e| vec![Diagnostic::error(
            format!("Failed to write object file: {}", e.to_string()),
            crate::span::Span::dummy(),
        )])?;

    Ok(())
}

/// Compile HIR to LLVM IR text.
pub fn compile_to_ir(hir_crate: &hir::Crate) -> Result<String, Vec<Diagnostic>> {
    let context = Context::create();
    let module = context.create_module("blood_program");
    let builder = context.create_builder();

    let mut codegen = CodegenContext::new(&context, &module, &builder);
    codegen.compile_crate(hir_crate)?;

    Ok(module.print_to_string().to_string())
}

/// Compile HIR to an object file with escape analysis optimization.
///
/// When escape analysis results are provided, the code generator can:
/// - Skip generation checks for values that don't escape (NoEscape)
/// - Use stack allocation for non-escaping values
/// - Apply tier-appropriate allocation strategies
pub fn compile_to_object_with_analysis(
    hir_crate: &hir::Crate,
    escape_analysis: &EscapeAnalysisMap,
    output_path: &Path,
) -> Result<(), Vec<Diagnostic>> {
    let context = Context::create();
    let module = context.create_module("blood_program");
    let builder = context.create_builder();

    let mut codegen = CodegenContext::new(&context, &module, &builder);
    codegen.set_escape_analysis(escape_analysis.clone());

    // Generate code for all items
    codegen.compile_crate(hir_crate)?;

    // Verify the module
    if let Err(err) = module.verify() {
        return Err(vec![Diagnostic::error(
            format!("LLVM verification failed: {}", err.to_string()),
            crate::span::Span::dummy(),
        )]);
    }

    // Get target machine
    let target_machine = get_native_target_machine()
        .map_err(|e| vec![Diagnostic::error(e, crate::span::Span::dummy())])?;

    // Write object file
    target_machine
        .write_to_file(&module, FileType::Object, output_path)
        .map_err(|e| vec![Diagnostic::error(
            format!("Failed to write object file: {}", e.to_string()),
            crate::span::Span::dummy(),
        )])?;

    Ok(())
}

/// Compile HIR to LLVM IR text with escape analysis optimization.
pub fn compile_to_ir_with_analysis(
    hir_crate: &hir::Crate,
    escape_analysis: &EscapeAnalysisMap,
) -> Result<String, Vec<Diagnostic>> {
    let context = Context::create();
    let module = context.create_module("blood_program");
    let builder = context.create_builder();

    let mut codegen = CodegenContext::new(&context, &module, &builder);
    codegen.set_escape_analysis(escape_analysis.clone());
    codegen.compile_crate(hir_crate)?;

    Ok(module.print_to_string().to_string())
}

/// Get a target machine for the native platform.
fn get_native_target_machine() -> Result<TargetMachine, String> {
    Target::initialize_native(&InitializationConfig::default())
        .map_err(|e| format!("Failed to initialize native target: {}", e))?;

    let triple = TargetMachine::get_default_triple();
    let target = Target::from_triple(&triple)
        .map_err(|e| format!("Failed to get target: {}", e.to_string()))?;

    let cpu = TargetMachine::get_host_cpu_name();
    let features = TargetMachine::get_host_cpu_features();

    target
        .create_target_machine(
            &triple,
            cpu.to_str().unwrap_or("generic"),
            features.to_str().unwrap_or(""),
            OptimizationLevel::Default,
            RelocMode::PIC,  // Required for PIE executables
            CodeModel::Default,
        )
        .ok_or_else(|| "Failed to create target machine".to_string())
}
