//! Codegen regression test suite.
//!
//! Compiles Blood source to LLVM IR and snapshots the result using insta.
//! When codegen changes, `cargo insta review` shows exactly what changed.
//!
//! Run:  cargo test -p bloodc codegen_regression
//! Review: cargo insta review

use std::path::Path;

use bloodc::codegen::{self, BloodOptLevel, EscapeAnalysisMap};
use bloodc::mir::{EscapeAnalyzer, MirLowering};
use bloodc::typeck::check_program;
use bloodc::Parser;

/// Compile Blood source code to LLVM IR (unoptimized for stable snapshots).
///
/// Returns the IR with volatile elements stripped for deterministic comparison.
fn compile_to_ir(source: &str) -> String {
    // Parse
    let mut parser = Parser::new(source);
    let program = parser
        .parse_program()
        .expect("fixture should parse without errors");
    let interner = parser.take_interner();

    // Type check → HIR
    let hir_crate = check_program(&program, source, interner)
        .expect("fixture should type-check without errors");

    // MIR lowering
    let mut mir_lowering = MirLowering::new(&hir_crate);
    let (mir_bodies, _inline_handlers) = mir_lowering
        .lower_crate()
        .expect("fixture should lower to MIR without errors");

    // Escape analysis (required by codegen)
    let escape_map: EscapeAnalysisMap = mir_bodies
        .iter()
        .map(|(&def_id, body)| {
            let mut analyzer = EscapeAnalyzer::new();
            (def_id, analyzer.analyze(body))
        })
        .collect();

    let builtin_def_ids = (None, None, None, None);

    // Generate unoptimized IR for stable snapshots
    let ir = codegen::compile_mir_to_ir_with_opt(
        &hir_crate,
        &mir_bodies,
        &escape_map,
        BloodOptLevel::None,
        builtin_def_ids,
    )
    .expect("fixture should codegen without errors");

    normalize_ir(&ir)
}

/// Strip volatile elements from LLVM IR so snapshots are deterministic
/// across machines and LLVM versions.
///
/// Also sorts top-level definitions alphabetically to handle HashMap
/// iteration order non-determinism.
fn normalize_ir(ir: &str) -> String {
    let mut filtered_lines: Vec<&str> = Vec::new();

    for line in ir.lines() {
        // Strip target datalayout and target triple (machine-specific)
        if line.starts_with("target datalayout") || line.starts_with("target triple") {
            continue;
        }
        // Strip source_filename (path-specific)
        if line.starts_with("source_filename") {
            continue;
        }
        // Strip LLVM module flags and debug metadata IDs (volatile across versions)
        if line.starts_with("!llvm.") || (line.starts_with('!') && !line.starts_with("!\"")) {
            continue;
        }
        // Strip attributes blocks (can vary by LLVM version)
        if line.starts_with("attributes #") {
            continue;
        }
        filtered_lines.push(line);
    }

    // Remove trailing blank lines
    while filtered_lines.last() == Some(&"") {
        filtered_lines.pop();
    }

    // Split IR into top-level blocks (functions, declares, type defs) and sort
    // to ensure deterministic output regardless of HashMap iteration order.
    let text = filtered_lines.join("\n");
    let mut blocks: Vec<String> = Vec::new();
    let mut current_block = String::new();

    for line in text.lines() {
        let is_toplevel_start = line.starts_with("define ")
            || line.starts_with("declare ")
            || (line.starts_with('%') && line.contains(" = type "));

        if is_toplevel_start && !current_block.trim().is_empty() {
            blocks.push(current_block.trim_end().to_string());
            current_block = String::new();
        }
        current_block.push_str(line);
        current_block.push('\n');
    }
    if !current_block.trim().is_empty() {
        blocks.push(current_block.trim_end().to_string());
    }

    blocks.sort();
    blocks.join("\n\n")
}

/// Load a fixture file relative to the test fixtures directory.
fn load_fixture(name: &str) -> String {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let fixture_path = Path::new(manifest_dir)
        .join("tests/codegen_fixtures")
        .join(name);
    std::fs::read_to_string(&fixture_path)
        .unwrap_or_else(|e| panic!("Failed to read fixture {}: {}", fixture_path.display(), e))
}

// ============================================================================
// Smoke Tests — basic constructs produce valid IR
// ============================================================================

#[test]
fn test_basic_arithmetic_ir() {
    let source = load_fixture("basic_arithmetic.blood");
    let ir = compile_to_ir(&source);
    insta::assert_snapshot!(ir);
}

#[test]
fn test_if_else_ir() {
    let source = load_fixture("if_else.blood");
    let ir = compile_to_ir(&source);
    insta::assert_snapshot!(ir);
}

#[test]
fn test_while_loop_ir() {
    let source = load_fixture("while_loop.blood");
    let ir = compile_to_ir(&source);
    insta::assert_snapshot!(ir);
}

#[test]
fn test_function_calls_ir() {
    let source = load_fixture("function_calls.blood");
    let ir = compile_to_ir(&source);
    insta::assert_snapshot!(ir);
}

#[test]
fn test_recursion_ir() {
    let source = load_fixture("recursion.blood");
    let ir = compile_to_ir(&source);
    insta::assert_snapshot!(ir);
}

// ============================================================================
// Struct / Enum IR Tests — regression for GEP and field access bugs
// ============================================================================

#[test]
fn test_struct_fields_ir() {
    let source = load_fixture("struct_fields.blood");
    let ir = compile_to_ir(&source);
    insta::assert_snapshot!(ir);
}

#[test]
fn test_nested_struct_ir() {
    let source = load_fixture("nested_struct.blood");
    let ir = compile_to_ir(&source);
    insta::assert_snapshot!(ir);
}

#[test]
fn test_enum_match_ir() {
    let source = load_fixture("enum_match.blood");
    let ir = compile_to_ir(&source);
    insta::assert_snapshot!(ir);
}

// ============================================================================
// Targeted Pattern Assertions — verify specific IR patterns exist
// ============================================================================

#[test]
fn test_arithmetic_produces_add_instruction() {
    let source = load_fixture("basic_arithmetic.blood");
    let ir = compile_to_ir(&source);
    assert!(
        ir.contains("add ") || ir.contains("add nsw"),
        "Expected 'add' instruction in IR for arithmetic:\n{}",
        ir
    );
}

#[test]
fn test_if_else_produces_branch() {
    let source = load_fixture("if_else.blood");
    let ir = compile_to_ir(&source);
    assert!(
        ir.contains("br i1") || ir.contains("br label"),
        "Expected branch instruction in IR for if/else:\n{}",
        ir
    );
}

#[test]
fn test_while_loop_produces_branch() {
    let source = load_fixture("while_loop.blood");
    let ir = compile_to_ir(&source);
    // Loops produce backedge branches
    assert!(
        ir.contains("br i1") || ir.contains("br label"),
        "Expected branch instruction in IR for while loop:\n{}",
        ir
    );
}

#[test]
fn test_struct_produces_getelementptr() {
    let source = load_fixture("struct_fields.blood");
    let ir = compile_to_ir(&source);
    assert!(
        ir.contains("getelementptr") || ir.contains("extractvalue"),
        "Expected GEP or extractvalue in IR for struct field access:\n{}",
        ir
    );
}

#[test]
fn test_function_call_produces_call_instruction() {
    let source = load_fixture("function_calls.blood");
    let ir = compile_to_ir(&source);
    assert!(
        ir.contains("call "),
        "Expected 'call' instruction in IR for function calls:\n{}",
        ir
    );
}
