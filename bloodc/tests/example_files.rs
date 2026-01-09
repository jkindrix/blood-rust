//! Integration tests for all example Blood files.
//!
//! These tests ensure that all example files in the examples/ directory
//! can be parsed successfully without errors.

use bloodc::Parser;
use std::fs;

/// Test helper to parse a file and assert it succeeds.
fn parse_file_ok(path: &str) {
    let source = fs::read_to_string(path).unwrap_or_else(|e| {
        panic!("Failed to read file {path}: {e}");
    });

    let mut parser = Parser::new(&source);
    match parser.parse_program() {
        Ok(program) => {
            // Verify the program has some content
            assert!(
                program.declarations.len() > 0 || program.imports.len() > 0,
                "Parsed program from {path} should have declarations or imports"
            );
        }
        Err(errors) => {
            panic!(
                "Failed to parse {path}:\n{}",
                errors
                    .iter()
                    .map(|e| format!("  - {}", e.message))
                    .collect::<Vec<_>>()
                    .join("\n")
            );
        }
    }
}

#[test]
fn test_parse_hello_blood() {
    parse_file_ok("../examples/hello.blood");
}

#[test]
fn test_parse_simple_blood() {
    parse_file_ok("../examples/simple.blood");
}

#[test]
fn test_parse_test1_blood() {
    parse_file_ok("../examples/test1.blood");
}

#[test]
fn test_parse_test2_blood() {
    parse_file_ok("../examples/test2.blood");
}

#[test]
fn test_parse_test3_blood() {
    parse_file_ok("../examples/test3.blood");
}

#[test]
fn test_parse_test4_blood() {
    parse_file_ok("../examples/test4.blood");
}

#[test]
fn test_parse_test5_blood() {
    parse_file_ok("../examples/test5.blood");
}

#[test]
fn test_parse_test6_blood() {
    parse_file_ok("../examples/test6.blood");
}

/// Test that we can parse all example files in a loop.
/// This provides a single test that covers all files for quick validation.
#[test]
fn test_parse_all_examples() {
    let examples_dir = "../examples";
    let entries = fs::read_dir(examples_dir).unwrap_or_else(|e| {
        panic!("Failed to read examples directory: {e}");
    });

    let mut parsed_count = 0;
    let mut errors = Vec::new();

    for entry in entries {
        let entry = entry.expect("Failed to read directory entry");
        let path = entry.path();

        if path.extension().map_or(false, |ext| ext == "blood") {
            let path_str = path.to_string_lossy();
            let source = fs::read_to_string(&path).unwrap_or_else(|e| {
                panic!("Failed to read {path_str}: {e}");
            });

            let mut parser = Parser::new(&source);
            match parser.parse_program() {
                Ok(_) => {
                    parsed_count += 1;
                }
                Err(parse_errors) => {
                    errors.push(format!(
                        "{path_str}:\n{}",
                        parse_errors
                            .iter()
                            .map(|e| format!("    - {}", e.message))
                            .collect::<Vec<_>>()
                            .join("\n")
                    ));
                }
            }
        }
    }

    if !errors.is_empty() {
        panic!(
            "Failed to parse {} example files:\n{}",
            errors.len(),
            errors.join("\n\n")
        );
    }

    assert!(
        parsed_count >= 8,
        "Expected at least 8 example files, found {parsed_count}"
    );
}

/// Test parsing performance sanity check.
/// Ensures parsing the comprehensive hello.blood file is reasonably fast.
#[test]
fn test_parse_performance_sanity() {
    use std::time::Instant;

    let source = fs::read_to_string("../examples/hello.blood")
        .expect("Failed to read hello.blood");

    let start = Instant::now();
    for _ in 0..100 {
        let mut parser = Parser::new(&source);
        let _ = parser.parse_program();
    }
    let elapsed = start.elapsed();

    // Should be able to parse 100 times in under 1 second
    assert!(
        elapsed.as_secs() < 1,
        "Parsing hello.blood 100 times took {:?}, expected < 1s",
        elapsed
    );
}
