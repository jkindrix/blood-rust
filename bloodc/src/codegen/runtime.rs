//! Runtime support for Blood programs.
//!
//! This module provides declarations and stubs for runtime functions
//! that Blood programs can call. For Phase 1, we provide basic I/O.
//!
//! The runtime is a separate C library that must be linked with
//! compiled Blood programs.

/// Runtime function names.
pub mod functions {
    /// Print an integer (no newline).
    pub const PRINT_INT: &str = "print_int";

    /// Print an integer with newline.
    pub const PRINTLN_INT: &str = "println_int";

    /// Print a string (no newline).
    pub const PRINT_STR: &str = "print_str";

    /// Print a string with newline.
    pub const PRINTLN_STR: &str = "println_str";

    /// Allocate memory.
    pub const ALLOC: &str = "blood_alloc";

    /// Free memory.
    pub const FREE: &str = "blood_free";
}

/// Generate a minimal C runtime source.
///
/// This can be compiled with `cc -c runtime.c -o runtime.o` and linked
/// with Blood programs.
pub fn generate_c_runtime() -> String {
    r#"// Blood Runtime Library - Phase 1
// Compile with: cc -c runtime.c -o runtime.o

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void print_int(int n) {
    printf("%d", n);
}

void println_int(int n) {
    printf("%d\n", n);
}

void print_str(const char* s) {
    printf("%s", s);
}

void println_str(const char* s) {
    printf("%s\n", s);
}

void* blood_alloc(size_t size) {
    return malloc(size);
}

void blood_free(void* ptr) {
    free(ptr);
}
"#.to_string()
}
