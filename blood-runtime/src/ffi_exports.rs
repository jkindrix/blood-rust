//! # FFI Exports
//!
//! C-compatible exports for linking compiled Blood programs against the runtime.
//!
//! ## Design
//!
//! This module exposes the Blood runtime functionality via C ABI so that
//! compiled Blood programs (which use LLVM codegen) can link against
//! a static or shared library built from this crate.
//!
//! ## Usage
//!
//! Build as a cdylib or staticlib:
//! ```toml
//! [lib]
//! crate-type = ["cdylib", "staticlib", "rlib"]
//! ```
//!
//! Then link compiled Blood programs with `-lblood_runtime`.

use std::ffi::{c_char, c_int, c_void, CStr};
use std::io::{self, Write};

use crate::memory::{BloodPtr, PointerMetadata, generation};

// ============================================================================
// I/O Functions
// ============================================================================

/// Print an integer (no newline).
#[no_mangle]
pub extern "C" fn print_int(n: i32) {
    print!("{n}");
    let _ = io::stdout().flush();
}

/// Print an integer with newline.
#[no_mangle]
pub extern "C" fn println_int(n: i32) {
    println!("{n}");
}

/// Print a 64-bit integer with newline.
#[no_mangle]
pub extern "C" fn println_i64(n: i64) {
    println!("{n}");
}

/// Print a string (no newline).
///
/// # Safety
/// The pointer must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn print_str(s: *const c_char) {
    if !s.is_null() {
        if let Ok(cstr) = CStr::from_ptr(s).to_str() {
            print!("{cstr}");
            let _ = io::stdout().flush();
        }
    }
}

/// Print a string with newline.
///
/// # Safety
/// The pointer must be a valid null-terminated C string.
#[no_mangle]
pub unsafe extern "C" fn println_str(s: *const c_char) {
    if !s.is_null() {
        if let Ok(cstr) = CStr::from_ptr(s).to_str() {
            println!("{cstr}");
        }
    }
}

// ============================================================================
// Memory Management (Generational References)
// ============================================================================

/// Allocate memory with generational reference.
///
/// Returns a 128-bit Blood pointer (as two 64-bit values via out parameters).
/// Returns 0 on success, non-zero on failure.
///
/// # Safety
///
/// `out_addr` and `out_gen_meta` must be valid pointers to writable u64 locations.
#[no_mangle]
pub unsafe extern "C" fn blood_alloc(
    size: usize,
    out_addr: *mut u64,
    out_gen_meta: *mut u64,
) -> c_int {
    if out_addr.is_null() || out_gen_meta.is_null() {
        return -1;
    }

    // Use standard allocation for now
    let layout = match std::alloc::Layout::from_size_align(size, 8) {
        Ok(l) => l,
        Err(_) => return -2,
    };

    unsafe {
        let ptr = std::alloc::alloc(layout);
        if ptr.is_null() {
            return -3;
        }

        // Create a BloodPtr with initial generation (region allocation)
        let blood_ptr = BloodPtr::new(
            ptr as usize,
            generation::FIRST,
            PointerMetadata::REGION,
        );

        *out_addr = blood_ptr.address() as u64;
        *out_gen_meta = ((blood_ptr.generation() as u64) << 32) | (blood_ptr.metadata().bits() as u64);
    }

    0
}

/// Free memory allocated with blood_alloc.
///
/// # Safety
/// The address must have been allocated with blood_alloc.
#[no_mangle]
pub unsafe extern "C" fn blood_free(addr: u64, size: usize) {
    if addr == 0 {
        return;
    }

    let layout = match std::alloc::Layout::from_size_align(size, 8) {
        Ok(l) => l,
        Err(_) => return,
    };

    std::alloc::dealloc(addr as *mut u8, layout);
}

/// Check if a generational reference is valid.
///
/// Returns 1 if valid, 0 if stale.
#[no_mangle]
pub extern "C" fn blood_check_generation(
    expected_gen: u32,
    slot_gen: u32,
) -> c_int {
    // Persistent objects always valid
    if expected_gen == generation::PERSISTENT {
        return 1;
    }

    if expected_gen == slot_gen {
        1
    } else {
        0
    }
}

/// Get current generation from a memory slot.
///
/// # Safety
/// The address must point to a valid Blood allocation header.
#[no_mangle]
pub unsafe extern "C" fn blood_get_generation(addr: u64) -> u32 {
    if addr == 0 {
        return 0;
    }

    // In a real implementation, this would read from the slot header
    // For now, return a placeholder
    1
}

// ============================================================================
// Effect Runtime Support
// ============================================================================

/// Evidence vector for effect handlers.
///
/// Opaque handle to an evidence vector.
pub type EvidenceHandle = *mut c_void;

/// Create a new evidence vector.
#[no_mangle]
pub extern "C" fn blood_evidence_create() -> EvidenceHandle {
    let ev = Box::new(Vec::<u64>::new());
    Box::into_raw(ev) as EvidenceHandle
}

/// Destroy an evidence vector.
///
/// # Safety
/// The handle must have been created with blood_evidence_create.
#[no_mangle]
pub unsafe extern "C" fn blood_evidence_destroy(ev: EvidenceHandle) {
    if !ev.is_null() {
        let _ = Box::from_raw(ev as *mut Vec<u64>);
    }
}

/// Push a handler onto the evidence vector.
///
/// # Safety
/// The handle must be valid.
#[no_mangle]
pub unsafe extern "C" fn blood_evidence_push(ev: EvidenceHandle, handler_ptr: u64) {
    if !ev.is_null() {
        let vec = &mut *(ev as *mut Vec<u64>);
        vec.push(handler_ptr);
    }
}

/// Pop a handler from the evidence vector.
///
/// # Safety
/// The handle must be valid.
#[no_mangle]
pub unsafe extern "C" fn blood_evidence_pop(ev: EvidenceHandle) -> u64 {
    if ev.is_null() {
        return 0;
    }
    let vec = &mut *(ev as *mut Vec<u64>);
    vec.pop().unwrap_or(0)
}

/// Get handler at index from evidence vector.
///
/// # Safety
/// The handle must be valid.
#[no_mangle]
pub unsafe extern "C" fn blood_evidence_get(ev: EvidenceHandle, index: usize) -> u64 {
    if ev.is_null() {
        return 0;
    }
    let vec = &*(ev as *const Vec<u64>);
    vec.get(index).copied().unwrap_or(0)
}

// ============================================================================
// Fiber/Continuation Support (for effect handlers)
// ============================================================================

/// Fiber handle for continuation capture.
pub type FiberHandle = u64;

/// Create a new fiber for continuation capture.
///
/// Returns a fiber handle (0 on failure).
#[no_mangle]
pub extern "C" fn blood_fiber_create() -> FiberHandle {
    // Placeholder - real implementation would use the fiber scheduler
    static NEXT_FIBER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
    NEXT_FIBER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
}

/// Suspend current fiber and capture continuation.
///
/// Returns the captured continuation ID.
#[no_mangle]
pub extern "C" fn blood_fiber_suspend() -> u64 {
    // Placeholder - real implementation would save stack state
    0
}

/// Resume a suspended fiber with a value.
///
/// # Safety
/// The fiber handle must be valid.
#[no_mangle]
pub unsafe extern "C" fn blood_fiber_resume(_fiber: FiberHandle, _value: u64) {
    // Placeholder - real implementation would restore stack state
}

// ============================================================================
// Panic/Error Handling
// ============================================================================

/// Called when a stale reference is dereferenced.
///
/// By default, this aborts the program.
#[no_mangle]
pub extern "C" fn blood_stale_reference_panic(expected: u32, actual: u32) -> ! {
    eprintln!(
        "BLOOD RUNTIME ERROR: Stale reference detected!\n\
         Expected generation: {expected}, Actual: {actual}\n\
         This indicates use-after-free. Aborting."
    );
    std::process::abort();
}

/// Called on unrecoverable runtime errors.
///
/// # Safety
/// The message must be a valid C string.
#[no_mangle]
pub unsafe extern "C" fn blood_panic(msg: *const c_char) -> ! {
    let message = if msg.is_null() {
        "unknown error"
    } else {
        CStr::from_ptr(msg).to_str().unwrap_or("invalid UTF-8")
    };
    eprintln!("BLOOD RUNTIME PANIC: {message}");
    std::process::abort();
}

// ============================================================================
// Runtime Initialization
// ============================================================================

/// Initialize the Blood runtime.
///
/// Must be called before any other runtime functions.
/// Returns 0 on success, non-zero on failure.
#[no_mangle]
pub extern "C" fn blood_runtime_init() -> c_int {
    // Initialize any global state here
    0
}

/// Shutdown the Blood runtime.
///
/// Should be called when the program exits.
#[no_mangle]
pub extern "C" fn blood_runtime_shutdown() {
    // Cleanup any global state here
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_print_functions() {
        // Just verify they don't panic
        print_int(42);
        println_int(42);
        println_i64(42);
    }

    #[test]
    fn test_evidence_vector() {
        unsafe {
            let ev = blood_evidence_create();
            assert!(!ev.is_null());

            blood_evidence_push(ev, 100);
            blood_evidence_push(ev, 200);

            assert_eq!(blood_evidence_get(ev, 0), 100);
            assert_eq!(blood_evidence_get(ev, 1), 200);

            assert_eq!(blood_evidence_pop(ev), 200);
            assert_eq!(blood_evidence_pop(ev), 100);

            blood_evidence_destroy(ev);
        }
    }

    #[test]
    fn test_generation_check() {
        assert_eq!(blood_check_generation(1, 1), 1);
        assert_eq!(blood_check_generation(1, 2), 0);
        assert_eq!(blood_check_generation(generation::PERSISTENT, 999), 1);
    }

    #[test]
    fn test_runtime_init() {
        assert_eq!(blood_runtime_init(), 0);
        blood_runtime_shutdown();
    }
}
