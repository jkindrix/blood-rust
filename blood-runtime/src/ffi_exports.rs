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
    // Use the global scheduler if available
    if let Some(scheduler) = GLOBAL_SCHEDULER.get() {
        let sched = scheduler.lock();
        sched.spawn(|| {}).as_u64()
    } else {
        // Fallback: return a unique ID
        static NEXT_FIBER: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        NEXT_FIBER.fetch_add(1, std::sync::atomic::Ordering::SeqCst)
    }
}

/// Suspend current fiber and capture continuation.
///
/// Returns the captured continuation ID.
#[no_mangle]
pub extern "C" fn blood_fiber_suspend() -> u64 {
    // In a full implementation, this would capture the current continuation.
    // For now, just yield to the scheduler.
    std::thread::yield_now();
    0
}

/// Resume a suspended fiber with a value.
///
/// # Safety
/// The fiber handle must be valid.
#[no_mangle]
pub unsafe extern "C" fn blood_fiber_resume(_fiber: FiberHandle, _value: u64) {
    // Placeholder - real implementation would restore stack state
    // The scheduler will pick up the fiber when it becomes runnable
}

// ============================================================================
// Work-Stealing Scheduler FFI
// ============================================================================

use std::sync::OnceLock;
use parking_lot::Mutex;
use crate::scheduler::Scheduler;
use crate::SchedulerConfig;

/// Global scheduler instance for FFI access.
static GLOBAL_SCHEDULER: OnceLock<Mutex<Scheduler>> = OnceLock::new();

/// Scheduler thread handle for background execution.
static SCHEDULER_THREAD: OnceLock<Mutex<Option<std::thread::JoinHandle<()>>>> = OnceLock::new();

/// Initialize the global scheduler with the given number of workers.
///
/// Returns 0 on success, -1 if already initialized.
#[no_mangle]
pub extern "C" fn blood_scheduler_init(num_workers: usize) -> c_int {
    let workers = if num_workers == 0 {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
    } else {
        num_workers
    };

    let config = SchedulerConfig {
        num_workers: workers,
        ..Default::default()
    };

    match GLOBAL_SCHEDULER.set(Mutex::new(Scheduler::new(config))) {
        Ok(()) => {
            // Initialize thread handle storage
            let _ = SCHEDULER_THREAD.set(Mutex::new(None));
            0
        }
        Err(_) => -1, // Already initialized
    }
}

/// Get the global scheduler, initializing with defaults if needed.
fn get_or_init_scheduler() -> &'static Mutex<Scheduler> {
    GLOBAL_SCHEDULER.get_or_init(|| {
        let _ = SCHEDULER_THREAD.set(Mutex::new(None));
        Mutex::new(Scheduler::new(SchedulerConfig::default()))
    })
}

/// Spawn a task on the scheduler.
///
/// The `task_fn` is a function pointer that takes a single `arg` parameter.
/// Returns the fiber ID on success, 0 on failure.
///
/// # Safety
/// The function pointer must be valid.
#[no_mangle]
pub unsafe extern "C" fn blood_scheduler_spawn(
    task_fn: extern "C" fn(*mut c_void),
    arg: *mut c_void,
) -> u64 {
    let scheduler = get_or_init_scheduler();
    let sched = scheduler.lock();

    // Capture the function pointer and argument
    let fn_ptr = task_fn;
    let arg_ptr = arg as usize; // Convert to usize for Send

    let fiber_id = sched.spawn(move || {
        fn_ptr(arg_ptr as *mut c_void);
    });

    fiber_id.as_u64()
}

/// Spawn a simple task (no arguments).
///
/// # Safety
/// The function pointer must be valid.
#[no_mangle]
pub unsafe extern "C" fn blood_scheduler_spawn_simple(
    task_fn: extern "C" fn(),
) -> u64 {
    let scheduler = get_or_init_scheduler();
    let sched = scheduler.lock();

    // Wrap extern "C" fn in a closure to satisfy FnOnce trait
    let fiber_id = sched.spawn(move || task_fn());
    fiber_id.as_u64()
}

/// Yield the current fiber to the scheduler.
///
/// This allows other fibers to run.
#[no_mangle]
pub extern "C" fn blood_scheduler_yield() {
    std::thread::yield_now();
}

/// Run the scheduler in the current thread.
///
/// This function blocks until the scheduler is shut down.
/// Call blood_scheduler_shutdown() from another thread to stop it.
#[no_mangle]
pub extern "C" fn blood_scheduler_run() {
    let scheduler = get_or_init_scheduler();
    let mut sched = scheduler.lock();
    sched.run();
}

/// Run the scheduler in a background thread.
///
/// Returns 0 on success, -1 if already running.
#[no_mangle]
pub extern "C" fn blood_scheduler_run_background() -> c_int {
    // Ensure scheduler is initialized
    let _ = get_or_init_scheduler();

    if let Some(thread_holder) = SCHEDULER_THREAD.get() {
        let mut thread_guard = thread_holder.lock();

        // Check if already running
        if thread_guard.is_some() {
            return -1;
        }

        // Start scheduler in background thread
        let handle = std::thread::Builder::new()
            .name("blood-scheduler".to_string())
            .spawn(move || {
                let scheduler = get_or_init_scheduler();
                let mut sched = scheduler.lock();
                sched.run();
            })
            .ok();

        *thread_guard = handle;
        0
    } else {
        -1
    }
}

/// Shutdown the scheduler.
///
/// This signals all workers to stop and returns immediately.
/// Use blood_scheduler_wait() to wait for completion.
#[no_mangle]
pub extern "C" fn blood_scheduler_shutdown() {
    if let Some(scheduler) = GLOBAL_SCHEDULER.get() {
        let sched = scheduler.lock();
        sched.shutdown();
    }
}

/// Wait for the scheduler to finish.
///
/// This blocks until all workers have stopped.
#[no_mangle]
pub extern "C" fn blood_scheduler_wait() {
    if let Some(thread_holder) = SCHEDULER_THREAD.get() {
        let mut thread_guard = thread_holder.lock();
        if let Some(handle) = thread_guard.take() {
            let _ = handle.join();
        }
    }
}

/// Get the number of active fibers.
#[no_mangle]
pub extern "C" fn blood_scheduler_active_fibers() -> usize {
    if let Some(scheduler) = GLOBAL_SCHEDULER.get() {
        let sched = scheduler.lock();
        sched.active_fiber_count()
    } else {
        0
    }
}

/// Get the number of runnable fibers.
#[no_mangle]
pub extern "C" fn blood_scheduler_runnable_fibers() -> usize {
    if let Some(scheduler) = GLOBAL_SCHEDULER.get() {
        let sched = scheduler.lock();
        sched.runnable_fiber_count()
    } else {
        0
    }
}

/// Check if the scheduler is running.
#[no_mangle]
pub extern "C" fn blood_scheduler_is_running() -> c_int {
    if let Some(scheduler) = GLOBAL_SCHEDULER.get() {
        let sched = scheduler.lock();
        if sched.is_shutting_down() { 0 } else { 1 }
    } else {
        0
    }
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
