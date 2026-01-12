//! # Blood Runtime Library
//!
//! The Blood runtime provides:
//!
//! - **Fiber Scheduler**: M:N cooperative scheduling with work-stealing
//! - **Channels**: Multi-producer multi-consumer communication
//! - **I/O Reactor**: Platform-native async I/O (io_uring, kqueue, IOCP)
//! - **FFI Support**: Safe foreign function interface
//! - **Standard Library**: Core types and effects
//!
//! ## Technical Standards
//!
//! Implementation follows these standards:
//!
//! - **Work Stealing**: Based on Chase-Lev deque per
//!   [crossbeam-deque](https://docs.rs/crossbeam-deque)
//! - **Channels**: MPMC channels per
//!   [crossbeam-channel](https://docs.rs/crossbeam-channel)
//! - **I/O**: Platform-native (io_uring on Linux 5.6+)
//! - **FFI**: Per Rust 2024 Edition with `unsafe extern`
//!
//! ## Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────┐
//! │                       BLOOD RUNTIME                              │
//! ├─────────────────────────────────────────────────────────────────┤
//! │                                                                  │
//! │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │
//! │  │   Scheduler  │  │   Channels   │  │  I/O Reactor │          │
//! │  │  (fiber.rs)  │  │ (channel.rs) │  │   (io.rs)    │          │
//! │  └──────────────┘  └──────────────┘  └──────────────┘          │
//! │         │                 │                 │                   │
//! │         └─────────────────┼─────────────────┘                   │
//! │                           │                                     │
//! │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐          │
//! │  │     FFI      │  │   Stdlib     │  │    Memory    │          │
//! │  │   (ffi.rs)   │  │ (stdlib.rs)  │  │ (memory.rs)  │          │
//! │  └──────────────┘  └──────────────┘  └──────────────┘          │
//! │                                                                  │
//! └─────────────────────────────────────────────────────────────────┘
//! ```

#![warn(missing_docs)]
#![warn(rust_2018_idioms)]

pub mod channel;
pub mod continuation;
pub mod fiber;
pub mod ffi;
pub mod ffi_exports;
pub mod io;
pub mod memory;
pub mod scheduler;
pub mod simd;
pub mod stdlib;
pub mod sync;

// Re-exports
pub use channel::{bounded, unbounded, Receiver, Sender};
pub use fiber::{Fiber, FiberId, FiberHandle, FiberState};
pub use scheduler::{Scheduler, Worker};
pub use sync::{Mutex, RwLock, Once, Barrier, Semaphore, OnceLock};

/// Runtime version.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Initialize the runtime with default configuration.
pub fn init() -> Scheduler {
    Scheduler::new(SchedulerConfig::default())
}

/// Initialize the runtime with custom configuration.
pub fn init_with(config: SchedulerConfig) -> Scheduler {
    Scheduler::new(config)
}

/// Configuration for the runtime scheduler.
#[derive(Debug, Clone)]
pub struct SchedulerConfig {
    /// Number of worker threads (default: number of CPUs).
    pub num_workers: usize,
    /// Initial fiber stack size in bytes (default: 8KB).
    pub initial_stack_size: usize,
    /// Maximum fiber stack size in bytes (default: 1MB).
    pub max_stack_size: usize,
    /// Enable work stealing (default: true).
    pub work_stealing: bool,
}

impl Default for SchedulerConfig {
    fn default() -> Self {
        Self {
            num_workers: num_cpus(),
            initial_stack_size: 8 * 1024,      // 8 KB
            max_stack_size: 1024 * 1024,       // 1 MB
            work_stealing: true,
        }
    }
}

/// Get the number of CPUs.
fn num_cpus() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scheduler_config_default() {
        let config = SchedulerConfig::default();
        assert!(config.num_workers >= 1);
        assert_eq!(config.initial_stack_size, 8 * 1024);
        assert_eq!(config.max_stack_size, 1024 * 1024);
        assert!(config.work_stealing);
    }
}
