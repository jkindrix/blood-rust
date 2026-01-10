//! # Work-Stealing Fiber Scheduler
//!
//! M:N cooperative scheduler with work-stealing.
//!
//! ## Design
//!
//! Based on the Blood runtime specification (ROADMAP.md §9.2):
//! - Multiple worker threads each with local deque
//! - Global queue for overflow
//! - Work-stealing for load balancing
//!
//! ## Technical References
//!
//! - [Chase-Lev Deque](https://doi.org/10.1145/1073970.1073974)
//! - [crossbeam-deque](https://docs.rs/crossbeam-deque)
//! - [Tokio Scheduler](https://tokio.rs/blog/2019-10-scheduler)

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread::{self, JoinHandle};

use crossbeam_deque::{Injector, Stealer, Worker as Deque};
use parking_lot::Mutex;

use crate::fiber::{Fiber, FiberConfig, FiberId, FiberState, WakeCondition};
use crate::SchedulerConfig;

/// Work-stealing scheduler for fibers.
pub struct Scheduler {
    /// Configuration.
    config: SchedulerConfig,
    /// Worker threads.
    workers: Vec<WorkerHandle>,
    /// Global injection queue.
    global_queue: Arc<Injector<FiberId>>,
    /// All fibers indexed by ID.
    fibers: Arc<Mutex<HashMap<FiberId, Fiber>>>,
    /// Stealers for work-stealing.
    stealers: Vec<Stealer<FiberId>>,
    /// Shutdown flag.
    shutdown: Arc<AtomicBool>,
    /// Number of active workers.
    active_workers: Arc<AtomicUsize>,
}

impl Scheduler {
    /// Create a new scheduler with the given configuration.
    pub fn new(config: SchedulerConfig) -> Self {
        let global_queue = Arc::new(Injector::new());
        let fibers = Arc::new(Mutex::new(HashMap::new()));
        let shutdown = Arc::new(AtomicBool::new(false));
        let active_workers = Arc::new(AtomicUsize::new(0));

        // Create worker deques and collect stealers
        let mut workers = Vec::with_capacity(config.num_workers);
        let mut stealers = Vec::with_capacity(config.num_workers);

        for id in 0..config.num_workers {
            let deque = Deque::new_fifo();
            stealers.push(deque.stealer());

            workers.push(WorkerHandle {
                id,
                deque,
                thread: None,
            });
        }

        Self {
            config,
            workers,
            global_queue,
            fibers,
            stealers,
            shutdown,
            active_workers,
        }
    }

    /// Get the number of workers.
    pub fn num_workers(&self) -> usize {
        self.config.num_workers
    }

    /// Spawn a new fiber with a task.
    pub fn spawn<F>(&self, task: F) -> FiberId
    where
        F: FnOnce() + Send + 'static,
    {
        self.spawn_with_config(task, FiberConfig::default())
    }

    /// Spawn a new fiber with configuration.
    pub fn spawn_with_config<F>(&self, task: F, config: FiberConfig) -> FiberId
    where
        F: FnOnce() + Send + 'static,
    {
        let fiber = Fiber::new(task, config);
        let id = fiber.id;

        // Add to fiber registry
        {
            let mut fibers = self.fibers.lock();
            fibers.insert(id, fiber);
        }

        // Push to global queue
        self.global_queue.push(id);

        id
    }

    /// Run the scheduler, blocking until shutdown.
    pub fn run(&mut self) {
        // Start worker threads
        let worker_count = self.workers.len();

        for i in 0..worker_count {
            let worker = Worker::new(
                i,
                self.global_queue.clone(),
                self.fibers.clone(),
                self.stealers.clone(),
                self.shutdown.clone(),
                self.active_workers.clone(),
            );

            // Take ownership of the deque
            let deque = std::mem::replace(
                &mut self.workers[i].deque,
                Deque::new_fifo(),
            );

            let handle = thread::Builder::new()
                .name(format!("blood-worker-{}", i))
                .spawn(move || worker.run_loop(deque))
                .expect("failed to spawn worker thread");

            self.workers[i].thread = Some(handle);
        }

        // Wait for all workers to finish
        for worker in &mut self.workers {
            if let Some(handle) = worker.thread.take() {
                let _ = handle.join();
            }
        }
    }

    /// Request scheduler shutdown.
    pub fn shutdown(&self) {
        self.shutdown.store(true, Ordering::Release);
    }

    /// Check if the scheduler is shutting down.
    pub fn is_shutting_down(&self) -> bool {
        self.shutdown.load(Ordering::Acquire)
    }

    /// Get the number of active fibers.
    pub fn active_fiber_count(&self) -> usize {
        self.fibers.lock().len()
    }

    /// Get the number of runnable fibers.
    pub fn runnable_fiber_count(&self) -> usize {
        self.fibers
            .lock()
            .values()
            .filter(|f| f.is_runnable())
            .count()
    }
}

/// Handle to a worker thread.
struct WorkerHandle {
    /// Worker ID (reserved for debugging).
    #[allow(dead_code)]
    id: usize,
    /// Local work deque.
    deque: Deque<FiberId>,
    /// Thread handle.
    thread: Option<JoinHandle<()>>,
}

/// A worker thread in the scheduler.
pub struct Worker {
    /// Worker ID (reserved for debugging and metrics).
    #[allow(dead_code)]
    id: usize,
    /// Global injection queue.
    global_queue: Arc<Injector<FiberId>>,
    /// All fibers.
    fibers: Arc<Mutex<HashMap<FiberId, Fiber>>>,
    /// Stealers from other workers.
    stealers: Vec<Stealer<FiberId>>,
    /// Shutdown flag.
    shutdown: Arc<AtomicBool>,
    /// Active worker count.
    active_workers: Arc<AtomicUsize>,
}

impl Worker {
    /// Create a new worker.
    fn new(
        id: usize,
        global_queue: Arc<Injector<FiberId>>,
        fibers: Arc<Mutex<HashMap<FiberId, Fiber>>>,
        stealers: Vec<Stealer<FiberId>>,
        shutdown: Arc<AtomicBool>,
        active_workers: Arc<AtomicUsize>,
    ) -> Self {
        Self {
            id,
            global_queue,
            fibers,
            stealers,
            shutdown,
            active_workers,
        }
    }

    /// Run the worker loop.
    fn run_loop(self, local: Deque<FiberId>) {
        self.active_workers.fetch_add(1, Ordering::AcqRel);

        loop {
            // Check for shutdown
            if self.shutdown.load(Ordering::Acquire) {
                break;
            }

            // Try to get work
            if let Some(fiber_id) = self.find_work(&local) {
                self.run_fiber(fiber_id);
            } else {
                // No work available, yield to OS
                thread::yield_now();
            }
        }

        self.active_workers.fetch_sub(1, Ordering::AcqRel);
    }

    /// Find work using work-stealing.
    fn find_work(&self, local: &Deque<FiberId>) -> Option<FiberId> {
        // 1. Try local queue first
        if let Some(id) = local.pop() {
            return Some(id);
        }

        // 2. Try global queue
        loop {
            match self.global_queue.steal() {
                crossbeam_deque::Steal::Success(id) => return Some(id),
                crossbeam_deque::Steal::Empty => break,
                crossbeam_deque::Steal::Retry => continue,
            }
        }

        // 3. Try stealing from other workers
        for stealer in &self.stealers {
            loop {
                match stealer.steal() {
                    crossbeam_deque::Steal::Success(id) => return Some(id),
                    crossbeam_deque::Steal::Empty => break,
                    crossbeam_deque::Steal::Retry => continue,
                }
            }
        }

        None
    }

    /// Run a fiber to completion or suspension.
    fn run_fiber(&self, fiber_id: FiberId) {
        // Get the fiber
        let mut fiber = {
            let mut fibers = self.fibers.lock();
            match fibers.remove(&fiber_id) {
                Some(f) => f,
                None => return, // Fiber was removed
            }
        };

        // Check if runnable
        if !fiber.is_runnable() {
            // Put it back
            let mut fibers = self.fibers.lock();
            fibers.insert(fiber_id, fiber);
            return;
        }

        // Run the fiber
        fiber.run();

        // Handle result based on state
        match fiber.state {
            FiberState::Completed | FiberState::Failed | FiberState::Cancelled => {
                // Fiber is done, don't re-add
            }
            FiberState::Suspended => {
                // Fiber is suspended, add back to registry (will be woken later)
                let mut fibers = self.fibers.lock();
                fibers.insert(fiber_id, fiber);
            }
            FiberState::Runnable => {
                // Fiber yielded, reschedule
                {
                    let mut fibers = self.fibers.lock();
                    fibers.insert(fiber_id, fiber);
                }
                self.global_queue.push(fiber_id);
            }
            _ => {
                // Other states, put back
                let mut fibers = self.fibers.lock();
                fibers.insert(fiber_id, fiber);
            }
        }
    }
}

/// Result of running a fiber.
#[derive(Debug, Clone, PartialEq)]
pub enum FiberResult {
    /// Fiber yielded control.
    Yielded,
    /// Fiber suspended waiting for condition.
    Suspended(WakeCondition),
    /// Fiber completed successfully.
    Completed,
    /// Fiber failed with error.
    Failed,
    /// Fiber was cancelled.
    Cancelled,
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicI32;
    use std::time::Duration;

    #[test]
    fn test_scheduler_creation() {
        let config = SchedulerConfig::default();
        let scheduler = Scheduler::new(config.clone());
        assert_eq!(scheduler.num_workers(), config.num_workers);
    }

    #[test]
    fn test_spawn_fiber() {
        let scheduler = Scheduler::new(SchedulerConfig::default());
        let id = scheduler.spawn(|| {});
        assert_eq!(scheduler.active_fiber_count(), 1);
        assert!(id.as_u64() > 0);
    }

    #[test]
    fn test_fiber_execution() {
        let counter = Arc::new(AtomicI32::new(0));
        let counter_clone = counter.clone();

        let scheduler = Scheduler::new(SchedulerConfig {
            num_workers: 1,
            ..Default::default()
        });

        scheduler.spawn(move || {
            counter_clone.fetch_add(1, Ordering::SeqCst);
        });

        // Run in a separate thread with timeout
        let scheduler_arc = Arc::new(Mutex::new(scheduler));
        let scheduler_clone = scheduler_arc.clone();

        let handle = thread::spawn(move || {
            let mut sched = scheduler_clone.lock();

            // Spawn a shutdown task
            let shutdown_flag = sched.shutdown.clone();
            thread::spawn(move || {
                thread::sleep(Duration::from_millis(100));
                shutdown_flag.store(true, Ordering::Release);
            });

            sched.run();
        });

        // Wait for completion
        let _ = handle.join();

        assert_eq!(counter.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_multiple_fibers() {
        let counter = Arc::new(AtomicI32::new(0));
        let mut scheduler = Scheduler::new(SchedulerConfig {
            num_workers: 2,
            ..Default::default()
        });

        for _ in 0..10 {
            let c = counter.clone();
            scheduler.spawn(move || {
                c.fetch_add(1, Ordering::SeqCst);
            });
        }

        assert_eq!(scheduler.active_fiber_count(), 10);

        // Shutdown after short delay
        let shutdown = scheduler.shutdown.clone();
        thread::spawn(move || {
            thread::sleep(Duration::from_millis(100));
            shutdown.store(true, Ordering::Release);
        });

        scheduler.run();

        assert_eq!(counter.load(Ordering::SeqCst), 10);
    }

    #[test]
    fn test_work_stealing() {
        // This is a basic test that the work-stealing mechanism works
        let counter = Arc::new(AtomicI32::new(0));
        let mut scheduler = Scheduler::new(SchedulerConfig {
            num_workers: 4,
            ..Default::default()
        });

        // Spawn many fibers
        for _ in 0..100 {
            let c = counter.clone();
            scheduler.spawn(move || {
                c.fetch_add(1, Ordering::SeqCst);
            });
        }

        let shutdown = scheduler.shutdown.clone();
        thread::spawn(move || {
            thread::sleep(Duration::from_millis(200));
            shutdown.store(true, Ordering::Release);
        });

        scheduler.run();

        // All fibers should have run
        assert_eq!(counter.load(Ordering::SeqCst), 100);
    }
}
