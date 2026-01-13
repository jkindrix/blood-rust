//! Escape analysis effectiveness benchmarks.
//!
//! Benchmarks for escape analysis optimization effectiveness,
//! measuring stack promotion rates and analysis overhead.
//!
//! Run with: cargo bench --bench escape_bench
//!
//! PERF-005: Benchmark escape analysis optimization effectiveness

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use std::collections::{HashMap, HashSet};

// ============================================================================
// Simulated MIR Structures for Benchmarking
// ============================================================================

/// Simulated local ID for benchmarking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct LocalId(u32);

impl LocalId {
    fn new(index: u32) -> Self {
        LocalId(index)
    }
}

/// Escape state (mirrors bloodc::mir::escape::EscapeState).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
enum EscapeState {
    #[default]
    NoEscape,
    ArgEscape,
    GlobalEscape,
}

impl EscapeState {
    fn join(self, other: EscapeState) -> EscapeState {
        std::cmp::max(self, other)
    }

    fn can_stack_allocate(self) -> bool {
        matches!(self, EscapeState::NoEscape)
    }
}

/// Simulated statement types that affect escape analysis.
#[derive(Debug, Clone)]
enum StatementKind {
    // Simple assignment: dest = src
    Assign { dest: LocalId, src: LocalId },
    // Assignment to field: dest.field = src
    FieldAssign { dest: LocalId, src: LocalId },
    // Reference taken: dest = &src
    RefOf { dest: LocalId, src: LocalId },
    // Call with args: dest = func(args...)
    Call { dest: LocalId, args: Vec<LocalId> },
    // Return value
    Return(LocalId),
    // Store to global
    StoreGlobal { src: LocalId },
    // Effect operation (captures values)
    EffectOp { args: Vec<LocalId> },
    // Closure creation with captures
    Closure { dest: LocalId, captures: Vec<LocalId> },
    // Just a regular statement (no escape implications)
    Nop,
}

/// A simulated MIR body for benchmarking escape analysis.
struct TestMirBody {
    /// Number of locals (including params)
    num_locals: u32,
    /// Number of parameters
    num_params: u32,
    /// Statements to analyze
    statements: Vec<StatementKind>,
}

impl TestMirBody {
    fn new(num_locals: u32, num_params: u32) -> Self {
        Self {
            num_locals,
            num_params,
            statements: Vec::new(),
        }
    }

    fn add_statement(&mut self, stmt: StatementKind) {
        self.statements.push(stmt);
    }

    fn locals(&self) -> impl Iterator<Item = LocalId> + '_ {
        (0..self.num_locals).map(LocalId::new)
    }

    fn params(&self) -> impl Iterator<Item = LocalId> + '_ {
        (1..=self.num_params).map(LocalId::new)
    }

    fn return_place(&self) -> LocalId {
        LocalId::new(0)
    }
}

// ============================================================================
// Escape Analyzer for Benchmarking
// ============================================================================

/// Simplified escape analyzer for benchmarking.
struct EscapeAnalyzer {
    states: HashMap<LocalId, EscapeState>,
    effect_captured: HashSet<LocalId>,
    closure_captures: HashMap<LocalId, Vec<LocalId>>,
    captured_by_closure: HashSet<LocalId>,
}

/// Results of escape analysis.
struct EscapeResults {
    states: HashMap<LocalId, EscapeState>,
    effect_captured: HashSet<LocalId>,
    stack_promotable: HashSet<LocalId>,
    closure_captures: HashMap<LocalId, Vec<LocalId>>,
    captured_by_closure: HashSet<LocalId>,
}

impl EscapeResults {
    fn stack_promotion_rate(&self) -> f64 {
        if self.states.is_empty() {
            return 0.0;
        }
        self.stack_promotable.len() as f64 / self.states.len() as f64
    }

    fn effect_capture_rate(&self) -> f64 {
        if self.states.is_empty() {
            return 0.0;
        }
        self.effect_captured.len() as f64 / self.states.len() as f64
    }

    fn closure_capture_rate(&self) -> f64 {
        if self.states.is_empty() {
            return 0.0;
        }
        self.captured_by_closure.len() as f64 / self.states.len() as f64
    }
}

impl EscapeAnalyzer {
    fn new() -> Self {
        Self {
            states: HashMap::new(),
            effect_captured: HashSet::new(),
            closure_captures: HashMap::new(),
            captured_by_closure: HashSet::new(),
        }
    }

    fn analyze(&mut self, body: &TestMirBody) -> EscapeResults {
        self.states.clear();
        self.effect_captured.clear();
        self.closure_captures.clear();
        self.captured_by_closure.clear();

        // Initialize all locals to NoEscape
        for local in body.locals() {
            self.states.insert(local, EscapeState::NoEscape);
        }

        // Return place always escapes
        self.states.insert(body.return_place(), EscapeState::ArgEscape);

        // Parameters may escape
        for param in body.params() {
            self.states.insert(param, EscapeState::ArgEscape);
        }

        // First pass: collect closure captures
        for stmt in &body.statements {
            if let StatementKind::Closure { dest, captures } = stmt {
                self.closure_captures.insert(*dest, captures.clone());
                for &cap in captures {
                    self.captured_by_closure.insert(cap);
                }
            }
        }

        // Iterate to fixed point
        loop {
            let mut changed = false;

            for stmt in &body.statements {
                changed |= self.analyze_statement(stmt);
            }

            // Propagate escape to closure captures
            let updates: Vec<_> = self.closure_captures.iter()
                .filter_map(|(closure, captures)| {
                    let state = self.states.get(closure).copied()
                        .unwrap_or(EscapeState::NoEscape);
                    if state != EscapeState::NoEscape {
                        Some((captures.clone(), state))
                    } else {
                        None
                    }
                })
                .collect();

            for (captures, state) in updates {
                for cap in captures {
                    changed |= self.update_state(cap, state);
                }
            }

            if !changed {
                break;
            }
        }

        // Determine stack-promotable allocations
        let mut stack_promotable = HashSet::new();
        for (local, state) in &self.states {
            let can_stack = state.can_stack_allocate()
                && !self.effect_captured.contains(local)
                && !self.is_captured_by_escaping_closure(*local);
            if can_stack {
                stack_promotable.insert(*local);
            }
        }

        EscapeResults {
            states: self.states.clone(),
            effect_captured: self.effect_captured.clone(),
            stack_promotable,
            closure_captures: self.closure_captures.clone(),
            captured_by_closure: self.captured_by_closure.clone(),
        }
    }

    fn analyze_statement(&mut self, stmt: &StatementKind) -> bool {
        match stmt {
            StatementKind::Assign { dest, src } => {
                let src_state = self.states.get(src).copied().unwrap_or(EscapeState::NoEscape);
                self.update_state(*dest, src_state)
            }
            StatementKind::FieldAssign { dest, src } => {
                // Value escapes to a field
                let dest_state = self.states.get(dest).copied().unwrap_or(EscapeState::NoEscape);
                self.update_state(*src, dest_state)
            }
            StatementKind::RefOf { dest, src } => {
                // Taking a reference: if dest escapes, src escapes
                let dest_state = self.states.get(dest).copied().unwrap_or(EscapeState::NoEscape);
                self.update_state(*src, dest_state)
            }
            StatementKind::Call { dest: _, args } => {
                // Arguments may escape via call
                let mut changed = false;
                for &arg in args {
                    changed |= self.update_state(arg, EscapeState::ArgEscape);
                }
                changed
            }
            StatementKind::Return(local) => {
                self.update_state(*local, EscapeState::ArgEscape)
            }
            StatementKind::StoreGlobal { src } => {
                self.update_state(*src, EscapeState::GlobalEscape)
            }
            StatementKind::EffectOp { args } => {
                // Effect operations capture values
                for &arg in args {
                    self.effect_captured.insert(arg);
                }
                false
            }
            StatementKind::Closure { .. } => {
                // Closure captures handled in first pass
                false
            }
            StatementKind::Nop => false,
        }
    }

    fn update_state(&mut self, local: LocalId, new_state: EscapeState) -> bool {
        let current = self.states.get(&local).copied().unwrap_or(EscapeState::NoEscape);
        let joined = current.join(new_state);
        if joined != current {
            self.states.insert(local, joined);
            true
        } else {
            false
        }
    }

    fn is_captured_by_escaping_closure(&self, local: LocalId) -> bool {
        if !self.captured_by_closure.contains(&local) {
            return false;
        }
        for (closure, captures) in &self.closure_captures {
            if captures.contains(&local) {
                let closure_state = self.states.get(closure).copied()
                    .unwrap_or(EscapeState::NoEscape);
                if closure_state != EscapeState::NoEscape {
                    return true;
                }
            }
        }
        false
    }
}

// ============================================================================
// Test Program Generators
// ============================================================================

/// Generate a simple function with local computations (high stack promotion).
fn generate_local_computation(num_locals: u32) -> TestMirBody {
    let mut body = TestMirBody::new(num_locals + 1, 0);

    // Local computations: x = y + z pattern (no escapes)
    for i in 1..num_locals {
        body.add_statement(StatementKind::Assign {
            dest: LocalId::new(i + 1),
            src: LocalId::new(i),
        });
    }

    body
}

/// Generate a function with call-heavy pattern (lower stack promotion).
fn generate_call_heavy(num_locals: u32, num_calls: u32) -> TestMirBody {
    let mut body = TestMirBody::new(num_locals + 1, 2);

    // Create some local values
    for i in 3..num_locals {
        body.add_statement(StatementKind::Assign {
            dest: LocalId::new(i),
            src: LocalId::new(i - 1),
        });
    }

    // Make calls that cause escape
    for i in 0..num_calls {
        let arg_idx = 3 + (i % (num_locals.saturating_sub(3).max(1)));
        body.add_statement(StatementKind::Call {
            dest: LocalId::new(0),
            args: vec![LocalId::new(arg_idx)],
        });
    }

    body
}

/// Generate a function with effect operations (effect captures).
fn generate_effect_heavy(num_locals: u32, num_effects: u32) -> TestMirBody {
    let mut body = TestMirBody::new(num_locals + 1, 1);

    // Create some local values
    for i in 2..num_locals {
        body.add_statement(StatementKind::Assign {
            dest: LocalId::new(i),
            src: LocalId::new(i - 1),
        });
    }

    // Effect operations that capture values
    for i in 0..num_effects {
        let arg_idx = 2 + (i % (num_locals.saturating_sub(2).max(1)));
        body.add_statement(StatementKind::EffectOp {
            args: vec![LocalId::new(arg_idx)],
        });
    }

    body
}

/// Generate a function with closures (closure captures).
fn generate_closure_heavy(num_locals: u32, num_closures: u32) -> TestMirBody {
    let mut body = TestMirBody::new(num_locals + num_closures + 1, 1);

    // Create local values
    for i in 2..(num_locals + 2) {
        body.add_statement(StatementKind::Assign {
            dest: LocalId::new(i),
            src: LocalId::new(1),
        });
    }

    // Create closures that capture values
    for i in 0..num_closures {
        let closure_local = LocalId::new(num_locals + 2 + i);
        let captures: Vec<_> = (0..3.min(num_locals))
            .map(|j| LocalId::new(2 + ((i + j) % num_locals.max(1))))
            .collect();
        body.add_statement(StatementKind::Closure {
            dest: closure_local,
            captures,
        });

        // Some closures escape via calls
        if i % 3 == 0 {
            body.add_statement(StatementKind::Call {
                dest: LocalId::new(0),
                args: vec![closure_local],
            });
        }
    }

    body
}

/// Generate a mixed workload (realistic function).
fn generate_mixed_workload(num_locals: u32) -> TestMirBody {
    let mut body = TestMirBody::new(num_locals + 5, 2);

    // 60% local computations
    let local_count = (num_locals * 60) / 100;
    for i in 3..(3 + local_count) {
        body.add_statement(StatementKind::Assign {
            dest: LocalId::new(i),
            src: LocalId::new(i - 1),
        });
    }

    // 20% call escapes
    let call_count = (num_locals * 20) / 100;
    for i in 0..call_count {
        let arg_idx = 3 + (i % local_count.max(1));
        body.add_statement(StatementKind::Call {
            dest: LocalId::new(0),
            args: vec![LocalId::new(arg_idx)],
        });
    }

    // 10% effect captures
    let effect_count = (num_locals * 10) / 100;
    for i in 0..effect_count {
        let arg_idx = 3 + local_count + i;
        if arg_idx < num_locals + 3 {
            body.add_statement(StatementKind::EffectOp {
                args: vec![LocalId::new(arg_idx)],
            });
        }
    }

    // 10% closures
    let closure_count = (num_locals * 10) / 100;
    for i in 0..closure_count {
        let closure_local = LocalId::new(num_locals + 3 + i);
        let captures = vec![LocalId::new(3 + (i % local_count.max(1)))];
        body.add_statement(StatementKind::Closure {
            dest: closure_local,
            captures,
        });
    }

    body
}

// ============================================================================
// Benchmarks
// ============================================================================

fn bench_escape_analysis_speed(c: &mut Criterion) {
    let mut group = c.benchmark_group("escape_analysis_speed");

    for size in [10, 50, 100, 500, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("local_computation", size), size, |b, &size| {
            let body = generate_local_computation(size);
            b.iter(|| {
                let mut analyzer = EscapeAnalyzer::new();
                black_box(analyzer.analyze(&body))
            });
        });

        group.bench_with_input(BenchmarkId::new("call_heavy", size), size, |b, &size| {
            let body = generate_call_heavy(size, size / 5);
            b.iter(|| {
                let mut analyzer = EscapeAnalyzer::new();
                black_box(analyzer.analyze(&body))
            });
        });

        group.bench_with_input(BenchmarkId::new("effect_heavy", size), size, |b, &size| {
            let body = generate_effect_heavy(size, size / 5);
            b.iter(|| {
                let mut analyzer = EscapeAnalyzer::new();
                black_box(analyzer.analyze(&body))
            });
        });

        group.bench_with_input(BenchmarkId::new("mixed_workload", size), size, |b, &size| {
            let body = generate_mixed_workload(size);
            b.iter(|| {
                let mut analyzer = EscapeAnalyzer::new();
                black_box(analyzer.analyze(&body))
            });
        });
    }

    group.finish();
}

fn bench_stack_promotion_effectiveness(c: &mut Criterion) {
    let mut group = c.benchmark_group("stack_promotion_effectiveness");

    // Measure actual promotion rates for different program patterns
    for size in [100, 500, 1000].iter() {
        group.bench_with_input(BenchmarkId::new("local_computation", size), size, |b, &size| {
            let body = generate_local_computation(size);
            let mut analyzer = EscapeAnalyzer::new();
            b.iter(|| {
                let results = analyzer.analyze(&body);
                let rate = results.stack_promotion_rate();
                black_box(rate)
            });
        });

        group.bench_with_input(BenchmarkId::new("call_heavy", size), size, |b, &size| {
            let body = generate_call_heavy(size, size / 5);
            let mut analyzer = EscapeAnalyzer::new();
            b.iter(|| {
                let results = analyzer.analyze(&body);
                let rate = results.stack_promotion_rate();
                black_box(rate)
            });
        });

        group.bench_with_input(BenchmarkId::new("mixed_workload", size), size, |b, &size| {
            let body = generate_mixed_workload(size);
            let mut analyzer = EscapeAnalyzer::new();
            b.iter(|| {
                let results = analyzer.analyze(&body);
                let rate = results.stack_promotion_rate();
                black_box(rate)
            });
        });
    }

    group.finish();
}

/// Measure the cost savings from stack promotion.
///
/// This benchmark compares the cost of:
/// 1. Always using heap allocation with generation checks
/// 2. Using stack allocation when escape analysis permits
fn bench_allocation_cost_savings(c: &mut Criterion) {
    let mut group = c.benchmark_group("allocation_cost_savings");

    // Simulate heap allocation cost (allocation + gen check on use)
    const HEAP_ALLOC_CYCLES: u64 = 150;  // Approximate cycles for heap alloc
    const GEN_CHECK_CYCLES: u64 = 4;     // Generation check cost
    const STACK_ALLOC_CYCLES: u64 = 1;   // Stack alloc is essentially free
    const DEREF_COUNT: u64 = 10;         // Average dereferences per value

    fn heap_cost_per_value() -> u64 {
        HEAP_ALLOC_CYCLES + (GEN_CHECK_CYCLES * DEREF_COUNT)
    }

    fn stack_cost_per_value() -> u64 {
        STACK_ALLOC_CYCLES + 0 // No gen checks for stack
    }

    for size in [100, 500, 1000].iter() {
        // Local computation pattern (high promotion rate)
        group.bench_with_input(BenchmarkId::new("savings_local_comp", size), size, |b, &size| {
            let body = generate_local_computation(size);
            let mut analyzer = EscapeAnalyzer::new();
            let results = analyzer.analyze(&body);
            let promotable = results.stack_promotable.len() as u64;
            let non_promotable = (results.states.len() as u64).saturating_sub(promotable);

            b.iter(|| {
                // Cost without escape analysis (all heap)
                let baseline_cost = size as u64 * heap_cost_per_value();

                // Cost with escape analysis
                let optimized_cost = (promotable * stack_cost_per_value())
                    + (non_promotable * heap_cost_per_value());

                let savings = baseline_cost.saturating_sub(optimized_cost);
                black_box((baseline_cost, optimized_cost, savings))
            });
        });

        // Mixed workload pattern
        group.bench_with_input(BenchmarkId::new("savings_mixed", size), size, |b, &size| {
            let body = generate_mixed_workload(size);
            let mut analyzer = EscapeAnalyzer::new();
            let results = analyzer.analyze(&body);
            let promotable = results.stack_promotable.len() as u64;
            let non_promotable = (results.states.len() as u64).saturating_sub(promotable);

            b.iter(|| {
                let baseline_cost = size as u64 * heap_cost_per_value();
                let optimized_cost = (promotable * stack_cost_per_value())
                    + (non_promotable * heap_cost_per_value());
                let savings = baseline_cost.saturating_sub(optimized_cost);
                black_box((baseline_cost, optimized_cost, savings))
            });
        });
    }

    group.finish();
}

/// Print detailed escape analysis statistics.
fn bench_escape_statistics(c: &mut Criterion) {
    let mut group = c.benchmark_group("escape_statistics");

    let patterns = [
        ("local_computation", generate_local_computation(100)),
        ("call_heavy", generate_call_heavy(100, 20)),
        ("effect_heavy", generate_effect_heavy(100, 20)),
        ("closure_heavy", generate_closure_heavy(100, 20)),
        ("mixed_workload", generate_mixed_workload(100)),
    ];

    for (name, body) in patterns.iter() {
        group.bench_function(BenchmarkId::new("analyze", name), |b| {
            b.iter(|| {
                let mut analyzer = EscapeAnalyzer::new();
                let results = analyzer.analyze(body);

                // Collect statistics
                let total = results.states.len();
                let stack_promotable = results.stack_promotable.len();
                let effect_captured = results.effect_captured.len();
                let closure_captured = results.captured_by_closure.len();

                let no_escape = results.states.values()
                    .filter(|&&s| s == EscapeState::NoEscape)
                    .count();
                let arg_escape = results.states.values()
                    .filter(|&&s| s == EscapeState::ArgEscape)
                    .count();
                let global_escape = results.states.values()
                    .filter(|&&s| s == EscapeState::GlobalEscape)
                    .count();

                black_box((
                    total, stack_promotable, effect_captured, closure_captured,
                    no_escape, arg_escape, global_escape
                ))
            });
        });
    }

    group.finish();
}

/// Benchmark fixed-point iteration convergence.
fn bench_fixpoint_convergence(c: &mut Criterion) {
    let mut group = c.benchmark_group("fixpoint_convergence");

    // Measure iterations needed for different patterns
    for size in [50, 100, 500].iter() {
        group.bench_with_input(BenchmarkId::new("closure_chains", size), size, |b, &size| {
            // Create a chain of closures where escape propagates
            let mut body = TestMirBody::new(size * 2, 1);

            // Create closure chain
            for i in 0..size {
                let closure = LocalId::new(size + i);
                let capture = LocalId::new(i.max(1));
                body.add_statement(StatementKind::Closure {
                    dest: closure,
                    captures: vec![capture],
                });

                // Later closures capture earlier ones
                if i > 0 {
                    body.add_statement(StatementKind::Closure {
                        dest: LocalId::new(size + i),
                        captures: vec![LocalId::new(size + i - 1)],
                    });
                }
            }

            // Make the last closure escape
            body.add_statement(StatementKind::Call {
                dest: LocalId::new(0),
                args: vec![LocalId::new(size * 2 - 1)],
            });

            b.iter(|| {
                let mut analyzer = EscapeAnalyzer::new();
                black_box(analyzer.analyze(&body))
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_escape_analysis_speed,
    bench_stack_promotion_effectiveness,
    bench_allocation_cost_savings,
    bench_escape_statistics,
    bench_fixpoint_convergence,
);
criterion_main!(benches);
