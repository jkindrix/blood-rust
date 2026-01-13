# Blood Compiler: Action Items Checklist

**Generated**: 2026-01-13
**Source**: Comprehensive codebase analysis and review
**Status**: Active tracking document

---

## Priority Legend

| Priority | Meaning | Timeline |
|----------|---------|----------|
| **P0** | Critical - Blocks fundamental use cases | Immediate |
| **P1** | High - Required for beta readiness | Near-term |
| **P2** | Medium - Required for 1.0 release | Mid-term |
| **P3** | Low - Quality of life improvements | Long-term |

---

## 1. Missing Features (Implementation Gaps)

### 1.1 Persistent Memory Tier [P0]

The reference-counting tier for long-lived objects is designed but not implemented.

- [ ] **IMPL-001**: Implement `PersistentPtr` allocation in `blood-runtime/src/memory.rs`
- [ ] **IMPL-002**: Implement deferred reference counting mechanism
- [ ] **IMPL-003**: Implement cycle detection/collection for persistent tier
- [ ] **IMPL-004**: Add tier promotion logic when generation reaches `OVERFLOW_GUARD`
- [ ] **IMPL-005**: Integrate persistent tier with MIR codegen (`codegen/mir_codegen/`)
- [ ] **IMPL-006**: Add tests for tier 2→3 promotion scenarios
- [ ] **IMPL-007**: Benchmark persistent tier overhead vs. generational checks

### 1.2 FFI Code Generation [P0]

Bridge blocks parse and runtime FFI exists, but codegen is incomplete.

- [ ] **FFI-001**: Complete `extern` block code generation in `codegen/`
- [ ] **FFI-002**: Implement calling convention handling (sysv64, win64)
- [ ] **FFI-003**: Implement type marshalling for FFI boundary (Blood types ↔ C types)
- [ ] **FFI-004**: Generate wrapper functions for safe FFI calls
- [ ] **FFI-005**: Implement `@unsafe` block code generation
- [ ] **FFI-006**: Add integration tests calling actual C libraries (libc, libm)
- [ ] **FFI-007**: Document FFI ABI compatibility guarantees

### 1.3 Closures Enhancement [P1]

Closures work but need optimization.

- [ ] **CLOS-001**: Implement closure environment size optimization
- [ ] **CLOS-002**: Add escape analysis for closure captures
- [ ] **CLOS-003**: Implement inline closure optimization for small closures
- [ ] **CLOS-004**: Add tests for closure capture of linear/affine values

---

## 2. Validation Gaps (Testing & Verification)

### 2.1 Integration Testing for Novel Features [P0]

Core code exists but novel feature interactions need end-to-end validation.

- [ ] **TEST-001**: Add E2E test: effects + generation snapshots (resume with stale reference)
- [ ] **TEST-002**: Add E2E test: linear values in multi-shot handler rejection
- [ ] **TEST-003**: Add E2E test: affine values in deep handler capture
- [ ] **TEST-004**: Add E2E test: nested region suspension with effects
- [ ] **TEST-005**: Add E2E test: generation overflow triggering tier promotion
- [ ] **TEST-006**: Add E2E test: content-addressed incremental rebuild
- [ ] **TEST-007**: Add E2E test: multiple dispatch with generic handlers
- [ ] **TEST-008**: Add E2E test: fiber scheduler with effect handlers
- [ ] **TEST-009**: Add stress test: rapid alloc/free cycles approaching `OVERFLOW_GUARD`

### 2.2 Real-World Validation [P1]

No substantial applications exist to validate the design.

- [ ] **REAL-001**: Implement a non-trivial example: JSON parser in Blood
- [ ] **REAL-002**: Implement a non-trivial example: HTTP client in Blood
- [ ] **REAL-003**: Implement a non-trivial example: concurrent web scraper
- [ ] **REAL-004**: Implement a non-trivial example: binary tree benchmark
- [ ] **REAL-005**: Port an existing benchmark suite (e.g., Computer Language Benchmarks Game subset)
- [ ] **REAL-006**: Profile real workloads to validate 128-bit pointer overhead claims
- [ ] **REAL-007**: Measure actual escape analysis effectiveness on real programs

### 2.3 Performance Validation [P1]

Some performance claims are theoretical, not measured.

- [ ] **PERF-001**: Benchmark generation check in compiled Blood code (claim: ~1-2 cycles)
- [ ] **PERF-002**: Benchmark effect handler overhead in real programs
- [ ] **PERF-003**: Benchmark 128-bit pointer overhead vs. 64-bit baseline
- [ ] **PERF-004**: Add memory pressure benchmarks for pointer-heavy data structures
- [ ] **PERF-005**: Benchmark escape analysis optimization effectiveness
- [ ] **PERF-006**: Compare Blood vs. Rust vs. C on equivalent programs
- [ ] **PERF-007**: Profile and optimize hot paths in compiled code

---

## 3. Code Quality Issues

### 3.1 Large File Modularization [P2]

Some files are too large for maintainability.

- [ ] **CODE-001**: Split `lexer.rs` (27KB) into submodules by token category
- [ ] **CODE-002**: Split `parser.rs` (26KB) into `parser/stmt.rs`, `parser/decl.rs`
- [ ] **CODE-003**: Review `typeck/context/mod.rs` (144 lines of struct fields) for decomposition
- [ ] **CODE-004**: Extract `typeck/dispatch/` complexity into smaller focused modules
- [ ] **CODE-005**: Document module boundaries and responsibilities

### 3.2 Code Duplication [P2]

Similar patterns exist in MIR and HIR lowering.

- [ ] **DUP-001**: Audit HIR→MIR lowering for duplicate patterns
- [ ] **DUP-002**: Extract common lowering utilities into shared module
- [ ] **DUP-003**: Unify error handling patterns across compiler phases
- [ ] **DUP-004**: Create shared visitor/walker infrastructure

### 3.3 Documentation Gaps [P3]

Some internal modules lack documentation.

- [ ] **DOC-001**: Add module-level docs to all `mod.rs` files
- [ ] **DOC-002**: Document internal compiler architecture (for contributors)
- [ ] **DOC-003**: Add architecture decision records for non-obvious choices
- [ ] **DOC-004**: Create contributor onboarding guide

---

## 4. Design Concerns

### 4.1 128-bit Pointer Overhead [P1]

Blood uses 128-bit pointers universally, unlike Vale's flexible approach.

- [ ] **PTR-001**: Profile memory usage on pointer-heavy data structures
- [ ] **PTR-002**: Investigate thin pointer optimization for known-safe cases
- [ ] **PTR-003**: Document when 128-bit overhead is acceptable vs. problematic
- [ ] **PTR-004**: Consider optional 64-bit mode for trusted code paths
- [ ] **PTR-005**: Add compiler warnings for pointer-heavy anti-patterns
- [ ] **PTR-006**: Benchmark linked list / tree traversal vs. 64-bit baseline

### 4.2 Effect System Complexity [P2]

Evidence passing adds compilation complexity.

- [ ] **EFF-001**: Audit evidence vector allocation for optimization opportunities
- [ ] **EFF-002**: Implement evidence vector caching for repeated handler patterns
- [ ] **EFF-003**: Add compile-time warnings for deep handler nesting
- [ ] **EFF-004**: Profile evidence lookup overhead in hot paths
- [ ] **EFF-005**: Document effect system performance characteristics for users

### 4.3 Generation Snapshot Overhead [P2]

Snapshot capture/validation has O(L) cost per reference.

- [ ] **SNAP-001**: Implement lazy validation optimization
- [ ] **SNAP-002**: Implement snapshot sharing for nested handlers
- [ ] **SNAP-003**: Profile snapshot overhead in effect-heavy programs
- [ ] **SNAP-004**: Add liveness filtering to reduce snapshot size
- [ ] **SNAP-005**: Document snapshot overhead characteristics

---

## 5. Ecosystem & Tooling Gaps

### 5.1 Self-Hosting [P1]

Compiler is written in Rust, not Blood.

- [ ] **SELF-001**: Identify minimal Blood subset needed for self-hosting
- [ ] **SELF-002**: Implement lexer in Blood (`blood-std/std/compiler/lexer.blood`)
- [ ] **SELF-003**: Implement parser in Blood
- [ ] **SELF-004**: Implement type checker in Blood
- [ ] **SELF-005**: Bootstrap: compile Blood compiler with Blood compiler

### 5.2 Standard Library [P1]

Standard library exists but is incomplete.

- [ ] **STD-001**: Complete `Vec<T>` implementation in Blood
- [ ] **STD-002**: Complete `HashMap<K,V>` implementation in Blood
- [ ] **STD-003**: Implement `String` type with UTF-8 handling
- [ ] **STD-004**: Implement file I/O wrappers using effects
- [ ] **STD-005**: Implement networking primitives
- [ ] **STD-006**: Add comprehensive standard library tests

### 5.3 Developer Tooling [P2]

Tooling exists but needs polish.

- [ ] **TOOL-001**: Complete LSP hover documentation with examples
- [ ] **TOOL-002**: Add LSP go-to-definition for effect operations
- [ ] **TOOL-003**: Add LSP completion for effect handlers
- [ ] **TOOL-004**: Implement blood-fmt auto-formatting
- [ ] **TOOL-005**: Add REPL for interactive exploration
- [ ] **TOOL-006**: Create VS Code extension package

### 5.4 Build System [P2]

- [ ] **BUILD-001**: Implement content-addressed build caching
- [ ] **BUILD-002**: Add incremental compilation using content hashes
- [ ] **BUILD-003**: Implement distributed build cache (HTTP-based)
- [ ] **BUILD-004**: Add dependency resolution for multi-file projects
- [ ] **BUILD-005**: Create package manager foundation

---

## 6. Safety & Correctness

### 6.1 Formal Verification [P3]

Proofs are informal/paper-style.

- [ ] **FORMAL-001**: Formalize type soundness proof in Coq/Agda
- [ ] **FORMAL-002**: Formalize effect safety theorem
- [ ] **FORMAL-003**: Formalize generation snapshot correctness
- [ ] **FORMAL-004**: Mechanically verify key safety invariants

### 6.2 Fuzzing & Property Testing [P2]

- [ ] **FUZZ-001**: Expand fuzzer coverage (`bloodc/fuzz/`)
- [ ] **FUZZ-002**: Add grammar-based fuzzing for parser
- [ ] **FUZZ-003**: Add property tests for type checker soundness
- [ ] **FUZZ-004**: Add property tests for MIR lowering correctness
- [ ] **FUZZ-005**: Add property tests for escape analysis

### 6.3 Error Handling Audit [P2]

Per CLAUDE.md, ensure no silent failures.

- [ ] **ERR-001**: Audit for `_ =>` catch-all patterns that should be explicit
- [ ] **ERR-002**: Audit for `unwrap_or_default()` hiding real errors
- [ ] **ERR-003**: Audit for silent `continue` in match arms
- [ ] **ERR-004**: Replace `Type::error()` placeholders with proper errors
- [ ] **ERR-005**: Ensure all TODO/FIXME comments are addressed or tracked

---

## 7. Documentation Improvements

### 7.1 Specification Clarifications [P3]

Minor spec clarifications identified.

- [ ] **SPEC-001**: Add integration status column to MEMORY_MODEL.md pointer layout
- [ ] **SPEC-002**: Add runtime linking requirements to CONCURRENCY.md
- [ ] **SPEC-003**: Clarify validated platforms in FFI.md
- [ ] **SPEC-004**: Sync README.md version with IMPLEMENTATION_STATUS.md (0.5.0 vs 0.5.2)

### 7.2 User Documentation [P2]

- [ ] **USERDOC-001**: Expand GETTING_STARTED.md with more examples
- [ ] **USERDOC-002**: Create effect system tutorial with common patterns
- [ ] **USERDOC-003**: Create memory model guide for users
- [ ] **USERDOC-004**: Document performance best practices
- [ ] **USERDOC-005**: Create migration guide from Rust patterns

---

## 8. Risk Mitigation

### 8.1 Single-Maintainer Risk [P1]

Project appears to have single maintainer.

- [ ] **RISK-001**: Document all non-obvious design decisions
- [ ] **RISK-002**: Create comprehensive contributor documentation
- [ ] **RISK-003**: Add inline comments explaining complex algorithms
- [ ] **RISK-004**: Establish code review process for contributions
- [ ] **RISK-005**: Create project governance documentation

### 8.2 Technical Debt [P2]

- [ ] **DEBT-001**: Address all `TODO` comments in codebase
- [ ] **DEBT-002**: Address all `FIXME` comments in codebase
- [ ] **DEBT-003**: Remove dead code identified by tooling
- [ ] **DEBT-004**: Update dependencies to latest stable versions
- [ ] **DEBT-005**: Run `cargo audit` and address vulnerabilities

---

## Summary Statistics

| Category | P0 | P1 | P2 | P3 | Total |
|----------|----|----|----|----|-------|
| Missing Features | 14 | 4 | 0 | 0 | **18** |
| Validation Gaps | 9 | 14 | 0 | 0 | **23** |
| Code Quality | 0 | 0 | 9 | 4 | **13** |
| Design Concerns | 0 | 6 | 10 | 0 | **16** |
| Ecosystem | 0 | 11 | 11 | 0 | **22** |
| Safety | 0 | 0 | 10 | 4 | **14** |
| Documentation | 0 | 0 | 5 | 4 | **9** |
| Risk Mitigation | 0 | 5 | 5 | 0 | **10** |
| **Total** | **23** | **40** | **50** | **12** | **125** |

---

## Recommended Execution Order

### Phase 1: Critical Path (P0 items)
1. Persistent memory tier (IMPL-001 through IMPL-007)
2. FFI code generation (FFI-001 through FFI-007)
3. Integration tests for novel features (TEST-001 through TEST-009)

### Phase 2: Beta Readiness (P1 items)
1. Real-world validation programs
2. Performance benchmarks
3. Self-hosting progress
4. Standard library completion
5. 128-bit pointer profiling

### Phase 3: 1.0 Release (P2 items)
1. Code quality improvements
2. Design optimizations
3. Developer tooling polish
4. Fuzzing and property testing

### Phase 4: Long-term (P3 items)
1. Formal verification
2. Documentation polish

---

*This document should be reviewed and updated as items are completed.*
