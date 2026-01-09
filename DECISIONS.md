# Blood Architecture Decision Records

This document captures key architectural decisions made during the design of Blood and their rationale.

### Related Specifications

- [SPECIFICATION.md](./SPECIFICATION.md) — Core language specification
- [MEMORY_MODEL.md](./MEMORY_MODEL.md) — ADR-001, ADR-004, ADR-008, ADR-013, ADR-014 details
- [DISPATCH.md](./DISPATCH.md) — ADR-005 details
- [CONTENT_ADDRESSED.md](./CONTENT_ADDRESSED.md) — ADR-003, ADR-012 details
- [FORMAL_SEMANTICS.md](./FORMAL_SEMANTICS.md) — ADR-002, ADR-006, ADR-007, ADR-011 details
- [ROADMAP.md](./ROADMAP.md) — Implementation timeline

---

## ADR-001: Use Generational References Instead of Borrow Checking

**Status**: Accepted

**Context**: Blood needs memory safety without garbage collection. The two main approaches are:
1. Borrow checking (Rust) — compile-time ownership tracking
2. Generational references (Vale) — runtime generation tag checking

**Decision**: Blood uses generational references with 128-bit fat pointers.

**Rationale**:
- Borrow checking has a steep learning curve and adversarial feel
- Generational references are simpler to understand and use
- Runtime overhead is minimal (~1-2 cycles per dereference, theoretical—see MEMORY_MODEL.md §1.1)
- Escape analysis can eliminate checks for provably-safe references
- Mutable value semantics further reduce the need for references

**Consequences**:
- Slightly larger pointer size (128-bit vs 64-bit)
- Small runtime overhead for non-optimized paths
- Simpler mental model for developers
- Easier to achieve memory safety correctness

---

## ADR-002: Algebraic Effects for All Side Effects

**Status**: Accepted

**Context**: Languages handle side effects in various ways:
- Untracked (C, Go)
- Monads (Haskell)
- Keywords (async/await)
- Algebraic effects (Koka)

**Decision**: Blood uses algebraic effects as the universal effect mechanism.

**Rationale**:
- Unifies IO, state, exceptions, async, non-determinism
- Effects are explicit in function signatures
- Handlers enable dependency injection and testing
- Composable without "wrapper hell"
- Resumable exceptions enable powerful control flow

**Consequences**:
- All side effects visible in types
- Some learning curve for effect handlers
- Enables mock handlers for testing
- Requires careful design of standard effect library

---

## ADR-003: Content-Addressed Code via BLAKE3-256

**Status**: Accepted

**Context**: Traditional languages use file paths and symbol names for code identity. Unison pioneered content-addressed code using hashes.

**Decision**: Blood identifies all definitions by BLAKE3-256 hash of canonicalized AST.

**Rationale**:
- Eliminates dependency hell (multiple versions coexist by hash)
- Enables perfect incremental compilation
- Makes refactoring safe (renames don't change identity)
- Enables zero-downtime hot-swapping
- BLAKE3 provides sufficient collision resistance with high performance

**Consequences**:
- Requires new tooling paradigm (codebase manager vs files)
- FFI requires bridge dialect for C symbol mapping
- Learning curve for content-addressed workflow
- Perfect reproducibility and caching

---

## ADR-004: Generation Snapshots for Effect Safety

**Status**: Accepted

**Context**: When algebraic effects suspend computation, captured continuations may hold generational references that become stale before resume.

**Decision**: Blood captures a "generation snapshot" with each continuation and validates on resume.

**Rationale**:
- No existing language addresses this interaction
- Stale references could cause use-after-free on resume
- Validation cost is proportional to captured references
- Lazy validation amortizes cost to actual dereferences
- StaleReference effect enables graceful recovery

**Consequences**:
- Novel contribution (no prior art)
- Small overhead on continuation capture
- Validation on resume adds safety guarantee
- Handlers can choose panic or graceful degradation

---

## ADR-005: Multiple Dispatch with Type Stability Enforcement

**Status**: Accepted

**Context**: Julia demonstrates multiple dispatch can enable high performance, but type instability causes performance cliffs.

**Decision**: Blood uses multiple dispatch with compile-time type stability checking.

**Rationale**:
- Solves the Expression Problem (add types and operations independently)
- Enables retroactive protocol conformance
- Type stability ensures predictable performance
- Compiler warnings prevent performance cliffs

**Consequences**:
- More flexible than single dispatch
- Requires clear dispatch resolution rules
- Ambiguity is a compile error
- Type-unstable code rejected

---

## ADR-006: Linear Types for Resource Management

**Status**: Accepted

**Context**: Some resources (file handles, network connections) must be used exactly once and cannot be forgotten.

**Decision**: Blood supports linear types (must use exactly once) and affine types (at most once).

**Rationale**:
- Prevents resource leaks at compile time
- Ensures cleanup code always runs
- Interacts with effect system (linear values can't cross multi-shot resume)
- More precise than Rust's affine-only approach

**Consequences**:
- Additional type annotations for resources
- Compiler enforces use-exactly-once
- Multi-shot handlers cannot capture linear values
- Strong resource safety guarantees

---

## ADR-007: Deep and Shallow Handlers

**Status**: Accepted

**Context**: Effect handlers can be "deep" (persistent) or "shallow" (one-shot). Different use cases benefit from each.

**Decision**: Blood supports both, with deep as default.

**Rationale**:
- Deep handlers handle all operations in a computation (most common)
- Shallow handlers handle one operation then disappear (generators, streams)
- Explicit choice prevents confusion about handler semantics
- Both are needed for full expressiveness

**Consequences**:
- Handler kind must be specified (or defaulted to deep)
- Different operational semantics for each
- Enables both state-like and stream-like patterns

---

## ADR-008: Tiered Memory Model

**Status**: Accepted

**Context**: Different allocations have different lifecycles and safety requirements.

**Decision**: Blood uses three memory tiers:
1. Stack (lexical, zero cost)
2. Region (scoped, generational checks)
3. Persistent (global, reference counted)

**Rationale**:
- Stack allocation is fastest
- Most allocations can be proven to be stack-safe
- Generational checks for heap allocations
- Reference counting fallback for long-lived objects
- Escape analysis promotes to optimal tier

**Consequences**:
- Compiler complexity for tier selection
- Most code gets zero-cost safety
- Performance predictable by tier
- Generation overflow handled by tier promotion

---

## ADR-009: Row Polymorphism for Records and Effects

**Status**: Accepted

**Context**: Structural typing and effect polymorphism both benefit from row variables.

**Decision**: Blood uses row polymorphism for both record types and effect rows.

**Rationale**:
- Functions can accept any record with required fields
- Functions can be generic over additional effects
- Enables "extensible records" pattern
- Unified approach for data and effects

**Consequences**:
- More flexible than nominal typing
- Slightly more complex type inference
- Enables powerful generic programming
- Well-established theory (Rémy's rows, Koka's effects)

---

## ADR-010: Hierarchy of Concerns

**Status**: Accepted

**Context**: Design decisions sometimes conflict (e.g., safety vs ergonomics). A priority ordering is needed.

**Decision**: Blood prioritizes: Correctness > Safety > Predictability > Performance > Ergonomics

**Rationale**:
- Incorrect code is worthless regardless of speed
- Memory safety is non-negotiable for target domains
- Developers must understand performance characteristics
- Performance matters after correctness/safety
- Ergonomics is last but not unimportant

**Consequences**:
- Sometimes verbose syntax when safety requires it
- No "escape hatches" that compromise safety
- Poor ergonomics indicates design problem
- Clear decision framework for tradeoffs

---

## ADR-011: Five Innovation Composition

**Status**: Accepted

**Context**: Blood combines five specific innovations from different research languages:
1. Content-addressed code (Unison)
2. Generational references (Vale)
3. Mutable value semantics (Hylo)
4. Algebraic effects (Koka)
5. Multiple dispatch (Julia)

This combination is unprecedented and required formal analysis of interaction safety.

**Decision**: Blood adopts all five innovations with formal composition safety proofs.

**Rationale**:
- Each innovation solves real problems independently
- Composition benefits exceed sum of parts (synergies documented in FORMAL_SEMANTICS.md §10)
- Formal analysis proves innovations compose safely (no emergent unsoundness)
- Addresses gaps in existing languages (safety-performance tradeoff, expression problem, effect management)

**Consequences**:
- Unprecedented language design requiring novel research
- Complexity in implementation and tooling
- Rich feature set enabling new programming patterns
- Formal proofs provide confidence in soundness (see FORMAL_SEMANTICS.md §10)

**Novel Contribution**: The composition and its formal analysis constitute Blood's primary research contribution.

---

## ADR-012: VFT Hot-Swap with Effect Coordination

**Status**: Accepted

**Context**: Content-addressed code enables hot-swapping by redirecting hash references. However, in-flight operations (active function calls, suspended effect handlers) complicate safe replacement.

**Decision**: Blood supports three swap strategies with effect handler coordination:
1. **Immediate** — New version takes effect at next call (may mix versions)
2. **Barrier** — Wait for quiescent point before swap
3. **Epoch** — Requests entering after swap use new version; in-flight complete with old

**Rationale**:
- Different applications need different consistency guarantees
- Effect handlers can span VFT boundaries (suspended continuations)
- Version mixing is sometimes acceptable (stateless functions)
- Full consistency sometimes required (stateful operations)
- See CONTENT_ADDRESSED.md §8.5 for full specification

**Consequences**:
- Runtime must track version epochs per handler
- Rollback possible if new version fails validation
- Observability metrics for swap progress
- Clear semantics for each consistency level

**Novel Contribution**: Integrating hot-swap with algebraic effect handlers is novel to Blood.

---

## ADR-013: Effect-Aware Escape Analysis

**Status**: Accepted

**Context**: Traditional escape analysis determines whether values can be stack-allocated based on whether references outlive their scope. Algebraic effects add complexity: effect suspension points can capture references in continuations.

**Decision**: Blood extends escape analysis with effect boundary tracking:
- Values that may be captured in continuations at effect suspension points are classified differently
- Deep handlers preserve captured references across multiple resumes
- Shallow handlers consume values (single resume)
- Multi-shot handlers require special handling (values may be used multiple times)

**Rationale**:
- Effect suspension creates implicit reference capture (in continuation)
- Captured references must survive to resume point
- Optimization requires understanding effect handler semantics
- Shallow handlers enable optimizations impossible with deep handlers
- See MEMORY_MODEL.md §5.8 for full specification

**Consequences**:
- More conservative stack promotion near effect boundaries
- Optimization based on handler kind (deep vs shallow)
- Multi-shot handlers require stricter escape classification
- Effect inference provides information for escape analysis

**Novel Contribution**: This interaction between escape analysis and algebraic effects is novel to Blood.

---

## ADR-014: Hybrid Mutable Value Semantics

**Status**: Accepted

**Context**: Hylo demonstrates pure mutable value semantics (MVS) can eliminate many reference-related bugs. However, some patterns genuinely require references (graph structures, shared state).

**Decision**: Blood uses a hybrid model:
- Default to value semantics (like Hylo)
- Explicit borrowing syntax (`&T`, `&mut T`) when references are genuinely needed
- Clear distinction between value operations and reference operations

**Rationale**:
- Pure MVS is too restrictive for systems programming
- Explicit references make aliasing visible
- Value semantics simplify reasoning for most code
- Hybrid approach provides best of both worlds
- See MEMORY_MODEL.md §1.3 for clarification

**Consequences**:
- Most code uses simple value semantics
- Reference patterns require explicit annotation
- Clear mental model: values copy, references alias
- Gradual adoption path from reference-heavy code

---

## Decision Status Legend

- **Proposed**: Under discussion
- **Accepted**: Decision made and documented
- **Deprecated**: No longer valid
- **Superseded**: Replaced by another decision

---

*Last updated: 2026-01-09*
