# Blood

**A systems programming language for environments where failure is not an option.**

Blood synthesizes five cutting-edge programming language innovations:

- **Content-Addressed Code** (Unison) — Code identity via BLAKE3-256 hashes
- **Generational Memory Safety** (Vale) — 128-bit fat pointers, no GC
- **Mutable Value Semantics** (Hylo) — Simple ownership without borrow checker complexity
- **Algebraic Effects** (Koka) — All side effects typed and composable
- **Multiple Dispatch** (Julia) — Type-stable open extensibility

## Status

> **Stability Level: Research Prototype (Alpha)**
>
> Blood is suitable for language research, learning, and contributing to development. Not yet suitable for production use.

**Early implementation phase.** Core compiler functionality is working (lexer, parser, type checker, LLVM codegen). Simple programs like FizzBuzz compile and run.

| Component | Status | Details |
|-----------|--------|---------|
| Lexer & Parser | ✅ Complete | Production-tested |
| Type Checker | ✅ Complete | Bidirectional + unification |
| Code Generation | ✅ Complete | LLVM backend |
| Effects System | ✅ Integrated | Evidence passing with runtime FFI exports |
| Memory Model | ✅ Integrated | Generational pointers in codegen (blood_alloc/blood_free) |
| Runtime | ✅ Integrated | Scheduler FFI exports linked to programs |
| Multiple Dispatch | ✅ Integrated | Runtime dispatch table with type tags |
| Closures | ✅ Integrated | Environment capture and codegen |

**Legend**: ✅ = Implemented, 🔶 = Scaffolded (code exists, not integrated)

**[Getting Started](GETTING_STARTED.md)** | [Specification](SPECIFICATION.md) | [Implementation Status](IMPLEMENTATION_STATUS.md)

## The Name

In engineering, regulations "written in blood" are those born from catastrophic failures — rules that exist because someone died or systems failed in ways that can never be allowed again.

Blood is for avionics, medical devices, financial infrastructure, autonomous vehicles, nuclear control systems. Systems where failure is not an option.

## Design Principles

1. **No Hidden Costs** — Every abstraction has predictable, visible cost
2. **Failure is Data** — All errors tracked in the type system via effects
3. **Zero-Cost When Provable** — Compile-time proofs eliminate runtime checks
4. **Effects are Universal** — IO, state, exceptions, async — one unified mechanism
5. **Interop is First-Class** — C FFI designed from day one

## Quick Example

```blood
effect Error<E> {
    op raise(err: E) -> never
}

effect IO {
    op read_file(path: Path) -> Bytes
}

fn load_config(path: Path) -> Config / {IO, Error<ParseError>} {
    let data = read_file(path)
    parse_config(data)
}

fn main() / {IO, Error<AppError>} {
    let config = with ParseErrorHandler handle {
        load_config("config.toml")
    }
    run_app(config)
}
```

## Quick Start

```bash
# Build the compiler
cargo build --release

# Compile and run a program
cargo run -- run examples/fizzbuzz.blood
```

See **[GETTING_STARTED.md](GETTING_STARTED.md)** for the full tutorial.

## Documentation

### Core Specifications

| Document | Description |
|----------|-------------|
| [SPECIFICATION.md](./SPECIFICATION.md) | Core language specification |
| [MEMORY_MODEL.md](./MEMORY_MODEL.md) | Synthetic Safety Model (generational references) |
| [DISPATCH.md](./DISPATCH.md) | Multiple dispatch and type stability |
| [GRAMMAR.md](./GRAMMAR.md) | Complete surface syntax grammar |
| [FORMAL_SEMANTICS.md](./FORMAL_SEMANTICS.md) | Operational semantics and type rules |

### System Specifications

| Document | Description |
|----------|-------------|
| [CONTENT_ADDRESSED.md](./CONTENT_ADDRESSED.md) | Content-addressed storage and VFT |
| [CONCURRENCY.md](./CONCURRENCY.md) | Fiber model and scheduler |
| [FFI.md](./FFI.md) | Foreign function interface |
| [STDLIB.md](./STDLIB.md) | Standard library design |
| [DIAGNOSTICS.md](./DIAGNOSTICS.md) | Error messages and diagnostics |
| [UCM.md](./UCM.md) | Codebase Manager (tooling) |

### Planning & Status

| Document | Description |
|----------|-------------|
| [GETTING_STARTED.md](./GETTING_STARTED.md) | Tutorial and quick start guide |
| [ROADMAP.md](./ROADMAP.md) | Implementation plan and milestones |
| [DECISIONS.md](./DECISIONS.md) | Architecture decision records |
| [IMPLEMENTATION_STATUS.md](./IMPLEMENTATION_STATUS.md) | Detailed implementation audit |

## License

MIT License

## Contributing

We welcome contributions! See the [implementation status](IMPLEMENTATION_STATUS.md) for areas that need work.

- **Bug reports**: Open an issue with reproduction steps
- **Feature requests**: Open a discussion first
- **Code contributions**: Fork, branch, and submit a PR
