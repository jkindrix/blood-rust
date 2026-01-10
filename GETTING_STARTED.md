# Getting Started with Blood

A quick guide to writing and running your first Blood programs.

## Prerequisites

- **Rust**: Install via [rustup](https://rustup.rs/) (1.75+)
- **LLVM**: Version 14+ (`llvm-config --version`)
- **C compiler**: GCC or Clang for runtime linking

## Building the Compiler

```bash
# Clone the repository
git clone https://github.com/blood-lang/blood.git
cd blood

# Build in release mode
cargo build --release

# The compiler binary is at target/release/blood
```

## Your First Program

### Hello World

Create a file `hello.blood`:

```blood
fn main() {
    println_str("Hello, World!");
}
```

Compile and run:

```bash
# Compile to executable
cargo run -- build examples/hello.blood -o hello

# Run the program
./hello
# Output: Hello, World!
```

### FizzBuzz

A more complete example (`fizzbuzz.blood`):

```blood
fn main() {
    let mut i: i32 = 1;
    while i <= 15 {
        if i % 15 == 0 {
            println_str("FizzBuzz");
        } else if i % 3 == 0 {
            println_str("Fizz");
        } else if i % 5 == 0 {
            println_str("Buzz");
        } else {
            println_int(i);
        }
        i = i + 1;
    }
}
```

Compile and run:

```bash
cargo run -- build fizzbuzz.blood -o fizzbuzz
./fizzbuzz
```

Output:
```
1
2
Fizz
4
Buzz
Fizz
7
8
Fizz
Buzz
11
Fizz
13
14
FizzBuzz
```

## Command Reference

```bash
# Compile a Blood file
blood build <file.blood> [-o <output>]

# Compile and run immediately
blood run <file.blood>

# Show help
blood --help
```

## Language Basics

### Variables

```blood
// Immutable binding
let x: i32 = 42;

// Mutable binding
let mut y: i32 = 0;
y = y + 1;

// Type inference
let z = 100;  // inferred as i32
```

### Functions

```blood
fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn greet(name: &str) {
    print_str("Hello, ");
    println_str(name);
}
```

### Control Flow

```blood
// If-else
if condition {
    // ...
} else if other_condition {
    // ...
} else {
    // ...
}

// While loop
while i < 10 {
    i = i + 1;
}

// Loop with break
loop {
    if done {
        break;
    }
}
```

### Structs

```blood
struct Point {
    x: i32,
    y: i32,
}

fn main() {
    let p = Point { x: 10, y: 20 };
}
```

### Enums

```blood
enum Option<T> {
    Some(T),
    None,
}

enum Direction {
    North,
    South,
    East,
    West,
}
```

## Effects (Advanced)

Blood uses algebraic effects for I/O, state, and error handling:

```blood
// Effect declaration
effect State<T> {
    fn get() -> T;
    fn put(value: T);
}

// Function with effect
fn increment() / {State<i32>} {
    let x = perform State.get();
    perform State.put(x + 1);
}

// Handler
handle increment() with {
    State {
        get => resume(state),
        put(v) => { state = v; resume(()) },
    }
} where state = 0;
```

## Next Steps

- Read the [Language Specification](SPECIFICATION.md)
- Explore [Example Programs](examples/)
- Learn about [Effects](SPECIFICATION.md#4-effect-system)
- Understand the [Memory Model](MEMORY_MODEL.md)

## Troubleshooting

### LLVM Not Found

```bash
# Ubuntu/Debian
sudo apt install llvm-14-dev

# macOS
brew install llvm@14

# Set LLVM path
export LLVM_SYS_140_PREFIX=/usr/lib/llvm-14
```

### Linker Errors

The compiler generates object files that must be linked with the Blood runtime:

```bash
# Generate and compile the minimal C runtime
blood build --emit-runtime > runtime.c
cc -c runtime.c -o runtime.o

# Link your program
cc your_program.o runtime.o -o your_program
```

### Common Errors

| Error | Solution |
|-------|----------|
| "Unknown type `i32`" | Use lowercase types: `i32`, `bool`, `f64` |
| "Expected `;`" | Add semicolon after statements |
| "Undefined function" | Declare functions before use |
| "Type mismatch" | Check argument and return types |

## Getting Help

- [GitHub Issues](https://github.com/blood-lang/blood/issues)
- [Language Specification](SPECIFICATION.md)
- [Implementation Status](IMPLEMENTATION_STATUS.md)
