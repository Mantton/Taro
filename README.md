# Taro

Taro is an experimental programming language that draws inspiration from Rust, Swift, and Golang. It features a strong static type system, automatic garbage collection, and basic move semantics, with a familiar syntax inspired by all three languages.

## Prerequisites

- **Rust**: Latest stable version
- **LLVM**: Version 16

## Installation & Usage

Taro is distributed as a pre-built binary package. For development, we provide scripts to verify and run code easily.

### 1. Building the Compiler

To build the compiler, runtime, and standard library from source, use the `build_dist.py` script. This creates a `dist/` directory with a sysroot-like structure.

```bash
python3 development/scripts/build_dist.py
```

### 2. Running Code

To compile and run a Taro program (script or package) using your locally built compiler, use the `run_dist.py` script. This script automatically rebuilds the distribution if needed and sets up the strict environment (`TARO_HOME`, etc.) for you.

```bash
python3 development/scripts/run_dist.py examples/hello.tr
```

You can pass any arguments supported by the `taro run` command:

```bash
python3 development/scripts/run_dist.py [file_or_package] [args...]
```

### Manual Usage

If you prefer to run the binary directly (e.g., after adding `dist/bin` to your PATH):

```bash
export TARO_HOME=$(pwd)/dist
taro build examples/hello.tr
```

## Getting Started

Here is a simple "Hello, World!" example to get you started.

1.  Create a file named `hello.tr`:

    ```rust
    // hello.tr
    func main() {
        print("Hello, World!\n")
    }
    ```

2.  Run the file:
    ```bash
    python3 development/scripts/run_dist.py hello.tr
    ```

## Architecture & Features

### Compiler Pipeline
Taro's compiler pipeline is deeply inspired by modern compiler designs (like Rust's `rustc`). It progresses through several distinct stages:
-   **Parsing**: Source code is parsed into an Abstract Syntax Tree (AST).
-   **Name Resolution**: Resolves identifiers to their definitions, linking usage to declaration.
-   **HIR (High-level IR)**: The AST is lowered to a high-level intermediate representation where aggressive desugaring occurs.
-   **Type Checking**: A **Bidirectional TypeChecker** performs local expression type inference, handling function overloading and Swift-inspired optional coercions.
-   **THIR (Typed HIR)**: The fully typed representation where intrinsic operations (like integer addition) are lowered distinctly from overloaded function calls.
-   **MIR (Mid-level IR)**: A control-flow graph representation where significant optimizations happen (inlining, constant propagation, use-after-move catching, escape analysis).
-   **Codegen**: Handles monomorphization of generics and translates MIR to LLVM IR for final machine code generation.

### Memory Management
Taro uses a custom **non-moving, mark-and-sweep garbage collector** inspired by Golang's approach but tailored for simplicity and performance.
-   **Structure**: It uses a segregated-fit allocator with size classes and spans to minimize fragmentation.
-   **Concurrency**: Currently single-threaded stop-the-world, with future plans for concurrent marking.
-   **Safety**: The compiler emits shadow stack maps to precisely identify roots on the stack.

### Package Management
Taro features a built-in package manager that feels familiar to users of Cargo or Go Modules.
-   **Manifest**: Packages are defined in a TOML manifest.
-   **Dependencies**: Supports Git-based dependencies (tags, branches, commits) and local paths.
-   **Resolution**: Uses a full SAT solver approach (via `semver` and `petgraph`) to resolve dependency graphs.

### Key Features
-   **Enums**: Tagged unions (sum types) allow for expressive invalid state modeling.
-   **Generics**: Full monomorphization support (like Rust/C++ templates) for zero-cost abstractions.
-   **Diagnostics**: Rich, clear error messages to guide developers.
-   **Optimizations**: Sophisticated MIR passes including inlining, escape analysis, and simplify-cfg.
-   **Interoperability**: C ABI compatibility for easy FFI.


## Contributing

Contributions are welcome! Please check the `docs` directory for more information on the language internals.

## Design & Naming

Taro follows specific naming conventions for its standard library and core components:

- **Functions & Methods**: camelCase (e.g., `toString`, `makeIterator`).
- **Types (Structs, Enums, Interfaces)**: PascalCase (e.g., `String`, `Option`).
- **Variables**: snake_case (e.g., `local_var`, `index`).
- **Constants**: SCREAMING_SNAKE_CASE (e.g., `MAX_SIZE`).

**Exceptions:**
- **Intrinsics**: Intrinsic functions provided by the compiler are prefixed with `__intrinsic_` and use snake_case (e.g., `__intrinsic_ptr_add`).

## Repository Structure

-   `compiler/`: The core compiler source code (parsing, HIR, THIR, MIR, Codegen).
-   `runtime/`: Runtime components (Garbage Collector, attributes).
-   `std/`: The standard library implementation.
-   `language_tests/`: Comprehensive test suite for language features.
-   `compiler-cli/`: The command-line interface implementation.

## Package Structure

Taro packages follow a simple convention, similar to Cargo.

```bash
my-package/
├── package.toml   # Manifest file defining metadata and dependencies
├── src/           # Source code directory
│   └── main.tr    # Entry point
└── target/        # Build artifacts (automatically generated)
```

**Manifest Format**

The `package.toml` file must include a `[package]` section with a `name` field following the `<host>/<author>/<project>` convention.

If the package is a library, you must specify the `kind` field.

```toml
[package]
name = "github.com/mantton/apple"
version = "0.1.0"
kind = "library" # Required for libraries, defaults to "binary"
```

## Running Tests

To verify the compiler implementation, you can run the language test suite using the provided script. Note that we have both compiler unit tests (run via `cargo test`) and language E2E tests.

To run the language tests (which are easier for E2E verification):

```bash
python3 development/scripts/language_tests.py
```

You can also filter tests using a prefix:

```bash
python3 development/scripts/language_tests.py --filter basic_
```

## Roadmap & Status

Taro is currently **experimental**.

-   [x] Basic Compiler Pipeline (Parse -> Codegen)
-   [x] Garbage Collection (Stop-the-world)
-   [x] Generics & Monomorphization
-   [ ] Concurrency & Garbage Collection improvements
-   [ ] LSP Support & Editor Integration
-   [ ] Package Manager Polish & Registry
-   [ ] Standard Library Expansion

## Basics

Here are a few examples to showcase the familiar yet distinct syntax.

**Structs & Methods**

```rust
struct Point {
    x: int32
    y: int32
}

impl Point {
    // Allows usage of Point(x: ..., y: ...)
    func new(x: int32, y: int32) -> Point {
        return Point { x, y } // shorthand for { x: x, y: y }
    }

    func distance_squared(self) -> int32 {
        self.x * self.x + self.y * self.y // implicit return
    }

    operator +(self, other: Point) -> Point {
        Point { x: self.x + other.x, y: self.y + other.y }
    }
}

// Structs can also have immutable fields
struct Config {
    readonly id: int32
    debug: bool
}
```

**Enums (Tagged Unions)**



```rust
enum Message {
    case quit
    case move(int32, int32) // x, y
    case write(string)
}

func process(msg: Message) {
    match msg {
        case .quit => print("Quitting...\n")
        case Message.move(x, y) => print("Moving player\n") // fully qualified
        case .write(text) => print(text) // inferred
    }
}
```

> [!NOTE]
> Additional examples are available in the `examples` directory.

## Syntax Notes

-   **Automatic Semicolon Insertion (ASI)**: Semicolons are optional at the end of statements.
-   **Trailing Commas**: In multi-line sequences (like struct instantiation or lists), ensure you use explicit commas for the last element to prevent ASI from interpreting the newline as the end of the statement.

```rust
// Correct
let p = Point {
    x: 10,
    y: 20, // explicit comma required here if '}' is on next line
}
```
