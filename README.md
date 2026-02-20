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

To compile and run a Taro program (script or package) using your locally built compiler, use the `run_dist.py` script. This script rebuilds the distribution before running and sets up the strict environment (`TARO_HOME`, etc.) for you.

```bash
python3 development/scripts/run_dist.py examples/hello.tr
```

To run a file's test suite instead, pass `--test`:

```bash
python3 development/scripts/run_dist.py --test examples/test_example.tr
```

### Manual Usage

If you prefer to run the binary directly (e.g., after adding `dist/bin` to your PATH):

```bash
export TARO_HOME=$(pwd)/dist
taro build examples/hello.tr
```

To print compiler phase timings (parse/typecheck/THIR/MIR/codegen/link), pass `--timings`:

```bash
taro build examples/hello.tr --timings
taro check examples/hello.tr --timings
```

### Quick Commands (Makefile)

For day-to-day development, you can use the root `Makefile`:

```bash
make help
make run FILE=examples/hello.tr
make check FILE=examples/hello.tr
make test
make language-tests
make std-tests
make all-tests
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

## Testing

Taro has a built-in test runner. Mark any `() -> void` function with `@test` and run it with `taro test`:

```bash
taro test my_file.tr
# or for a package:
taro test my-package/
```

### Test Attributes

| Attribute | Description |
|-----------|-------------|
| `@test` | Marks a function as a test case. Must be `() -> void`. |
| `@skip` | Skips the test. Accepts an optional reason string: `@skip("not yet implemented")`. |
| `@expectPanic` | Passes if the function panics, fails if it returns normally. Accepts an optional expected message: `@expectPanic("out of bounds")`. |

### Example

```rust
@test
func testAddition() {
    assertEqual(1 + 2, 3, "basic addition")
}

@test
@expectPanic
func testDivisionByZero() {
    let _ = 1 / 0
}

@test
@skip("pending implementation")
func testNotYetReady() {
    fail("not implemented")
}
```

Running `taro test` on the above produces:

```
running 3 tests

test testAddition ... ok
test testDivisionByZero ... ok
test testNotYetReady ... SKIPPED (pending implementation)

test result: ok. 2 passed; 0 failed; 1 skipped
```

### Assertion Helpers

The standard library provides assertion helpers in `std/testing`:

| Function | Description |
|----------|-------------|
| `assertEqual(a, b, msg)` | Fails if `a != b` |
| `assertTrue(cond, msg)` | Fails if `cond` is `false` |
| `assertFalse(cond, msg)` | Fails if `cond` is `true` |
| `fail(msg)` | Unconditionally fails the test |

## Architecture & Features

### Compiler Pipeline
Taro's compiler pipeline is deeply inspired by modern compiler designs (like Rust's `rustc`). It progresses through several distinct stages:
-   **Parsing**: Source code is parsed into an Abstract Syntax Tree (AST).
-   **Name Resolution**: Resolves identifiers to their definitions, linking usage to declaration.
-   **HIR (High-level IR)**: The AST is lowered to a high-level intermediate representation where aggressive desugaring occurs.
-   **Type Checking**: A **Bidirectional TypeChecker** performs local expression type inference, handling function overloading and Swift-inspired optional coercions.
-   **THIR (Typed HIR)**: The fully typed representation where intrinsic operations (like integer addition) are lowered distinctly from overloaded function calls.
-   **MIR (Mid-level IR)**: A control-flow graph representation where significant optimizations happen (inlining, copy propagation, use-after-move catching, escape analysis).
-   **Codegen**: Handles monomorphization of generics and translates MIR to LLVM IR for final machine code generation.

### Memory Management
Taro uses a custom **non-moving, mark-and-sweep garbage collector** inspired by Golang's approach but tailored for simplicity and performance.
-   **Structure**: It uses a segregated-fit allocator with size classes and spans to minimize fragmentation.
-   **Concurrency**: Currently single-threaded stop-the-world, with future plans for concurrent marking.
-   **Safety**: The compiler emits shadow stack frames and root slots to precisely identify stack roots.

### Package Management
Taro features a built-in package manager that feels familiar to users of Cargo or Go Modules.
-   **Manifest**: Packages are defined in a TOML manifest.
-   **Dependencies**: Supports Git-based dependencies (tags, branches, commits) and local paths.
-   **Resolution**: Uses semver-aware selection with dependency graph validation (via `semver` and `petgraph`) to resolve dependency graphs.

### Key Features
-   **Enums**: Tagged unions (sum types) allow for expressive invalid state modeling.
-   **Generics**: Full monomorphization support (like Rust/C++ templates) for zero-cost abstractions.
-   **Diagnostics**: Rich, clear error messages to guide developers.
-   **Optimizations**: Sophisticated MIR passes including inlining, escape analysis, and simplify-cfg.
-   **Interoperability**: C ABI compatibility for easy FFI.
-   **Built-in Testing**: First-class test support via `taro test` with `@test`, `@skip`, and `@expectPanic` attributes.


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

To verify the compiler implementation, use the command that matches the test surface you want:

- `cargo test --workspace`: Rust unit/integration/doctests for workspace crates.
- `python3 development/scripts/language_tests.py`: Taro language E2E tests in `language_tests/source_files`. Runs in parallel by default using `min(selected_tests, CPU core count)` workers; `--jobs` is only needed to override (for example, `--jobs 1` for serial mode).
- `python3 development/scripts/test_all.py`: unified fail-fast pipeline (cargo tests, dist build, std compile smoke, std package tests, language tests).
- `make all-tests`: shorthand for the unified pipeline.

Std package tests live under `std/src/tests/<module>/<module_tests>.tr` and run in the `test_all.py` std stage (or via `make std-tests`).

If you only want language tests with simple flags:

```bash
make language-tests            # JOBS auto-defaults to the language test runner default
make language-tests JOBS=4     # optional override
make language-tests FILTER=std_
```

### Language Test Directives

Test files in `language_tests/source_files/` can contain directive comments that control how the runner executes them:

| Directive | Description |
|-----------|-------------|
| `// TEST` | Run with `taro test` instead of `taro run`. Passes if exit code is 0 (all tests pass). No output snapshot is compared. |
| `// CHECK_ONLY` | Type-check only via `taro check`. No binary is produced or run. |
| `// TARGET: <triple>` | Cross-compile for the given target triple. |
| `// EXPECT_EXIT: <code>` | Expect the given exit code instead of 0. |
| `// EXPECT_STDERR_CONTAINS: <text>` | Assert that `<text>` appears in stderr output. |

Use `// TEST` to write language tests that exercise the test harness itself:

```rust
// TEST
@test
func myTest() {
    assertEqual(1 + 1, 2, "math works")
}
```

## Roadmap & Status

Taro is currently **experimental**.

-   [x] Basic Compiler Pipeline (Parse -> Codegen)
-   [x] Garbage Collection (Stop-the-world)
-   [x] Generics & Monomorphization
-   [x] Built-in Test Framework (`taro test`, `@test`, `@skip`, `@expectPanic`)
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
-   **Leading `.` on a New Line**: A line that starts with `.` is parsed as postfix continuation of the previous expression unless the previous statement is explicitly terminated.
-   **Trailing Commas**: In multi-line sequences (like struct instantiation or lists), ensure you use explicit commas for the last element to prevent ASI from interpreting the newline as the end of the statement.

```rust
let out = value
.some(out)     // parsed as: value.some(out)

let out = value;
.some(out)     // standalone inferred member expression
```

```rust
// Correct
let p = Point {
    x: 10,
    y: 20, // explicit comma required here if '}' is on next line
}
```
