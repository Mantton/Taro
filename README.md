# Taro

Taro is an experimental programming language that draws inspiration from Rust, Swift, and Golang. It features a strong static type system and automatic garbage collection, with a familiar syntax inspired by all three languages.

## Prerequisites

- **Rust**: Latest stable version
- **LLVM**: Version 16

## Quick Start

1. Build the compiler, runtime, and standard library:

   ```bash
   python3 development/scripts/build_dist.py
   ```

2. Create `hello.tr`:

   ```rust
   func main() {
       print("Hello, World!\n")
   }
   ```

3. Run the file with your local distribution:

   ```bash
   python3 development/scripts/run_dist.py hello.tr
   ```

4. Run tests in a file:

   ```bash
   python3 development/scripts/run_dist.py --test examples/test_example.tr
   ```

## Build and Run

### Build Distribution

To build the compiler, runtime, and standard library from source, use `build_dist.py`. This creates a distribution directory with a sysroot-like structure (`dist/` by default). For automation/bench workflows, `build_dist.py` also supports `--profile` and `--dist-dir`.

```bash
python3 development/scripts/build_dist.py
```

### Run with Distribution Scripts

To compile and run a Taro program (script or package) using your locally built compiler, use `run_dist.py`. This script rebuilds the distribution before running and sets up the strict environment (`TARO_HOME`, etc.) for you.

```bash
python3 development/scripts/run_dist.py examples/hello.tr
```

To run a file's test suite instead, pass `--test`:

```bash
python3 development/scripts/run_dist.py --test examples/test_example.tr
```

### Manual CLI Usage

If you install Taro as a toolchain with binaries under `<toolchain>/bin`, both `taro` and `taro-lsp` can infer `TARO_HOME` from that layout automatically.

For a local repo `dist/` or any other portable/custom layout, set `TARO_HOME` explicitly:

```bash
export TARO_HOME=$(pwd)/dist
taro build examples/hello.tr
```

### VS Code Extension

The VS Code extension is designed for an external Taro toolchain install:

- put the toolchain `bin/` directory on your `PATH`
- ensure the toolchain root contains attached std artifacts under `lib/taro/std/<target>/`
- use `taro.languageServer.path` only for custom `taro-lsp` locations
- use `taro.languageServer.env` only for advanced overrides such as a custom `TARO_HOME`

Repo-local `target/debug/taro-lsp` and `dist/` are still supported as a development fallback when working inside the Taro repository.

### Language Server (Basic)

`taro-lsp` currently provides:

- diagnostics (parse/resolve/typecheck and related info) on open/change/save
- hover
- go-to-definition
- signature help

This is intentionally a basic surface for now (for example, completion/rename/formatting are not part of this phase yet).

### Compiler Timings

To print compiler phase timings (parse/typecheck/THIR/MIR/codegen/link), pass `--timings`:

```bash
taro build examples/hello.tr --timings
taro check examples/hello.tr --timings
```

`benchmark_timings.py` bootstraps per-profile distributions via `build_dist.py` and then reports timing comparison tables:

```bash
python3 development/scripts/benchmark_timings.py examples/hello.tr
python3 development/scripts/benchmark_timings.py examples/hello.tr --runs 10
python3 development/scripts/benchmark_timings.py examples/hello.tr --command run --runs 5
```

### Incremental Compilation

Incremental dependency reuse is enabled by default for:

- `taro build`
- `taro run`
- `taro test`
- `taro check`

Per dependency package, the compiler emits:

- `target/<profile>/metadata/<package-identifier>.taro_meta`
- `target/<profile>/objects/<package-identifier>.o` (build/run/test paths)

Reuse is mode-aware:

- `build`/`run`/`test` reuse dependency metadata + object artifacts.
- `check` reuses dependency semantic metadata only (no object requirement).

### Attached Std Artifacts (Strict)

`std` is treated as an attached toolchain artifact by default. The compiler expects prebuilt std artifacts in `TARO_HOME` and does not silently rebuild std on cache misses.

Expected attached std artifact layout:

- `TARO_HOME/lib/taro/std/<target-triple>/std.taro_meta`
- `TARO_HOME/lib/taro/std/<target-triple>/std.o`

On missing/invalid std artifacts, the compiler errors with guidance to rebuild std explicitly.

Use `--build-std` to rebuild and publish attached std artifacts from source.
Attached std is built in a canonical release-like configuration per target (shared across debug/release user builds):

```bash
taro check examples/hello.tr --build-std
```

Metadata reuse is guarded by format/version/compiler stamp/target/options/fingerprint/checksum validation for normal dependency caches.

The root package is still cold-compiled/rechecked in v0.

Use `--no-incremental` to force a cold path:

```bash
taro build my-package --no-incremental
taro run my-package --no-incremental
taro test my-package --no-incremental
taro check my-package --no-incremental
```

Metadata files use the `.taro_meta` extension and a binary internal ABI (not JSON).

### Makefile Commands

For day-to-day development, you can use the root `Makefile`:

```bash
make help
make run FILE=examples/hello.tr
make check FILE=examples/hello.tr
make lsp
make test
make language-tests
make std-tests
make all-tests
```

### Panic Stack Traces

Panic reports default to compact Taro-first output:

- prefer language-level frames under `taro stack:`
- otherwise render a filtered native backtrace (keeping Taro/std/synthetic entry frames)
- if filtering would be empty, fall back to a short raw trace so output is never blank

When a symbol is synthetic and no source definition symbol exists, stack entries use a stable fallback name (`missing_p{pkg}_d{idx}`) instead of debug-formatted IDs.

Set `TARO_BACKTRACE=full` to print the full unfiltered native backtrace.

## Language Basics

Here are a few examples to showcase the familiar yet distinct syntax.

**Structs & Methods**

```rust
struct Point {
    x: int32
    y: int32
}

impl Point {
    // Static `new(...)` methods can also be called as `Point(...)`.
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

**Optional / Result Propagation**

Postfix `!` propagates `Optional[T]` and `Result[T, E]` values.

- `Optional[T]!` extracts `T` or returns `.none` from the enclosing `Optional` context.
- `Result[T, E]!` extracts `T` or returns `.err(error)` from the enclosing `Result` context.
- Propagation only works within the same container family.
- `Result` propagation requires an exact error-type match.
- For awaited values, write `(await expr)!`.

```rust
func nextPort(raw: Optional[int32]) -> Optional[int32] {
    let port = raw!
    return .some(port + 1)
}

func readCount(input: Result[int32, std.io.Error]) -> Result[int32, std.io.Error] {
    let count = input!
    return .ok(count + 1)
}

func joinTask(task: std.task.Task[int32]) async -> Result[int32, std.task.TaskError] {
    let value = (await task.result())!
    return .ok(value)
}
```

> [!NOTE]
> Additional examples are available in the `examples` directory.

## Syntax Notes

- **Automatic Semicolon Insertion (ASI)**: Semicolons are optional at the end of statements.
- **Leading `.` on a New Line**: A line that starts with `.` is parsed as postfix continuation of the previous expression unless the previous statement is explicitly terminated.
- **Trailing Commas**: In multi-line sequences (like struct instantiation or lists), ensure you use explicit commas for the last element to prevent ASI from interpreting the newline as the end of the statement.
- **Integer Type Suffixes**: Integer literals support suffixes in `D_TY` form:
  - Signed: `_i8`, `_i16`, `_i32`, `_i64`
  - Unsigned: `_u8`, `_u16`, `_u32`, `_u64`
  - Uppercase sign specifiers are accepted (`_I32`, `_U64`)
  - Examples: `1_u32`, `200_i64`, `0xFF_u16`

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
| `@tag` | Adds tags for test selection. Valid on `@test` functions and `namespace` declarations. Uses string literals: `@tag("smoke", "slow")`. |
| `@skip` | Skips the test. Accepts an optional reason string: `@skip("not yet implemented")`. |
| `@expectPanic` | Passes if the function panics, fails if it returns normally. Accepts an optional expected message: `@expectPanic("out of bounds")`. |

### Filtering Tests

Use `--filter` to match qualified test names and `--tag` to select tagged tests:

```bash
taro test std --filter testing.testing_tests
taro test std --filter TESTING.TESTS
taro test std --tag smoke --tag slow
taro test std --filter testing --tag smoke
```

Rules:

- `--filter` is a case-insensitive substring match against the qualified name.
- `.` and `::` are treated as equivalent separators when matching names.
- `--tag` is case-insensitive and repeatable; multiple tags use OR semantics (any tag).
- Combining `--filter` and `--tag` uses AND semantics (must satisfy both).
- If nothing matches, the run succeeds with `running 0 tests`.

### Test Example

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

@tag("smoke")
namespace CoreTests {
    @test
    func testNamespaceTagInheritance() {
        assertTrue(true, "namespace tags are inherited")
    }
}

@test
@tag("slow")
func testTaggedFunction() {
    assertTrue(true, "function tags are supported")
}
```

Running `taro test` on the above produces:

```
running 5 tests

test testAddition ... ok
test testDivisionByZero ... ok
test testNotYetReady ... SKIPPED (pending implementation)
test CoreTests::testNamespaceTagInheritance ... ok
test testTaggedFunction ... ok

test result: ok. 4 passed; 0 failed; 1 skipped
```

### Assertion Helpers

The standard library provides assertion helpers in `std/testing`:

| Function | Description |
|----------|-------------|
| `assertEqual(a, b, msg)` | Fails if `a != b` |
| `assertTrue(cond, msg)` | Fails if `cond` is `false` |
| `assertFalse(cond, msg)` | Fails if `cond` is `true` |
| `fail(msg)` | Unconditionally fails the test |

### Repository Test Commands

To verify the compiler implementation, use the command that matches the test surface you want:

- `cargo test --workspace`: Rust unit/integration/doctests for workspace crates.
- `python3 development/scripts/language_tests.py`: Taro language E2E tests in `language_tests/source_files`. Runs in parallel by default using `min(selected_tests, CPU core count)` workers; `--jobs` is only needed to override (for example, `--jobs 1` for serial mode). Bootstraps an isolated distribution via `build_dist.py` (release by default; pass `--debug` for debug bootstrap).
- `make std-tests`: Runs std package tests only (`taro test std`) via the `test_all.py` std stage.
- `python3 development/scripts/test_all.py`: Unified fail-fast pipeline (cargo tests, dist build, std compile smoke, std package tests, language tests).
- `make all-tests`: Shorthand for the unified pipeline.

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

## Packages

### Package Management

Taro features a built-in package manager that feels familiar to users of Cargo or Go Modules.

- **Manifest**: Packages are defined in a TOML manifest.
- **Dependencies**: Supports Git-based dependencies (tags, branches, commits) and local paths.
- **Resolution**: Uses semver-aware selection with dependency graph validation (via `semver` and `petgraph`) to resolve dependency graphs.
- **Locking**: Generates `package.lock` with resolved revisions and dependency tree hashes for reproducible builds.
- **Integrity**: Verifies installed Git dependencies against locked content hashes and fails on tampering.

### Lockfile and Strict Mode

`package.lock` is generated automatically on dependency sync (`build`, `check`, `run`, `test` for package roots).

- `--locked`: Require `package.lock` to be present and up to date; do not rewrite it.
- `--update-lock`: Force lockfile refresh from current dependency sources.
- `CI=true`: Enables strict lock behavior (same drift checks as `--locked`).

Security policy in this phase:

- Transitive `path` dependencies are rejected. Only the root manifest may declare `path` dependencies.
- Git cache identity is bound to canonical URL + package name, and cached repositories are origin-validated.

### Package Structure

Taro packages follow a simple convention, similar to Cargo.

```bash
my-package/
├── package.toml   # Manifest file defining metadata and dependencies
├── src/           # Source code directory
│   └── main.tr    # Entry point
└── target/        # Build artifacts (automatically generated)
```

### Manifest Format

The `package.toml` file must include a `[package]` section with a `name` field following the `<host>/<author>/<project>` convention.

`kind` is optional and defaults to `executable`. Supported values are
`library`, `executable`, and `both`.

```toml
[package]
name = "github.com/mantton/apple"
version = "0.1.0"
kind = "library"
```

## Architecture and Features

### Compiler Pipeline

Taro's compiler pipeline is deeply inspired by modern compiler designs (like Rust's `rustc`). It progresses through several distinct stages:

- **Parsing**: Source code is parsed into an Abstract Syntax Tree (AST).
- **Name Resolution**: Resolves identifiers to their definitions, linking usage to declaration.
- **HIR (High-level IR)**: The AST is lowered to a high-level intermediate representation where aggressive desugaring occurs.
- **Type Checking**: A **Bidirectional TypeChecker** performs local expression type inference, handling function overloading and Swift-inspired optional coercions.
- **THIR (Typed HIR)**: The fully typed representation where intrinsic operations (like integer addition) are lowered distinctly from overloaded function calls.
- **MIR (Mid-level IR)**: A control-flow graph representation where significant optimizations happen (inlining, copy propagation, escape analysis).
- **Codegen**: Handles monomorphization of generics and translates MIR to LLVM IR for final machine code generation.

### Async Concurrency Runtime

Taro includes a multithreaded async runtime:

- `std.task.spawn` runs async closures concurrently and returns `Task[T]`
- `Task.result()` returns `Result[T, TaskError]` with cancellation/panic reporting
- `Task.cancel()` and `std.task.isCancelled()` provide cancellation controls
- `withTaskGroup` supports `.cancelOnPanic` and `.independent` policies
- `std.task.sleep` and `std.io.task.AsyncStream` provide timer and async I/O integration

The executor uses worker threads with work stealing. Worker count defaults to logical CPU count and can be overridden with `TARO_WORKERS`.

### Memory Management

Taro uses a custom **non-moving, mark-and-sweep garbage collector** inspired by Golang's approach but tailored for simplicity and performance.

- **Structure**: It uses a segregated-fit allocator with size classes and spans to minimize fragmentation.
- **Concurrency**: Currently single-threaded stop-the-world, with future plans for concurrent marking.
- **Safety**: The compiler emits shadow stack frames and root slots to precisely identify stack roots.

### Key Features

- **Enums**: Tagged unions (sum types) allow for expressive invalid state modeling.
- **Generics**: Full monomorphization support (like Rust/C++ templates) for zero-cost abstractions.
- **Move Semantics**: Rust-style ownership and move semantics, with values moved by default and explicit copying for copyable types, but without a mutability uniqueness guarantee.
- **Async Concurrency**: Multithreaded task runtime (`std.task.spawn`, cancellation, task groups, async sleep, async stream I/O).
- **Diagnostics**: Rich, clear error messages to guide developers.
- **Basic LSP**: Diagnostics, hover, go-to-definition, and signature help via `taro-lsp`.
- **Panic Reporting**: Compact Taro-first panic stacks by default, with `TARO_BACKTRACE=full` for raw native traces.
- **Optimizations**: Sophisticated MIR passes including inlining, escape analysis, and simplify-cfg.
- **Interoperability**: C ABI compatibility for easy FFI.
- **Built-in Testing**: First-class test support via `taro test` with `@test`, `@tag`, `@skip`, `@expectPanic`, plus `--filter` / `--tag` selection.

## Repository Structure

- `compiler/`: The core compiler source code (parsing, HIR, THIR, MIR, codegen).
- `runtime/`: Runtime components (garbage collector, async executor, panic/unwind support).
- `std/`: The standard library implementation.
- `language_tests/`: Comprehensive test suite for language features.
- `compiler-cli/`: The command-line interface implementation.
- `taro-lsp/`: Language server implementation.
- `editors/`: Editor integrations (VS Code, Zed).

## Roadmap and Status

Taro is currently **experimental**.

- [x] Basic Compiler Pipeline (Parse -> Codegen)
- [x] Garbage Collection (Stop-the-world)
- [x] Generics and Monomorphization
- [x] Built-in Test Framework (`taro test`, `@test`, `@tag`, `@skip`, `@expectPanic`, `--filter`, `--tag`)
- [x] Async Concurrency Runtime (`std.task`, task groups, async timers, async I/O waits)
- [x] Basic LSP support and editor integration (`taro-lsp`, VS Code, Zed)
- [ ] Package manager polish and registry
- [ ] Standard library expansion

## Contributing

Contributions are welcome. Check the `docs` directory for more information on the language internals.
