# Taro

Taro is an experimental compiled programming language inspired by Rust, Swift,
and Go. It combines algebraic data types, interfaces, generics, move semantics,
and structured concurrency with automatic garbage collection.

> [!WARNING]
> Taro is under active development. Language syntax, compiler metadata,
> standard-library APIs, and package tooling may change between commits.

## Highlights

- Strong static typing with bidirectional inference
- Payload enums, exhaustive pattern matching, optionals, and results
- Interfaces, associated types, generics, and monomorphization
- Rust-style moves with a non-moving, precise garbage collector
- Multithreaded async tasks, cancellation, groups, selection, and timeouts
- First-class tests and benchmarks
- LLVM code generation with incremental builds, bitcode, and optional LTO
- C ABI interoperability and compact language-level panic reports

## Quick Start

### Requirements

- Latest stable Rust
- LLVM 22.1.x; 22.1.8 is the certified development version
- A C++17 compiler for the narrow LLVM ThinLTO shim

`llvm-sys` discovers LLVM through `PATH`, Homebrew, or
`LLVM_SYS_221_PREFIX`. On macOS:

```bash
brew install llvm@22
```

On Linux, set the prefix only when `llvm-config` is not discoverable:

```bash
export LLVM_SYS_221_PREFIX=/usr/lib/llvm-22
```

### Run an Example

The repository helper builds a release distribution, configures `TARO_HOME`,
and runs the program:

```bash
python3 development/scripts/run_dist.py examples/hello.tr
```

The generated toolchain is available under `dist/`. Reuse it directly with:

```bash
export TARO_HOME="$PWD/dist"
dist/bin/taro check examples/hello.tr
dist/bin/taro run examples/fibonacci.tr
dist/bin/taro --help
```

## A Taste of Taro

```taro
import std.ops.Add

struct Point {
    x: int32
    y: int32
}

impl Add for Point {
    func add(self, rhs: Point) -> Point {
        Point { x: self.x + rhs.x, y: self.y + rhs.y }
    }
}

enum Command {
    case move(Point)
    case quit
}

func execute(command: Command) {
    match command {
        case .move(point) => print(f"moving to {point.x}, {point.y}\n")
        case .quit => print("quitting\n")
    }
}

func main() {
    execute(command: .move(Point { x: 3, y: 4 }))
}
```

Semicolons are inserted automatically. Taro also supports closures, async
functions, interfaces, associated types, opaque returns, optional chaining,
result propagation with postfix `!`, const generics, and checked formatted
strings. See the [syntax guide](docs/guide/syntax/README.md) and
[examples](examples/) for more.

## Packages

Create executable, library, or combined packages from a full package
identifier:

```bash
taro new github.com/acme/app
taro new github.com/acme/lib --kind library
```

Packages use `package.toml` and generated `package.lock` files. The package
manager supports Git dependencies, root-local path dependencies, aliases,
semantic-version resolution, locked revisions, and content verification. There
is no public registry yet.

See [Packages](docs/packages.md) for manifests, dependency selectors, and lock
behavior.

## Development

`make help` lists the maintained repository workflows.

| Command | Purpose |
| --- | --- |
| `make dist` | Build the compiler, runtime, and attached std |
| `make run FILE=examples/hello.tr` | Build and run a program |
| `make test` | Run Rust workspace tests |
| `make language-tests` | Run language end-to-end tests |
| `make std-tests` | Run standard-library tests |
| `make codegen-matrix` | Exercise high-risk codegen in debug and release |
| `make runtime-stress` | Stress the async runtime across worker counts |
| `make all-tests` | Run the complete repository pipeline |

Use `JOBS=<n>` with the language and codegen suites. See
[Developing Taro](docs/development.md) for local distributions, diagnostics,
benchmarking, and troubleshooting, and [Testing](docs/testing.md) for harness
attributes and regression directives.

## Documentation

| Document | Contents |
| --- | --- |
| [Syntax guide](docs/guide/syntax/README.md) | Practical language syntax by topic |
| [Grammar](docs/GRAMMAR.md) | Formal lexical and syntactic reference |
| [Development](docs/development.md) | Building, diagnostics, benchmarks, troubleshooting |
| [Testing](docs/testing.md) | Language harness and repository regression suites |
| [Code generation](docs/codegen.md) | Profiles, bitcode, LTO, incremental artifacts, cross-compilation |
| [Packages](docs/packages.md) | Manifests, dependency resolution, and lockfiles |
| [Async runtime](docs/async-runtime.md) | Executor lifecycle and concurrency invariants |
| [Existentials](docs/existentials.md) | Existential representation and dispatch |
| [Release checklist](docs/RELEASE_CHECKLIST.md) | Required validation before release |

## Status and Limitations

- Repository workflows currently support Unix-like hosts; Windows is out of
  scope.
- Std is an attached toolchain artifact and must be rebuilt after incompatible
  compiler metadata changes.
- Package management has no public registry.
- VS Code and Zed integrations provide syntax and static editing support, not
  diagnostics, completion, navigation, or refactoring.
- `.taro_meta` is an internal binary format, not a stable interchange format.

Near-term work includes package-manager polish, standard-library expansion,
runtime and GC improvements, and richer editor tooling.

## Repository Layout

| Path | Purpose |
| --- | --- |
| `compiler/` | Parsing, semantics, IRs, optimization, and LLVM codegen |
| `compiler-cli/` and `taro-bin/` | CLI workflows and the `taro` executable |
| `runtime/` | GC, executor, panic, process, filesystem, and native services |
| `std/` | Standard library sources and tests |
| `language_tests/` | End-to-end language and backend regressions |
| `showcase/` and `examples/` | Substantial and minimal Taro programs |
| `development/` | Build, test, benchmark, and verification tooling |
| `docs/` | Language, compiler, runtime, and contributor references |
| `editors/` and `tree-sitter-taro/` | Static editor integrations |

## Contributing

Contributions are welcome. Keep changes focused, add regression coverage for
behavior changes, and run the relevant suites above. Compiler changes require
the full compiler, language, standard-library, and codegen test surfaces.
