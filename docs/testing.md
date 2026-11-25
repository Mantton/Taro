# Testing

Taro has a language-level test harness and repository-level regression suites.
This document covers both.

## Language Tests

Mark a non-generic function with `@test` and run its file or package with
`taro test`. Test functions take no parameters and return unit. Both synchronous
and `async` tests are supported; async tests execute through the runtime.

The return-type annotation may be omitted, written as `-> ()`, or use a type
alias for `()`. Other result types are rejected. Taro's unit type is `()`;
`void` is not a built-in type name.

| Attribute | Behavior |
| --- | --- |
| `@test` | Declares a test case |
| `@tag("smoke", "slow")` | Adds case-insensitive selection tags |
| `@skip` or `@skip("reason")` | Skips a test |
| `@expectPanic` | Passes only when the test panics |
| `@expectPanic("text")` | Also requires the panic report to contain `text` |

```taro
import std::testing::{assertEqual, assertTrue}

@test
func addition() {
    assertEqual(1 + 2, 3, "basic addition")
}

@test
@expectPanic("attempt to divide by zero")
func divisionByZero() {
    var _ = 1 / 0
}

@test
@tag("smoke")
func tagged() {
    assertTrue(true, "selected by tag")
}
```

Select cases with `--filter` and repeatable `--tag` options:

```bash
taro test std --filter testing.tests
taro test std --tag smoke --tag slow
taro test std --filter testing --tag smoke
```

Filters are case-insensitive substrings of qualified names; `.` and `::` are
equivalent separators. Tags on a namespace are inherited by its tests.
Repeated tags use OR semantics, while combining a filter with tags uses AND
semantics. Selecting no tests is successful.

The standard library provides `assertEqual`, `assertTrue`, `assertFalse`,
`fail`, `allocations`, and `subtest` under `std::testing`.

Use `std::testing::subtest(name, body)` to give table-driven cases individual
names and results inside an `@test` function. A panic inside a subtest is
caught and reported under that child's name without preventing sibling subtests
from running, while still failing the enclosing test and process:

```taro
@test
func queueCases() {
    std::testing::subtest("empty queue", () => {
        std::testing::assertTrue(true, "empty queue behaves as expected")
    })
}
```

## Documentation Tests (`--doc`)

Pass `--doc` to `taro test` to extract, compile, and execute fenced `taro`
code blocks from `///` doc comments in `.tr` files and from `.md` documents:

```bash
taro test std --doc
taro test docs/guide/syntax/lexical.md --doc
```

- Fences tagged ```` ```taro ```` are compiled and executed; snippets without
  `func main()` are automatically wrapped in `func main() { ... }` while
  preserving leading `import` declarations.
- Fences tagged ```` ```taro,ignore ```` are reported as ignored and skipped;
  ```` ```taro,no_run ```` compiles without executing.
- Compiler and runtime failures remap file paths and line numbers back to the
  authored `.tr` or `.md` source location.
- Running `taro test` without `--doc` runs the normal `@test` suite unchanged.

## Source Coverage (`--coverage`)

Pass `--coverage` to `taro test` to instrument user functions in the package
with LLVM source-based coverage (`@llvm.instrprof.increment` and LLVM Coverage
Mapping v6), execute the tests, merge profile counters via `llvm-profdata`, and
print a per-file report via `llvm-cov`:

```bash
taro test std --coverage
taro test path/to/file.tr --coverage
```

- Instrumented artifacts are built in a separate `<profile>-coverage` directory
  with a distinct incremental cache fingerprint, so alternating ordinary and
  coverage test runs never cross-contaminate cached objects.
- Compiler-generated shims, harnesses, and synthetic definitions are excluded
  from coverage attribution.
- The merged `.profdata` file is saved under the build's `coverage/` directory
  for line-by-line inspection with `llvm-cov show`.
- Override tool locations with `TARO_LLVM_PROFDATA` and `TARO_LLVM_COV` when
  LLVM tools are outside `PATH` or `xcrun`.

## Fuzz Targets (`--fuzz`)

Mark a synchronous, non-generic function that accepts a single
`std::mem::Span[uint8]` parameter and returns unit with `@fuzz`, then invoke it
through `taro test --fuzz <target>`:

```taro
@fuzz
func parserNeverPanics(_ data: std::mem::Span[uint8]) {
    text := std::string::stringFromBytes(data)
    var _ = std::convert::parse[int64](text)
}
```

```bash
taro test std --fuzz fuzzParseInt64NeverPanics --fuzz-runs 500 --fuzz-seed 42
```

- Normal `taro test` runs discover `@test` functions only and never execute
  `@fuzz` campaigns.
- `--fuzz-seed <u64>` makes input generation deterministic; `--fuzz-runs <n>`
  bounds the number of iterations (default `1000`); `--fuzz-max-len <bytes>`
  caps input size (default `4096`).
- When a fuzz target panics, the exact failing bytes are saved under the
  ignored `target/<profile>-fuzz/fuzz-artifacts/` directory and printed with a
  ready-to-run `--fuzz-replay <file>` command:

```bash
taro test path/to/pkg --fuzz parserNeverPanics --fuzz-replay target/debug-fuzz/fuzz-artifacts/crash-...bin
```

## Repository Test Suites

| Command | Coverage |
| --- | --- |
| `make test` | Rust workspace unit, integration, and doc tests |
| `make language-tests` | Taro compile/run diagnostics and behavior |
| `make std-tests` | Standard-library package tests |
| `make codegen-matrix` | High-risk backend cases in debug and release |
| `make runtime-stress` | Runtime-tagged std tests across worker counts |
| `make all-tests` | Development scripts, Rust, dist, LTO, std, and language tests |

Use `JOBS=<n>` to control language-test concurrency and
`FILTER=<substring>` to select language cases. Compiler changes should finish
with the complete compiler, language, standard-library, and codegen suites.

The language runner defaults to a release-built compiler/runtime and debug
generated programs. `--debug` selects a debug-built compiler/runtime;
`--codegen-profile debug|release|both` independently selects the generated-program
profiles. `make codegen-matrix` uses both generated profiles, and `make all-tests`
runs the entire language suite with both.

For repeated implementation checks, build once with
`python3 development/scripts/build_dist.py --profile release`, then run
`python3 development/scripts/language_tests.py --dist dist --codegen-profile both`.
`--dist` reuses the installed compiler/runtime/std without another bootstrap;
rebuild the distribution after compiler changes. It cannot be combined with
`--debug` or `--release`. `make all-tests` reuses its already-built distribution
for the language stage automatically. Use focused filters between full runs.

`make all-tests` runs Rust workspace tests in debug mode and std tests with the
default debug generated profile. It does not run release Rust tests, runtime
stress, editor tests, or external-corpus certification. Run those separately
when relevant.

Runtime stress compiles each program once, then executes it under every requested
worker setting. It defaults to release compiler/runtime and generated programs;
`python3 development/scripts/runtime_stress.py --debug` selects debug for both.

Standard-library tests live under `std/src/tests/`. Language regression sources
live under `language_tests/source_files/`, with expected stdout or diagnostics
under `language_tests/outputs/`. `TARO_LANGUAGE_TEST_BLESS=1` rewrites snapshots
that differ (and creates missing diagnostic snapshots) instead of failing;
review that diff before committing it.

## Language Regression Directives

The runner reads directives from the first 30 lines of a language test. Normal
valid tests execute with `taro run` and compare stdout snapshots. Files under
`invalid/` must fail compilation and compare normalized stderr snapshots.
Valid `CHECK_ONLY`, `TEST`, and `BENCH` cases use successful exit status instead
of snapshots unless `EXPECT_EXIT` overrides it. Invalid cases still require
diagnostic snapshots in every mode.

A missing stdout snapshot means the expected output is empty. Invalid tests
require a diagnostic snapshot. Without `TARO_LANGUAGE_TEST_BLESS=1`, the runner
never changes snapshots; write expected output explicitly when adding a case. Malformed known directives
fail the test, and supplemental output assertions apply to every execution mode.

| Directive | Effect |
| --- | --- |
| `// CHECK_ONLY` | Run `taro check` without producing or executing a binary |
| `// TEST` | Run `taro test` |
| `// BENCH` | Run a bounded benchmark smoke test in the selected codegen profile |
| `// BENCH_RELEASE` | Run the benchmark smoke test with its release/O2 default |
| `// OVERFLOW_CHECKS` | Enable checked arithmetic in every codegen profile |
| `// RUN_TWICE` | Run the command twice with one cache directory and check only the second run, which must reuse the cache (`Reusing`) |
| `// NO_INCREMENTAL` | Force a cold compile for fixtures observing compile-time diagnostics, which metadata cache hits do not replay |
| `// TARGET: <triple>` | Cross-compile for the target triple |
| `// PACKAGE: <fixture>` | Run `language_tests/package_fixtures/<fixture>/app` |
| `// ARGS: <values...>` | Forward shell-split arguments to a normal run case |
| `// STDIN: <JSON string>` | Decode the JSON string and provide it as stdin |
| `// ENV: KEY=value ...` | Add environment variables to compile and execution |
| `// EXPECT_EXIT: <code>` | Require this exit code, or use `nonzero` for a fatal failure without prescribing OS signal encoding; invalid cases must still fail |
| `// EXPECT_STDOUT_CONTAINS: <text>` | Require a stdout substring |
| `// EXPECT_STDERR_CONTAINS: <text>` | Require a stderr substring |
| `// EXPECT_STDERR_NOT_CONTAINS: <text>` | Forbid a stderr substring |
| `// EXPECT_STDERR_COUNT: <n> <text>` | Require an exact stderr occurrence count |

Substring assertions may be repeated. `ARGS` applies only to normal `taro run`
cases. `STDIN` must contain a valid JSON string so escapes such as `\n` are
decoded predictably.

```taro
// STDIN: "first line\nsecond line\n"
// EXPECT_STDOUT_CONTAINS: second line

func main() {
    var input = std::io::stdin()
    match std::io::readToString(input) {
        case .ok(text) => print(text)
        case .err(_) => std::testing::fail("stdin read failed")
    }
}
```

This normal run case also needs a stdout snapshot containing `first line` and
`second line`, each followed by a newline. The substring assertion supplements
the snapshot comparison.

When fixing a compiler regression, add the narrowest language or Rust test that
fails before the fix and passes afterward.

`./dist/bin/taro vet path --std-path std` checks for accidental copies of
`@NoCopy` values and for shadowing that hides a later read (see
[Local Bindings](guide/syntax/declarations.md#local-bindings)) without running a
program. It always rechecks the requested
root package, including after a metadata cache hit; dependencies can reuse
metadata. Normal checking does not enable these warnings. The language runner's
`// VET` directive selects this analysis-only command for positive and negative
fixtures.
