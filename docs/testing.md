# Testing

Taro has a language-level test harness and repository-level regression suites.
This document covers both.

## Language Tests

Mark a `() -> void` function with `@test` and run its file or package with
`taro test`.

| Attribute | Behavior |
| --- | --- |
| `@test` | Declares a test case |
| `@tag("smoke", "slow")` | Adds case-insensitive selection tags |
| `@skip` or `@skip("reason")` | Skips a test |
| `@expectPanic` | Passes only when the test panics |
| `@expectPanic("text")` | Also requires the panic report to contain `text` |

```taro
import std.testing.{assertEqual, assertTrue}

@test
func addition() {
    assertEqual(1 + 2, 3, "basic addition")
}

@test
@expectPanic("division by zero")
func divisionByZero() {
    let _ = 1 / 0
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
equivalent separators. Repeated tags use OR semantics, while combining a filter
with tags uses AND semantics. Selecting no tests is successful.

The standard library provides `assertEqual`, `assertTrue`, `assertFalse`, and
`fail` under `std.testing`.

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

Standard-library tests live under `std/src/tests/`. Language regression sources
live under `language_tests/source_files/`, with expected stdout or diagnostics
under `language_tests/outputs/`.

## Language Regression Directives

The runner reads directives from the first 30 lines of a language test. Normal
valid tests execute with `taro run` and compare stdout snapshots. Files under
`invalid/` must fail compilation and compare normalized stderr snapshots.
`CHECK_ONLY`, `TEST`, and `BENCH` cases use successful exit status instead of
snapshots.

| Directive | Effect |
| --- | --- |
| `// CHECK_ONLY` | Run `taro check` without producing or executing a binary |
| `// TEST` | Run `taro test` |
| `// BENCH` | Run a bounded benchmark smoke test in the selected codegen profile |
| `// BENCH_RELEASE` | Run the benchmark smoke test with its release/O2 default |
| `// TARGET: <triple>` | Cross-compile for the target triple |
| `// PACKAGE: <fixture>` | Run `language_tests/package_fixtures/<fixture>/app` |
| `// ARGS: <values...>` | Forward shell-split arguments to a normal run case |
| `// STDIN: <JSON string>` | Decode the JSON string and provide it as stdin |
| `// ENV: KEY=value ...` | Add environment variables to compile and execution |
| `// EXPECT_EXIT: <code>` | Override the expected runtime exit code |
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
    // Exercise synchronous stdin here.
}
```

When fixing a compiler regression, add the narrowest language or Rust test that
fails before the fix and passes afterward.
