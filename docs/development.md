# Developing Taro

This guide covers the repository workflows used to build, run, inspect, and
benchmark the compiler. For language tests and regression conventions, see
[Testing](testing.md).

## Build a Local Distribution

Source builds require the toolchain listed in the
[root README](../README.md#requirements). Build the compiler, runtime, and
attached standard library with:

```bash
python3 development/scripts/build_dist.py
```

The default release distribution is written to `dist/`:

```text
dist/
├── bin/taro
├── lib/taro/runtime/
├── lib/taro/std/
└── std -> <repository>/std
```

Run `python3 development/scripts/build_dist.py --help` for profile, output
directory, standard-library source, and target options. The compiler, runtime,
and attached standard-library artifacts are assembled before an existing
distribution is replaced. A build or bootstrap failure preserves the last
usable `dist/`; symlink destinations are rejected.

## Run the Local Compiler

`run_dist.py` rebuilds the distribution, configures `TARO_HOME`, and invokes
the compiler:

```bash
python3 development/scripts/run_dist.py examples/hello.tr
python3 development/scripts/run_dist.py examples/hello.tr -- first second
python3 development/scripts/run_dist.py --test showcase/monkey
```

To reuse an existing distribution directly:

```bash
export TARO_HOME="$PWD/dist"
dist/bin/taro check examples/hello.tr
dist/bin/taro run examples/fibonacci.tr
dist/bin/taro --help
```

An installed toolchain infers `TARO_HOME` when `taro` lives under its
`bin/` directory and the toolchain root contains `lib/taro/`.

## Common Make Targets

`make help` is the authoritative list. The usual workflows are:

| Command | Purpose |
| --- | --- |
| `make dist` | Build the local release distribution |
| `make run FILE=examples/hello.tr` | Build and run a source file or package |
| `make check FILE=examples/hello.tr` | Type-check with the local distribution |
| `make test` | Run Rust workspace tests |
| `make language-tests` | Run language end-to-end tests |
| `make codegen-matrix` | Run high-risk codegen tests in debug and release |
| `make std-tests` | Run standard-library package tests |
| `make runtime-stress` | Exercise runtime-tagged tests across worker counts |
| `make all-tests` | Run the complete repository test pipeline |
| `make bench PACKAGE=path` | Run Taro `@bench` functions |

The language and codegen runners accept `JOBS=<n>`. Language tests also accept
`FILTER=<substring>`.

## Inspect the Compiler

The CLI exposes the maintained diagnostics; use `taro <command> --help` for
the complete option set.

```bash
taro build examples/arithmetic.tr --timings
taro build examples/arithmetic.tr --dump-mir
taro build examples/arithmetic.tr --dump-llvm
taro build examples/arithmetic.tr --release \
  --optimization-remarks 'inline|loop-vectorize' \
  --debug-info line-tables
```

Panic reports prefer compact Taro frames. Set `TARO_BACKTRACE=full` for an
unfiltered native backtrace. Runtime scheduler, I/O, and GC diagnostics are
available through `taro run --runtime-stats` and `--runtime-trace`.

## Benchmarking

`taro bench` runs synchronous, non-generic `@bench` functions with exactly one
`&mut std.bench.Benchmark` parameter and a unit result. The current harness
requires the return-type annotation to be omitted: even an explicit `-> ()`
is rejected. This is the same annotation restriction as for
[test functions](testing.md#language-tests). The parameter cannot be defaulted
or variadic. Benchmarks compile in release/O2 by default and each selected case
runs in a fresh process.

```bash
taro bench my-package
taro bench my-package --list
taro bench my-package --filter parse --tag smoke
taro bench my-package --warmup 500ms --time 2s --samples 30
taro bench my-package --format json
```

Use `std.hint.blackBox(value)` as a best-effort optimizer barrier and
`std.runtime.keepAlive(value)` when GC reachability is the requirement.
`taro bench --help` documents the measurement and timeout controls.

Repository tooling also measures the compiler itself:

```bash
python3 development/scripts/benchmark_timings.py examples/hello.tr --runs 10
make codegen-benchmark RUNS=10
make monkey-host-benchmark
```

The first command measures cold compiler phases. The codegen benchmark compares
the release baseline with O2, verifies equivalent output, and reports compile
time, runtime, and executable size. The Monkey host-gap suite runs matched Taro
and Go workloads for dictionary/environment lookup and churn, argument lists,
successful `Result` propagation, and small allocations. It verifies checksums
before reporting median time and allocation/GC counters; see
`development/benchmarks/monkey_host_gap/README.md` for interpretation guidance.

## Troubleshooting

- **Missing or invalid std artifacts:** rebuild `dist/`. For an intentional
  source rebuild, pass `--std-path std --build-std` with `TARO_HOME` set.
- **Runtime or linker errors:** verify the runtime archive and adjacent
  `.manifest.toml` under `$TARO_HOME/lib/taro/runtime/`. Cross targets may also
  require `--linker` and `--sysroot`.
- **Stale package artifacts:** retry once with `--no-incremental`. Compiler
  metadata changes intentionally invalidate older `.taro_meta` files.
- **Lockfile drift:** use `--update-lock` when dependency requests intentionally
  change, then commit the resulting `package.lock`.
