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

### Stage a macOS SDK

Use the release SDK build to test a relocatable install on a native macOS
host. It builds the CLI with vendored Git and OpenSSL, includes the LSP, and
copies std sources before building the attached artifacts. Both Cargo workspaces
use their committed lockfiles in this build. The loader audit rejects shared
libraries outside the macOS system paths.

For an LLVM build that links zstd, supply a static archive for the host
architecture. The path below is an example for an Apple Silicon Homebrew
build machine.

```sh
python3 -B development/scripts/build_dist.py --macos-sdk \
  --static-zstd /opt/homebrew/opt/zstd/lib/libzstd.a \
  --dist-dir "$PWD/target/taro-0.1.0-macos-arm64"
COPYFILE_DISABLE=1 tar -czf target/taro-0.1.0-macos-arm64.tar.gz \
  -C target taro-0.1.0-macos-arm64
python3 -B development/scripts/smoke_macos_sdk.py target/taro-0.1.0-macos-arm64.tar.gz
```

The smoke test extracts the archive to a new path, checks native linking with
only system tools on `PATH`, and verifies editor navigation into and within std.
Pass `--developer-dir /Library/Developer/CommandLineTools` to test Command Line
Tools on a host that also has Xcode installed.

Keep the SDK directory together and add its `bin/` to your shell's `PATH`.
Run `taro --version`, then `taro run hello.tr` from the directory containing
your program. The Mac needs Apple Command Line Tools or Xcode for native
linking. The installed SDK provides its runtime and std from the same root.

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
dist/bin/taro fmt --check examples/
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

## Frontend-only checks

The `compiler` crate exposes semantic analysis with LLVM disabled. The caller
provides a target descriptor to `CompilerStore::new_for_analysis`. Generate the
descriptor with the native CLI, or use the matching
`lib/taro/runtime/target-facts.toml` from a Taro distribution. A cross-target
distribution places the descriptor alongside that target's runtime archive.

Run the same overload and diagnostic oracle with both compiler configurations.
The frontend-only run needs the descriptor file and a Rust toolchain.

```bash
make disk-guard
cargo test -p compiler compile::analysis_oracle
make compiler-release
git check-ignore -q target/frontend-test-target.toml
target/release/taro-bin target-facts target/frontend-test-target.toml
cargo tree -p compiler --no-default-features
TARO_TEST_TARGET_FACTS="$PWD/target/frontend-test-target.toml" \
  cargo test -p compiler --no-default-features compile::analysis_oracle
```

Set `TARO_TEST_TARGET_FACTS` to the copied descriptor when running on a machine
without a native Taro installation. The two test runs assert the same types,
exact overload locations, diagnostics and full-check work counts.

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
unfiltered native backtrace. Runtime scheduler, I/O, and native-task diagnostics are
available through `taro run --runtime-stats` and `--runtime-trace`.

## Explain allocations

Run `taro build app.tr --explain-allocations` on a script or a package. The
compiler writes placement decisions to stderr with a filename, line and
column. Named locals whose addresses are taken can stay on the stack, escape
through a return, store or call, or require separate storage across overlapping
lifetimes. A conservative decision is identified as such. Explicit managed
allocation sites also report their placement. Existential boxing reports the
concrete payload size in bytes for the selected target.

The first request for a report rebuilds any package whose cached object lacks
one. Subsequent reporting builds replay the decisions from metadata. Ordinary
builds can reuse those objects silently.

## Configure the Garbage Collector

GC programs read these variables at startup; invalid values abort with a
message naming the variable.

- `TARO_GC_PERCENT` (default `100`) collects once the heap grows by this
  percentage over the live data left by the previous collection, with a minimum
  heap goal of 4 MiB; `0` to `10000`, or `off` to disable percentage pacing.
  An explicit soft memory limit can reduce that goal. When this is unset, the
  goal can grow up to 16 times while collections take over 2% of the time.
- `TARO_GC_MARK_THREADS` (`1` to `256`) marks on this many threads in every
  collection. When this is unset, marking uses one thread until a collection
  marks 16,384 objects, then up to one per mutator thread, at most 8 and at most
  the available parallelism.
- `TARO_GC_MEMORY_LIMIT` (default `off`) is a soft heap limit in decimal bytes
  with a `B`, `KiB`, `MiB`, `GiB`, or `TiB` suffix. Before the heap grows past it
  the collector runs; if live data still needs more room, the heap exceeds the
  limit rather than failing.
- `TARO_GC_STRESS=1` collects before every allocation and at every safepoint,
  poisons freed memory and verifies the heap after marking. It is a debugging
  mode, far slower than normal execution.
- `TARO_GC_TRACE=1` prints one line per collection to stderr:

  ```text
  gc 3: pause 0.215ms, heap 4194304 -> 1048576 bytes (goal 2097152), freed 1234 objects, reserved 8388608 bytes, total pause 0.640ms
  ```

  `heap` is allocated-but-unfreed bytes before and after the collection, `goal`
  the heap size that triggers the next one, and `reserved` the mapped heap.

Small objects use 51 size classes through 8 KiB, with sizes and multi-page span
geometry adapted from Go 1.26.2. Class selection preserves each descriptor's
alignment; an over-aligned request can use a larger class. Larger objects use
whole 8 KiB pages. The adapted tables' attribution is in `runtime/GO-LICENSE`,
which is included with the SDK runtime.

The collector releases completely empty segments, retaining one arena. Within
remaining segments, it keeps at most 1 MiB of free pages ready for reuse, bounded
by the next collection's allocation headroom. This avoids repeated page faults
without retaining a historical heap peak. The reserve shrinks near the soft
memory limit and reaches zero when the mapped heap meets that limit. Reused
objects are still zeroed before publication.

Programs can read the same counters with `std::runtime::gcStats()` (collections,
heap, reserved and goal bytes, cumulative allocated/freed bytes, total and last
pause), and force a collection with `std::runtime::collect()` for tests and
benchmarks; neither is needed for correctness. `taro run --runtime-stats`
reports pause percentiles and phase times alongside scheduler counters.

Allocation never returns null. A request larger than `isize::MAX` bytes panics
with `allocation size overflow`, and a heap that cannot grow after a collection
panics with `out of memory`; like any panic, either can be observed through a
task's result.

## Benchmarking

`taro bench` runs synchronous, non-generic `@bench` functions with exactly one
`&std::bench::Benchmark` parameter and a unit result. As with
[test functions](testing.md#language-tests), the return-type annotation may be
omitted, written as `-> ()`, or use a unit type alias. The parameter cannot be
defaulted or variadic. Benchmarks compile in release/O2 by default and each
selected case runs in a fresh process.

```bash
taro bench my-package
taro bench my-package --list
taro bench my-package --filter parse --tag smoke
taro bench my-package --warmup 500ms --time 2s --samples 30
taro bench my-package --format json
```

Use `std::hint::blackBox(value)` as a best-effort optimizer barrier.
Keep benchmark results observable and use `std::runtime::keepAlive` when an
unsafe native operation needs an explicit liveness use. GC liveness follows
actual uses rather than lexical scope, and dropping a local does not run a
language destructor. Native requests retain storage until completion.
`taro bench --help` documents the measurement and timeout controls.

The harness summarizes completed samples after timing ends. It reports the
median, nearest-rank 95th percentile, and median absolute deviation in
nanoseconds per operation. The JSON report also includes samples in
measurement order.

Repository tooling also provides compiler and showcase diagnostics:

```bash
python3 development/scripts/benchmark_timings.py examples/hello.tr --runs 10
make codegen-benchmark RUNS=10
make -C showcase/monkey host-benchmark
```

The first command measures cold compiler phases. The codegen benchmark compares
the release baseline with O2, verifies equivalent output, and reports compile
time, runtime, and executable size. The Monkey host-gap suite runs matched Taro
and Go workloads for dictionary/environment lookup and churn, argument lists,
successful `Result` propagation, and small allocations. It verifies checksums
before reporting median time and available allocation counters; see
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
