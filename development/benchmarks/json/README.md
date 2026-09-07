# JSON parser benchmarks

These first-party benchmarks measure the public `std.json` DOM parser without depending on an
external corpus. Every input is generated deterministically before timing begins, parsed and
stringified once as a smoke check, and then parsed afresh inside each measured iteration. DOM
allocation and any GC work triggered during measured batches contribute to the result;
dropping a result does not synchronously reclaim its garbage-collected storage.

Run all cases in the benchmark harness's default release/O2 configuration:

```sh
make json-benchmark
```

Forward normal harness options through `BENCH_ARGS`:

```sh
make json-benchmark BENCH_ARGS='--filter Wide --time 2s --samples 30'
```

For a machine-readable report, build first and invoke the compiler directly so
Make's recipe output is not mixed into the JSON:

```sh
make dist
mkdir -p target
TARO_HOME="$PWD/dist" dist/bin/taro bench development/benchmarks/json \
  --std-path std --format json > target/json-benchmark.json
```

The workload shapes are deliberately diagnostic rather than a composite score:

- a small application-shaped object captures fixed per-call overhead;
- a medium nested catalog exercises mixed objects, arrays, strings, numbers, and booleans;
- a 256-member unique-key object exposes object insertion and path bookkeeping costs;
- a 64 KiB unescaped ASCII string isolates the common string scanner;
- escaped Unicode strings exercise escape decoding and UTF-8 validation; and
- the medium catalog through a 7-byte `Reader` exercises refill and boundary handling.

Human output reports median, p95, MAD, iterations per sample, and throughput. Compare the same case,
compiler revision, hardware, power state, and harness policy; do not compare unlike workload names
or treat small differences below run-to-run noise as meaningful. Machine-readable output and local
baselines belong under the ignored `target/` tree and should not be committed.
