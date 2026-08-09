# Monkey host-gap diagnostics

This suite compares small, equivalent Taro and Go programs that model the hot
operations in the Monkey tree-walking evaluator. It is diagnostic support for
the full Monkey benchmark, not a replacement for it. The Monkey implementation
must remain idiomatic and algorithmically comparable to the Go book code.

The paired fixtures deliberately use `noinline` boundaries around escaping
allocations and return ABIs. This prevents either compiler from erasing the
operation a case is intended to measure; it is not a proposed optimization for
Monkey itself. Every measured run is a fresh process, and the harness rejects
unstable or cross-language checksum results.

## Cases

| Case | Isolates | A large Taro/Go gap suggests |
| --- | --- | --- |
| `dictionary_lookup` | One direct string-key lookup in an existing table | String hashing or dictionary probing/value access |
| `environment_lookup` | Local and enclosing string-key lookup in an existing scope | Hashing, dictionary probing, value copying, or managed call/safepoint cost |
| `environment_churn` | An escaped child scope, its dictionary, one binding, and two lookups per iteration | Dictionary construction footprint, allocation throughput, or GC pacing |
| `argument_list` | A returned two-element dynamic list/slice | List buffer growth, temporary escape analysis, or aggregate return ABI |
| `result_success` | Three successful, non-inlined propagation boundaries | Generic enum layout/return ABI and propagation code, without intended allocation |
| `small_allocation` | One escaped, pointer-sized object | Allocator and collector throughput independent of collections or strings |

Use the cases together. For example, slow `environment_churn` with competitive
`environment_lookup` points at construction/allocation rather than lookup. A
matching per-probe allocation rate in `dictionary_lookup` and
`environment_lookup` locates lookup churn below the environment abstraction.
Slow `result_success` with near-zero allocation points at ABI/code generation,
while a similar gap in `small_allocation` points at the runtime.

## Running

From the repository root:

```bash
make monkey-host-benchmark
make monkey-host-benchmark RUNS=9
make monkey-host-benchmark QUICK=1
make monkey-host-benchmark HOST_BENCH_ARGS='--case result_success'
```

The harness builds both fixtures in release mode, alternates Taro/Go process
order, runs one unmeasured warmup by default, and reports medians for elapsed
time, allocation counts and per-iteration rates, allocated bytes, and
collections. Taro runs with
`TARO_WORKERS=1` and `TARO_RUNTIME_STATS=1`; other GC environment settings such
as `TARO_GC_PERCENT` are inherited so collector experiments remain possible.
Go runs with its normal runtime settings.

The default iteration counts target stable sub-second-to-few-second samples on
a development machine. `--quick` selects smoke-test counts; `--iterations
case=count` overrides individual cases. Run `--help` for all controls.

Allocation counters have slightly different observation windows. Go snapshots
`runtime.MemStats` immediately around the timed workload. Taro's runtime report
covers the root task, including the final structured print. Default counts make
that fixed reporting overhead negligible; do not use tiny iteration overrides
for allocation-comparison conclusions.

## Instance-aware escape checkpoint (2026-08-08)

The pre-change compiler was preserved in an isolated worktree and both states
were measured with the unchanged fixtures on the same Apple M2:

```bash
make monkey-host-benchmark RUNS=7
```

Each median contains seven fresh measured processes after one unmeasured
warmup. Taro used release/O2, `TARO_WORKERS=1`, and runtime statistics; Go used
its release defaults.

| Case | Before ms | Final ms | Before allocs/i | Final allocs/i | Before bytes | Final bytes | GCs before/final |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `dictionary_lookup` | 648.563 | 385.976 | 1.000 | 0.000 | 320,002,272 | 2,368 | 305 / 0 |
| `environment_lookup` | 2,758.137 | 1,200.289 | 6.000 | 0.000 | 1,200,003,776 | 3,680 | 1,137 / 0 |
| `environment_churn` | 351.487 | 253.229 | 13.000 | 5.000 | 404,002,400 | 324,002,384 | 381 / 306 |
| `argument_list` | 59.023 | 57.477 | 1.000 | 1.000 | 64,000,992 | 64,001,056 | 61 / 61 |
| `result_success` | 51.733 | 51.700 | 0.000 | 0.000 | 992 | 1,056 | 0 / 0 |
| `small_allocation` | 74.821 | 72.923 | 1.000 | 1.000 | 16,000,992 | 16,001,056 | 15 / 15 |

The final Taro/Go elapsed ratios are 12.13x, 8.86x, 6.87x, 2.81x,
1.63x, and 4.13x in table order. The three non-target cases retain their prior
allocation shapes and show no material timing regression.

Doubling each lookup workload confirms that the remaining counters are fixed
process overhead rather than hidden per-lookup allocation:

| Case | 5M allocations | 10M allocations |
| --- | ---: | ---: |
| `dictionary_lookup` | 41 | 42 |
| `environment_lookup` | 47 | 47 |

`environment_churn` loses exactly eight transient allocations per iteration.
Its remaining five are the escaped child `BenchScope` and the four initial
Dictionary buffers (`controls`, `hashes`, `keys`, and `values`). Changing that
Dictionary footprint is intentionally outside this checkpoint.

Final instance MIR for
`std.collections.hashKey<string>` contains a local `SipHasher13` and no managed
`Alloc`. Optimized LLVM contains a stack `alloca` for that hasher and no
`__gc__alloc` in the function; the string key remains an argument/local pointer
rather than a heap cell. This is the structural acceptance evidence behind the
allocation counters, not an inference from elapsed time.

No Monkey implementation source changed for this checkpoint. Dictionary
layout, SipHash intrinsics, aggregate ABI, List growth, allocator batching, and
GC pacing remain deferred pending a new measurement-driven plan.
