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
