# Monkey Host Benchmarks

These paired Taro and Go workloads isolate operations used by the Monkey
tree-walking evaluator. They are diagnostics, not substitutes for the complete
Monkey benchmark.

| Case | Measures |
| --- | --- |
| `dictionary_lookup` | String hashing and dictionary lookup |
| `environment_lookup` | Local and enclosing environment lookup |
| `environment_churn` | Scope and dictionary construction |
| `argument_list` | A returned two-element dynamic list |
| `result_success` | Successful `Result` propagation across call boundaries |
| `small_allocation` | One escaped pointer-sized allocation |

The fixtures keep equivalent algorithms and checksums in both languages. Each
sample runs in a fresh process, and the harness alternates language order.

```bash
make -C showcase/monkey host-benchmark
make -C showcase/monkey host-benchmark RUNS=9
make -C showcase/monkey host-benchmark QUICK=1
make -C showcase/monkey host-benchmark HOST_BENCH_ARGS='--case result_success'
```

Taro runs in release/O2 mode with one worker and runtime statistics. Go uses its
normal release runtime. The report includes elapsed medians, allocation counts,
allocated bytes, collections, and Taro GC pause summaries. Runtime settings
otherwise inherit the calling environment. Taro allocation counters cover the
whole process, including startup and reporting work; Go counters cover the
measured workload. Compare scaling across iteration counts to separate fixed
overhead from per-iteration allocation.

Compare allocation scaling before interpreting elapsed time. A zero-allocation
gap points to hashing, probing, calls, or ABI cost; proportional allocation
growth points to placement or runtime cost. Compare only matching cases on the
same machine and compiler revisions.
