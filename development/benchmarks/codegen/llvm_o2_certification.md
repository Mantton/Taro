# LLVM O2 Release Certification

Date: 2026-07-13

Host: Apple arm64, macOS

LLVM: 22.1.8

## Policy under test

- Debug builds retain Taro's fast baseline (`mem2reg`) unless `-O` is explicit.
- Release builds default to LLVM's `default<O2>` module pipeline.
- The canonical attached standard-library artifact is built at O2.
- Explicit `-O0`, `-O1`, `-O2`, `-O3`, `-Os`, and `-Oz` continue to override the profile.
- The hidden `-Obaseline` control keeps the former release pipeline reproducible for compiler regression comparisons.

## Benchmark method

`development/scripts/codegen_benchmarks.py` built both variants with the release
profile and `--no-incremental`, alternated variant order for every sample,
warmed runtime execution once, and rejected output differences. Bootstrap time
was excluded. Five measured samples were collected per variant using
`optimizer_workload.tr`.

| Variant | Cold compile median | Warm runtime median | Executable size |
|---|---:|---:|---:|
| release baseline | 180.841 ms | 3726.116 ms | 2,850,256 bytes |
| release O2 | 188.116 ms | 3679.542 ms | 2,850,288 bytes |

Observed ratios:

- O2 runtime speedup: 1.01x
- O2 compile-time ratio: 1.04x
- O2 executable-size ratio: 1.000x
- Both variants printed `-8999169712941188607`.

These are local measurements, not portable performance thresholds. The harness
exists to make future comparisons reproducible and to catch output divergence.

## Optimization audit

LLVM's `inline` remarks confirm that O2 inlines ordinary Taro helper functions.
The workload's remaining hot loop still contains logical-stack push/pop calls
and GC polls inherited from the inlined callee and loop safepoints. Those
observable runtime calls dominate this microbenchmark and prevent more
aggressive loop transformations. Reducing that instrumentation safely is a
separate compiler/runtime optimization story; it is not folded into the O2
default change.

## Correctness gates

- Default-policy and attached-std unit tests: passed.
- High-risk debug/release codegen matrix using the promoted defaults: 54/54 passed.
- Full unified test pipeline: passed (10 development-script, 59 CLI, 465
  compiler, 22 LSP, 91 runtime, 343 standard-library, and 178 language tests;
  one standard-library test skipped).
- Additional non-incremental release-O2 standard-library suite: 343 passed,
  one skipped.

## Decision

Promote release builds and canonical attached std to O2. The measured size is
unchanged, runtime is non-regressing, compile overhead is modest for a cold
small program, and high-risk optimized correctness coverage is clean.
