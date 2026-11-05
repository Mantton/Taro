# Dictionary operation diagnostics

These matched Taro, Go and Rust programs separate costs hidden inside Monkey's
environment construction. They use the default dictionary/hasher in each
language, the same static string keys, and inline values containing two `int64`
fields. Rust uses borrowed `&str` keys, avoiding owned-string allocation so this
measures the table rather than ownership of the input strings. This is a
diagnostic comparison, not a reproduction of each Monkey implementation's
object representation.

| Case | Timed work |
| --- | --- |
| `construct` | Create an empty dictionary and observe its length |
| `construct_insert` | Create, insert one binding, observe length |
| `first_insert` | Insert into prepared empty dictionaries |
| `insert_new` | Insert an absent key into prepared 1- or 16-entry dictionaries |
| `overwrite` | Replace existing values in one reused table |
| `hit` | Read existing keys from one reused table |
| `miss` | Read an absent key from one reused table |

Insertion-only cases prepare at most 1,024 tables before starting each interval;
preparation and checksum reads are excluded. They include allocations deferred
until insertion. Their phase timings cannot simply be added to `construct`:
object lifetimes, cache state, deallocation and GC placement differ. The combined
`construct_insert` case measures the complete lifecycle in a single interval.
Rust drops each constructed table within that interval; tracing collectors may
reclaim an unreachable table later. Both are their normal lifecycle behavior.

Lookup and overwrite visit the same keys in order. Case selection happens outside
the hot loops. All fixtures use explicit non-inlining boundaries. Rust also uses
`black_box` to prevent empty construction and identical misses from disappearing.
These boundaries add call overhead: timings are operations through these helpers,
not a minimum possible inlined lookup cost. Hashing, probing, value access and
compiler/runtime bookkeeping are all included; hashing is not controlled to be
identical across languages. There is no adversarial collision or growth stress
benchmark here.

## Reproduce on macOS

Use an SDK built from the checkout's std sources. Finish all builds before timing.
The scripts require macOS `/usr/bin/time -l` for CPU and hardware counters.

```sh
work=$(mktemp -d /tmp/monkey-dictionary.XXXXXX)
dist/bin/taro build development/benchmarks/dictionary_ops/main.tr --release -O3 --no-incremental -o "$work/taro"
go build -p=1 -pgo=off -o "$work/go" development/benchmarks/dictionary_ops/main.go
rustc development/benchmarks/dictionary_ops/main.rs -C opt-level=3 -C target-cpu=native -C lto=thin -C codegen-units=1 -o "$work/rust"
python3 development/benchmarks/dictionary_ops/run.py --taro "$work/taro" --go "$work/go" --rust "$work/rust" --output "$work/checks.json" --smoke --runs 1
python3 development/benchmarks/dictionary_ops/run.py --taro "$work/taro" --go "$work/go" --rust "$work/rust" --output "$work/samples.json" --runs 5
python3 development/benchmarks/dictionary_ops/verify.py --taro "$work/taro" --output "$work/gc-checks.json"
```

The runner rotates language order, checks every checksum, and records internal
elapsed times, whole-process CPU time/instructions/cycles/RSS, and load averages.
It uses one Taro worker and `GOMAXPROCS=1`, and removes GC stress/statistics and
Go GC overrides during timing. Keep unrelated compilation/profiling off the
timing machine. Hardware counters cover the whole process, so for batched
insertion they also include untimed preparation and verification.

For a before/after change, retain the unchanged Taro executable and add
`--baseline /absolute/path/to/before` to `run.py`; pass the candidate with
`--taro`. The output labels these `before` and `after`, and explicitly alternates
their relative order alongside the Go and Rust controls.

`verify.py` runs all cases with forced Taro GC at small iteration counts, then
uses 1,000/10,000-iteration counter differences to distinguish proportional
allocations from startup/reporting costs. These diagnostic runs are separate
from timing. Its insertion counters include untimed preparation; do not call
them insertion-only allocation counts.

## Fresh tree-walker profile

Build Monkey separately, finish the build, then run:

```sh
dist/bin/taro build showcase/monkey --release -O3 --no-incremental -o "$work/monkey"
python3 development/benchmarks/dictionary_ops/profile.py --binary "$work/monkey" --input /absolute/path/to/fib35.monkey --checksum 9227465 --output-prefix "$work/tree"
```

The input is the existing recursive Monkey Fibonacci workload. The sampler runs
for eight seconds, then waits for the checksum. The summary counts each category
at most once per stack, so recursive ancestors are not counted repeatedly.
Inclusive categories overlap: a constructor can include allocation, which can
include GC. Inlined work is attributed to its enclosing symbol. This is a
main-thread wall sample, including syscall waits, not an isolated CPU benchmark.
The parser streams the recursive call graph and retains only the current stack;
the large raw report is compressed after parsing.

Keep generated measurements and profiles in the ignored
`development/benchmarks/results/` directory or a temporary directory. Remove
disposable SDKs when finished; keep benchmark binaries and logs outside the
checkout.
