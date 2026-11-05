# Large JSON corpus comparison

Compare fresh complete DOM construction in Taro, Swift, Rust and Go on six
real documents from [yyjson_benchmark](https://github.com/ibireme/yyjson_benchmark).
`fixtures.json` pins the upstream revision, file lengths and hashes, including
its MIT license. Downloads and all generated measurements stay in ignored
`target/json-corpus/`. Do not commit them. The corpus includes Canada geography,
a concert catalog, GSoC descriptions, Chinese poetry, mobile-game configuration
and a font dump; documents range from roughly 1.7 to 66.4 MB.

Every program accepts up to **100 MiB**. This is a benchmark configuration;
it does not increase the installed JSON API's default budget.

Run from the repository root on macOS, with Go, Swift and Rust installed:

```sh
python3 development/benchmarks/json/corpus/run.py prepare
python3 development/benchmarks/json/corpus/run.py build
python3 development/benchmarks/json/corpus/run.py check
python3 development/benchmarks/json/corpus/run.py calibrate
python3 development/benchmarks/json/corpus/run.py measure
python3 development/benchmarks/json/corpus/run.py audit
python3 development/benchmarks/json/corpus/report.py
python3 -m unittest discover -s development/benchmarks/json/corpus -p 'test_*.py'
```

Builds are serial and finish before measurement. Rust dependencies are pinned by
the lockfile; the build expects them in Cargo's cache (`--offline --locked`).
Taro uses release/O3 application code and the installed SDK's std configuration.
The current std sources are built in a disposable SDK, leaving the installed
SDK unchanged. Swift uses `-O -whole-module-optimization`, Rust release/O3, and
Go its normal optimized build. Programs use one Taro worker / Go processor.
Save toolchain versions and installed SDK identities beside executable hashes.

## Workloads and correctness

DOM cases use public Taro `parseWithOptions`, Foundation `JSONSerialization`,
`serde_json::Value` and Go `encoding/json` into `any`. A Python oracle rejects
duplicate keys and validates whole-tree counts, decoded UTF-8 byte totals, depth
and root size. Each native program traverses the complete result outside timing.
Taro and Go explicitly collect while that result remains alive before traversal.
These checks cover all fixtures before timing; they are structural checks, not
byte-for-byte equivalence or a JSON conformance suite.

Canada additionally compares complete typed decoding, including all strings and
all coordinate arrays, using nested dynamically sized arrays of Float64 across
all languages. Validation checks every coordinate and its numeric checksum.
Taro separately labels its public single-pass typed decoder and its explicit
validation-first option. No field projection, fixed-pair representation,
predecoded value, reusable destination or specialized geometry parser is used.

The default DOM representations differ: Taro retains exact numeric text and can
share immutable input strings; the other DOMs generally convert numbers and own
strings. Taro objects retain member order and index larger parsed objects, Rust's
serde_json uses its default sorted map, and Go/Foundation use their own maps.
Wide-object parsing and numeric-heavy parsing therefore exercise different work.
Treat this as a comparison of available API implementations, not an isolated
scanner or language ranking.

## Timing and memory

File reading, validation and calibration are outside operation timings. Taro
and Rust receive their native UTF-8 string inputs; Go and Swift receive byte
buffers/Data. Input preparation is excluded for all four. Each process warms up once. Taro and Go collect once before counters/timing, then use
normal GC without forced collections between operations. Each operation builds
a fresh full result and releases it from application scope. Rust destruction and
Swift ARC/autorelease cleanup occur within the operation; Go/Taro collection
work is included when triggered. The input remains alive. A root-size checksum
and result lifetime barrier prevent discarding the parse. Reporting occurs after
all samples, using preallocated sample storage.

Calibration chooses 1–128 parses per sample, targeting about 100 ms. Three
rounds rotate language order; each process records five samples. Summaries use
the median of the three round medians, retain their range and all raw samples.
Large files may exceed the target even with one parse. The runner requires three
quiet observations, checks before/after every process (load <=4, CPU idle >=70%),
rejects busy end observations, and resumes saved progress when rerun. Guards are
snapshots and cannot rule out brief interference. Each process has a 180-second
wall limit and 4 GiB process-tree RSS limit. Do not build or profile during timings.

Allocation audits are separate runs of one and two parses. Go uses MemStats loop
deltas. Taro uses loop GC stats for bytes/collections/pause and a difference of
whole-process allocation counters for an estimated allocation count; input,
warmup and reporting cancel, subject to small reporting variation. Rust uses a
separate counting-allocator build, counting successful alloc/alloc_zeroed/realloc
requests and their requested bytes, with no counter overhead in the timing binary.
Definitions differ: cumulative allocation bytes are not live memory or peak RSS.
Swift cumulative counters are unavailable here; tracing collections are N/A for
ARC and Rust. Peak RSS includes file input, runtime setup and warmup. Darwin CPU,
instruction and cycle counters likewise cover the whole process, not just parse
loops. Go pause time omits concurrent GC CPU/assists and is not a total GC cost.
