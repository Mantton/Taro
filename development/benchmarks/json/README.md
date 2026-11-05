# JSON benchmarks

These first-party benchmarks measure public `std::json` parsing, typed conversion, encoding,
and object lookup without depending on an external corpus. Inputs are generated deterministically
and validated before timing. Encoding and lookup fixtures are parsed outside the measured region;
typed decoding uses the public single-pass decoder, including parsing and conversion. Allocation and GC work triggered during
measured batches contribute to the result. Dropping a result does not synchronously reclaim its
garbage-collected storage.

Run all cases in the benchmark harness's default release/O2 configuration:

```sh
make json-benchmark
```

Forward normal harness options through `BENCH_ARGS`:

```sh
make json-benchmark BENCH_ARGS='--filter Wide --time 2s --samples 30'
```

To audit the installed SDK without rebuilding or installing compiler changes, invoke it directly.
For release/O3 measurements:

```sh
TARO_HOME="$PWD/dist" TARO_WORKERS=1 dist/bin/taro bench development/benchmarks/json \
  --std-path std --release -O3 --warmup 250ms --time 1s --samples 20
```

Record the installed compiler, runtime, and std artifact hashes separately from the source revision.
Run serially on an idle machine; repeat measurements before attributing small differences to code.

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
- the medium catalog through 7-byte and 4096-byte `Reader` chunks distinguishes boundary handling
  from the cost of the Reader parser itself;
- 16-, 64-, 256-, and 1024-member objects expose object insertion scaling;
- the same 256-integer array through DOM parsing and typed decoding separates their total costs;
- typed-array encoding and DOM stringification cover output costs, including a 64 KiB ASCII string;
  and
- first, last, and absent member lookups use the same prebuilt 256-member object. Lookup cases do
  not report input-byte throughput because they do not consume a document per iteration.

Human output reports median, p95, MAD, iterations per sample, and throughput. Compare the same case,
compiler revision, hardware, power state, and harness policy; do not compare unlike workload names
or treat small differences below run-to-run noise as meaningful. Machine-readable output and local
baselines belong under the ignored `target/` tree and should not be committed.

## Derived record codecs and host references

`src/records.tr` compares a handwritten format-neutral codec, a derived struct,
and a derived final class. Each has `name: string` and `age: uint8`, measured as
one record and as an array of 128 records. Decoding starts from JSON text on every
iteration; encoding starts from a predecoded value and produces fresh output.
Every case checks an exact round trip before timing. Class decoding additionally
allocates an object per record, so compare it separately from inline struct values.

Build all three programs before timing. The installed SDK is sufficient; these
commands do not rebuild or install the compiler or standard library:

```sh
mkdir -p target/json-current
TARO_HOME="$PWD/dist" TARO_WORKERS=1 dist/bin/taro bench development/benchmarks/json \
  --std-path std --release -O3 --list -o target/json-current/taro-json
GOMAXPROCS=1 go build -o target/json-current/go-json \
  development/benchmarks/json/reference/main.go
CARGO_BUILD_JOBS=1 cargo build --release \
  --manifest-path development/benchmarks/json/reference/Cargo.toml \
  --target-dir target/json-current/rust-build
python3 development/benchmarks/json/compare.py \
  --taro target/json-current/taro-json --go target/json-current/go-json \
  --rust target/json-current/rust-build/release/json-reference \
  --output target/json-current/comparison.json
```

For a focused encoder before/after comparison, add `--encoding-only` and
`--baseline <unchanged-taro-binary>`. Compile and preserve the baseline before
changing std; finish all candidate builds and correctness checks before timing.
The runner rotates the baseline, candidate, Go and Rust through three rounds.
Use `--filter People128` to focus on the 128-record cases across all languages.

An optional Swift reference uses synthesized `Codable` and Apple's Foundation
`JSONEncoder`/`JSONDecoder`. Build it before timing, then use four rounds so each
language gets one turn first. `--taro-filter` selects derived structs without
filtering out the differently named reference cases:

```sh
swiftc -O -whole-module-optimization -swift-version 6 \
  -module-cache-path target/json-current/swift-module-cache \
  development/benchmarks/json/reference/main.swift -o target/json-current/swift-json
python3 development/benchmarks/json/compare.py \
  --taro target/json-current/taro-json --go target/json-current/go-json \
  --rust target/json-current/rust-build/release/json-reference \
  --swift target/json-current/swift-json --taro-filter DerivedStruct --rounds 4 \
  --output target/json-current/four-language.json
```

The comparison runner currently uses macOS CPU counters. It checks three initial
quiet-system observations, requires one-minute load at most 4 and at least 70%
CPU idle, then rechecks before and after each case. Each child has a 60-second
wall limit and a 4 GiB process-tree RSS limit. Busy runs stop with resumable data;
a case whose final observation is busy is discarded and retried on resumption.
Snapshots cannot exclude brief interference between observations.

Existing JSON cases run once with 20 samples each. Record cases run three rounds
by default, with rotating language order and 20 samples per round. Taro uses its normal
250 ms calibration and 50 ms target sample batches. Reference programs calibrate
until a batch reaches 100 ms, then target 50 ms batches. Compare medians of the
three round medians and their range. Do not include compilation, validation, or
calibration in reported per-operation times. The report records executable hashes;
record toolchain versions and installed SDK identities alongside it.

Go uses standard `encoding/json` with fresh destinations. Rust uses pinned
`serde`/`serde_json` with owned `String` fields and derived codecs. Neither reuses
an output buffer or a previously decoded record. Go produces bytes; Taro and
Rust produce strings. Taro decoded strings can share immutable input storage,
whereas the Rust reference owns its field strings. Garbage collection and Rust
destruction are included in measured batches. Reference input has unique keys,
ASCII strings, and in-range integers; these timings do not compare duplicate-key,
number, missing-field, Unicode, or DOM ordering policies.

Swift reuses the encoder/decoder configuration objects, with predecoded values
for encoding and fresh decoded values or output `Data` on every iteration. Its
default object-key order is unrestricted, so validation checks semantic round
trips and the exact compact output size rather than sorting keys to force byte
equality. Each timed Swift batch includes draining its autorelease pool; ARC
cleanup contributes to the sample. The result sink retains one last result, like
the Go reference. These are standard-library implementation comparisons on this
schema, rather than a general ranking of the languages.

## Allocation audit

Build the fixed-count diagnostic with the installed SDK and run the collector:

```sh
TARO_HOME="$PWD/dist" TARO_WORKERS=1 dist/bin/taro build \
  development/benchmarks/json/allocation_audit.tr --std-path std --release -O3 \
  -o target/json-current/allocation-audit
python3 development/benchmarks/json/allocation_audit.py \
  --binary target/json-current/allocation-audit \
  --output target/json-current/allocation-audit.json
```

This measures allocation rather than performance. Fixtures and output validation
are prepared before the operation loop. Loop-local `gcStats()` deltas exclude
setup and reporting from allocated bytes and collection counts. Allocation counts
come from slopes of whole-process runtime counters across three iteration counts;
they are rounded estimates because the final diagnostic formatting can vary by
one or two allocations. The collector retains raw slopes and validates linear
allocation bytes, encoded output, byte totals, and writer-call counts.

The cases separate shared builder/buffer construction, immutable-to-writable
string copies, direct writes into a reused buffer, integer formatting, returned
JSON strings, and encoding to a counting/discard writer. The discard writer is
an allocation diagnostic, not a proposed replacement for retaining output.

The implementation keeps these allocation costs separate:

- `Writer.writeString` is a full-write operation. Its default creates an
  independent writable copy for arbitrary byte Writers; `Buffer` overrides it
  through its existing inherent `writeString` method to append directly into its
  own capacity. Immutable string input also avoids the alias snapshots needed
  for writable-span writes. The free `io.writeString` function dispatches through this hook.
  Go's [`io.WriteString`/`StringWriter`](https://go.dev/src/io/io.go) provides
  precedent for a string-capable sink avoiding intermediate byte storage.
- Decimal conversion uses a fixed 20-byte local digit array. JSON numbers use
  private decimal helpers instead of printf's existential arguments, scratch
  formatter and field-padding machinery. General printf still preserves its
  scratch formatter semantics for custom Formattable implementations.
  [`serde_json`'s integer formatter](https://docs.rs/serde_json/latest/src/serde_json/ser.rs.html)
  likewise emits decimal digits without general-purpose format parsing.
- Typed and DOM encoders retain field names and array indices in their existing
  cursor frames. A private location view formats JSONPath only on an error.
  Container locations exclude the last selected child for separators and closing
  delimiters; key/value errors retain that child. Saved errors own independent
  immutable path strings after traversal continues.

Keep partial-write behavior, error priority, UTF-8 checks, retained writable spans,
string immutability, output snapshots, container validation, and GC rooting when
changing these paths. A mutable Span backed by immutable string storage or a
reused scratch allocation handed to a retaining Writer is not a safe substitute.

## Parser and transport diagnostics

`src/stages.tr` separates DOM parsing, one bulk write into existing capacity,
and the same document emitted through its literal token fragments. The token
cases validate exact output, with both a reused destination and fresh storage
plus a final snapshot. They intentionally omit escaping, container validation,
and decimal conversion to isolate transport; they are diagnostic programs, not
replacement JSON implementations. Compare them with the derived struct's full
encode/decode cases in rotating, serial runs using the same harness policy.
DOM parsing and single-pass typed decoding use different paths and storage
lifetimes. Subtracting their timings does not isolate conversion cost.

For profiles, keep profiling runs separate from timings. The Go and Rust reference
programs accept `JSON_BENCH_SAMPLE_NS` to extend each of their 20 sample batches.
Go additionally accepts `JSON_BENCH_CPU_PROFILE` for its standard runtime profiler:

```sh
GOMAXPROCS=1 JSON_BENCH_SAMPLE_NS=500000000 \
  JSON_BENCH_CPU_PROFILE=target/json-current/go-encode.pprof \
  target/json-current/go-json encodePeople128
go tool pprof -top -relative_percentages -focus=encoding/json \
  target/json-current/go-json target/json-current/go-encode.pprof
```

Use `decodePeople128` for decoding. On macOS, `/usr/bin/sample <pid> 3 1 -file
<ignored-output>` can capture a native profile while an extended Rust run is
active. Build a profile-specific Rust binary with `RUSTFLAGS='-C debuginfo=1'`
and the same release optimization policy to retain source/symbol information.
For Taro's prebuilt harness, select `TARO_BENCH_ACTION=run`,
`TARO_BENCH_CASE=encodeDerivedStructPeople128` (or its decode counterpart),
`TARO_BENCH_MEASUREMENT_NS=10000000000`, `TARO_BENCH_SAMPLES=20`, and an ignored
`TARO_BENCH_PROTOCOL_PATH`. Begin sampling after calibration; validate the result
protocol when the process exits.

`summarize_profile.py --kind encode --input <sample> --output <ignored-json>`
groups Taro's main-thread sample tree. Inclusive buckets overlap; exclusive
buckets prioritize collection, allocation, then named layers. Inlined work is
charged to its containing symbol. Go's CPU profiles and native main-thread wall
samples have different denominators; do not compare their percentages directly.
Darwin Go profiles may contain large systemstack/kevent entries; JSON-focused
stacks help inspect application hot paths without treating these wait frames as
JSON work. They do not establish the cause of unrelated system-stack samples.

## Large external documents

For complete DOM and typed Canada comparisons across Taro, Swift, Rust and Go
on megabyte-scale real documents, see [the corpus runner](corpus/README.md).
Its benchmark-only input budget is 100 MiB; raw downloads and measurements stay
under ignored `target/json-corpus/`.
