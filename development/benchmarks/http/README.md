# HTTP benchmark programs

`body_collect.tr` isolates streaming-body collection into a string. Build with
release/O3 against the std being evaluated. Run, for example, with arguments
`65536 64` or `1048576 8`. It constructs the input outside timing, verifies all
bytes during warmup, forces one initial collection, then measures repeated
fresh body streams under the normal GC policy. The checksum and lifetime
barrier keep each complete collected result observable. Bytes are cumulative
allocated bytes, not peak memory. This is not a network throughput benchmark.

`stress.py` runs prebuilt servers through framework-benchmark levels: JSON at 16
to 512 connections, pipelined text at 256 to 16,000, then `/app` (a 1 ms wait and
a 20-record serialization), connection churn, idle connections beside live traffic
and a soak. Levels and the pipeline depth follow TechEmpower's JSON and plaintext
tests, without its `Server` header requirement. Build the servers first; results
and server logs go to ignored `target/http-stress/`:

```
dist/bin/taro build development/benchmarks/http/servers/taro.tr --release -O3 -o target/http-stress/taro-server
python3 development/benchmarks/http/stress.py --scenarios idle,json,plaintext,app,churn
python3 development/benchmarks/http/stress.py --languages taro,rust --scenarios soak
```

macOS gives every server a 128-entry accept queue, so connection bursts there can
reset clients on any server that accepts too slowly. Use Linux to judge that limit.

For comparisons, build both binaries before measuring. Alternate them on the
same machine, retain CPU/load observations and raw samples in ignored target
storage, and compare medians/ranges. Validate identical checksums. Never time
while building or profiling. Respect the repository's disk and process-tree
memory limits. Do not commit result datasets or historical timing tables.

Full HTTP comparisons must use a fixed independent peer for client and server
measurements. Label connection-per-request versus persistent connections,
concurrency, HTTP version, body buffering, TLS and framework/backend versions.
Client and server socket I/O use Taro's reactor; DNS uses the bounded blocking
pool. HTTP/1.1 keep-alive defaults to enabled. Compare equal settings on every
peer, and label isolated server/client runs separately from loopback tests.
Measure payload correctness, throughput, latency percentiles, CPU, allocation bytes/counts,
collections and peak RSS separately from setup and correctness traversal.
Use `python3 development/benchmarks/http/allocations.py --out <ignored-directory>
--artifacts <directory>` to attribute managed and native allocations per request
by call stack. It links a runtime built with the `alloc-profile` feature and
rebuilds attached std, so its counts reflect the working tree. Unwinding makes that
build far too slow for timing: use its counts, never its throughput.

Use `python3 development/benchmarks/http/profile.py --artifacts <directory>`
for a separate macOS native stack sample under c32 load. Its warmup and sampled
load stay outside the timing campaign; idle thread samples are not CPU cost.

`roundtrip.tr <bytes> <iterations> <keepalive: 0|1>` measures sequential plain
HTTP/1.1 exchanges with both endpoints in one Taro process. Inputs are bounded
multiples of 16 bytes. Setup, warmup, complete payload comparison, initial GC and
shutdown are outside timing; output includes the byte-length checksum and GC
allocation/collection deltas. Build release/O3 and pin worker counts. This is a
combined loopback diagnostic, not an isolated server or client league table.

## Framework server comparison

The `servers/` programs have ordinary GET handlers for three identical payloads:
`/text` returns 13 plain-text bytes, `/json` encodes a one-field value on every
request, and `/json-static` returns the same 27 JSON bytes pre-encoded. The
static endpoint separates HTTP overhead from serialization. No routing cache,
hand-written encoder, compression, TLS, pipelining or database work is added.

| Language | Stack | Dynamic JSON encoder |
| --- | --- | --- |
| Taro | std HTTP, release/O3 | Derived Codable + std JSON |
| Python | Starlette + Uvicorn, uvloop/httptools | Starlette JSONResponse / Python json |
| Go | net/http, standard optimized build | encoding/json.Marshal |
| Rust | Axum/Tokio, release | Axum Json / serde_json |
| Swift | Hummingbird/SwiftNIO, release | ResponseEncodable / Foundation JSONEncoder |
| Node.js | Native node:http, one event loop | JSON.stringify |
| Bun | Native Bun.serve, one event loop | Response.json |

The manifest/requirements inputs pin the top-level reference versions. Build
copies, transitive lockfiles, binaries, identities and raw results go into
ignored storage. Builds are serialized with one build job, 4 GiB process-tree
RSS guards and bounded wall time. The builder expects `uv`, Go, Rust, Swift,
Clang, Node.js, Bun and an existing OpenSSL installation for wrk. It does not change system
packages. Run from the repository root after installing the Taro release SDK:

```sh
python3 development/benchmarks/http/build.py
python3 development/benchmarks/http/compare.py --preflight-only --gc-stress --languages taro
python3 development/benchmarks/http/compare.py --workers 1 --connections 1,32 --rounds 3 --seconds 5
```

Use the same `--artifacts <ignored-directory>` on each command to select another
campaign. `build.py --openssl ... --python ...` selects tool dependencies.
`identities.json` records actual resolved packages, toolchains and executable
hashes; do not rebuild during timing. Interrupted timing campaigns resume saved
rows only when configuration and artifact identities match. Build after changing
program sources; a previous campaign with different identities needs a separate
artifacts directory.

Before timing, the runner validates exact bodies, Content-Type, repeated requests
over one physical connection and concurrent requests. Timed load uses pinned
wrk without a per-response Lua callback; wrk protocol/status/timeout errors are
rejected, and full payload validation is repeated afterward. Each trial uses a
fresh server, a five-second warmup (including JS JIT work), then a measured interval. Language order
rotates across rounds. This is a closed-loop throughput/latency comparison,
not an open-loop tail-latency guarantee. The load generator is on the same Mac;
its CPU usage is recorded and possible saturation is flagged.

The campaign starts only after three observations 30 seconds apart show
one-minute load <=4 and CPU idle >=70%. Between trials current CPU idle must
recover; the recorded trailing load also includes earlier benchmark trials.
Server CPU, instruction and cycle deltas come from macOS process-tree counters, alongside
sampled RSS and lifetime peak footprint. All process trees stay under the 4 GiB
campaign guard. One runtime worker is the default. Swift's setting controls NIO
loops; its separate concurrency executor can use additional threads, so CPU
consumption must accompany throughput comparisons. The results describe these
implementations/frameworks, rather than isolating language execution speed.
Deadline policies also differ: Taro enforces request-read, handler and write
timeouts, and isolates handler panics in a child task per request. With a
handler timeout of a second or more, that child gets its first poll on the
connection task's stack, under its own task identity and panic boundary. Before
registering with the reactor, a connection waiting for its next request retries
the read a bounded number of times, yielding to other runnable work between
attempts, and backs off when its peer doesn't answer that soon. Over loopback this
removes reactor wakeups for fast peers, which a remote peer's round trip wouldn't
benefit from, so low-concurrency loopback results don't carry over to real networks.
With several workers, connections gather on one worker until tasks wait about a
millisecond for a turn, and the rest sleep. That worker also reads the reactor,
sleeping in it when idle, so a wake crosses no second thread. Busy cores slow each other on the
benchmark machine, load generator included, so compare CPU as well as throughput,
and vary wrk's thread count: it changes which side the machine's fast cores go to.
Plain socket reads and buffered writes bound their waits
directly; TLS and streaming bodies use child tasks as well. The references use
ordinary framework handlers; Go configures header/idle timeouts, without
`http.TimeoutHandler`. Matching payloads and keep-alive does not normalize
these policies. Keep this distinction when attributing scheduler overhead.
Node and Bun use one process/event loop; campaigns including them require
`--workers 1`. Java is omitted when no actual JDK is installed; the macOS Java
launcher alone does not count as an installation.

For a focused Taro before/after comparison, copy the original server to
`<artifacts-parent>/taro-before`, record its hash in the campaign identities,
then include `taro-before` in `--languages`. Keep the baseline binary intact
when rebuilding the candidate. `--warmup-seconds` records an explicit warmup
override in the resumable campaign configuration.
An optional `taro-metadata` binary/label can isolate compiler metadata changes
from a subsequent runtime change; record both binaries' identities too.
The `taro-runtime` binary/label can similarly compare a runtime-only intermediate
with later HTTP/std changes. Keep every measured binary and its hash intact.

Go/Taro `/stats` snapshots also expose managed allocation bytes, collections and
GC pause time outside the timed load. Counter definitions differ, native
allocations are excluded differently, and small snapshot-query overhead remains
in the deltas. Cumulative allocated bytes are not peak memory. Python cycle-GC
and Rust/Swift ownership mechanisms are not assigned comparable collection
counts. Keep generated timing tables and raw samples out of this README/Git.
Go's pause counter measures its stop-the-world intervals, excluding concurrent
GC work; Taro currently performs marking and sweeping during its pause. A pause
ratio therefore is not a ratio of total GC CPU cost. See the
[Go GC guide](https://go.dev/doc/gc-guide).

`diagnose.py --artifacts <directory> --endpoint text` runs a separate bounded
load for Taro and Go. The Taro server's optional lifetime argument enables a
normal exit with `TARO_RUNTIME_STATS=1`, exposing managed allocation counts,
task/poll/timer counts and individual GC phases. Taro's diagnostic totals include
startup, two validation requests and drain; Go uses snapshots around the load.
`--taro-variant taro-metadata` diagnoses the optional intermediate binary too.
Treat per-request diagnostic ratios as approximate, and use the regular timing
campaign's snapshot deltas for steady-state allocated bytes and pause time.
Do not mix diagnostic/profiled load results into the throughput table.

`format.tr` isolates the `/app` handler's record-label formatting from networking,
timers and JSON encoding. Build it with the same SDK as the server:

```sh
dist/bin/taro build development/benchmarks/http/format.tr --release -O3 -o target/http-format/format
target/http-format/format 1000000
```

One million iterations must produce checksum `8500000`. The probe reports loop
time in nanoseconds, cumulative managed allocation bytes and collection count;
printing the counters is outside that interval. Preserve before/after binaries,
alternate their execution order, and keep raw results in an ignored directory.

The Taro, Go and Rust servers also provide four `/app` decomposition routes.
Every route returns the same 20-record JSON body:

| Route | Work before returning the response |
| --- | --- |
| `/stage/static` | Use pre-encoded record JSON |
| `/stage/sleep` | Sleep for 1 ms, then use that JSON |
| `/stage/encode` | Construct records, format their labels and encode them |
| `/app` | Sleep for 1 ms, then construct, format and encode |

This separates HTTP baseline, suspension and record construction. A requested
1 ms sleep is a lower bound; runtime timer precision affects throughput at low
concurrency. Differences between routes are diagnostic, not an additive cost
model: suspension can change scheduling, batching and GC behaviour.

For a focused comparison, build these three servers into an ignored directory as
`taro-server`, `go-server` and `rust-server`, retaining the resolved Rust lockfile
and binary/toolchain identities. Then run from the repository root:

```sh
python3 development/benchmarks/http/stages.py --out target/http-stages
```

The macOS runner validates all four payloads, rotates three language/route rounds
at c64 by default, records process CPU and instructions, and rejects socket/status
errors. Use `--connections 96` for a higher-concurrency control and `--rounds N`
for one to five rounds; the saved campaign identity includes both settings.
Go/Taro allocation-byte and collection counters are measured separately using
10,000 exact-body responses. Counter snapshots can include the diagnostic
request itself and are not peak-memory measurements. The output directory also
needs the three binaries; the existing comparison artifacts provide wrk and the
process-counter helper. Run the entire script through the standard 4 GiB,
bounded-wall-time benchmark guard. Changed binaries require a new output directory.

The same four routes are implemented by Node's HTTP server, Bun.serve,
Starlette/Uvicorn and Swift/Hummingbird. For the seven-language comparison, use
the artifact layout produced by `build.py` and run:

```sh
python3 development/benchmarks/http/stages.py --out target/http-all-stages \
  --artifacts target/http-all-stages/references --connections 96 --rounds 2 \
  --languages taro,go,rust,swift,node,bun,python
```

Configure four workers for Taro, Go and Rust, four Uvicorn worker processes, and
four Swift NIO event loops. Swift's global concurrency executor is separate from
those loops; Node and Bun use their normal single event loop. Report process-tree
CPU and RSS, especially for Uvicorn, rather than counters from its supervisor
alone. This is a framework/implementation comparison, not equal thread counts.
Use `--workers 1` or `--workers 2` for controlled worker-count comparisons;
Node and Bun remain single-event-loop servers regardless of that setting.
Payload checks accept JSON object-key reordering, validate all record values and
their array order, and verify a second exchange on the same physical connection.
The static payload is prepared once; dynamic routes construct and encode fresh
records on every request. All sleep routes request 1 ms, whose actual delay can
differ between runtimes. Counter trials remain limited to Go and Taro.
For a tail-latency confirmation, pass a route subset such as `--routes /app`
and use a new output directory. Retain the original samples, including outliers,
and report confirmations separately rather than replacing an inconvenient run.

For CPU attribution, profile separately from the timing campaign:

```sh
python3 development/benchmarks/http/profile.py \
  --artifacts target/http-all-stages/references --language taro --endpoint app \
  --connections 96 --workers 4 --profiler time-profiler --out target/http-profile/taro-w4
```

`--profiler time-profiler` uses Instruments' running-CPU samples; the default
`sample` mode observes thread stacks, including blocked waits. Sample weights
are statistical estimates rather than exact function durations. Keep inclusive
call-path shares separate from exclusive groups: allocation can appear inside
formatting and JSON. On Apple Silicon, inspect core placement as well as retired
instructions before attributing CPU-time differences entirely to algorithms.
Use a fresh output directory for each profile. The helper's timings are perturbed
and must not be merged into the regular timing results.

`diagnose.py` accepts the same stage endpoints, `--workers` and `--out` for
separate allocation, task/poll, timer and queue-counter runs. Opt-in runtime
counters add atomic operations, so their timings are diagnostic only. GC phase
durations are wall time and must not be presented as total collector CPU time.

`format.go` and `format.rs` complement `format.tr`: each formats one million
ordinary `record N` labels and checks their total byte length. Go additionally
reports allocation counters; the Rust program uses the standard allocator without
instrumentation. Keep these timings separate from HTTP load and native profiles.

The Go reference normally uses plain `net/http`. Set `BENCH_HANDLER_TIMEOUT=1`
to wrap its mux with the standard 30-second `http.TimeoutHandler` for a separate
control. Taro already enforces a per-handler deadline. Go's wrapper buffers the
response and its timeout/cancellation behaviour is not identical to Taro's
cancel-and-drain contract; label this control separately, especially for streaming.
