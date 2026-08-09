# Code Generation

Taro lowers typed source through HIR, THIR, MIR, and LLVM IR. LLVM performs
instruction selection and native optimization.

## Profiles

- Debug builds use the baseline pipeline and retain overflow checks.
- Release builds use O2 and disable overflow checks.
- `-O0`, `-O1`, `-O2`, `-O3`, `-Os`, and `-Oz` override LLVM optimization.
- `--overflow-checks` and `--no-overflow-checks` override the profile default.

Functions containing compiler stack maps use SelectionDAG. Rootless O0
functions may use GlobalISel on supported AArch64 targets.

## MIR Pipeline

Each body has three forms:

1. **Canonical MIR** is locally cleaned and is the input to MIR inlining.
2. **Shared MIR** has completed inlining, lowering, propagation, coalescing,
   and cleanup.
3. **Instance MIR** is finalized for concrete generic arguments with escape
   placement and safepoints before LLVM lowering.

Canonical and shared MIR are stored in dependency metadata. Instance MIR and
escape summaries are session-local, so source and cached dependencies use the
same finalization path.

The MIR inliner is deterministic. It does not inline recursive call-graph
edges, always respects `@noinline`, and treats `@inline` as a profitability
override rather than permission to violate ABI, depth, or growth limits. MIR is
the only stage allowed to inline across a collecting operation.

Escape analysis is keyed by concrete `Instance`. It follows references through
assignments, aggregates, control-flow joins, cleanup edges, and resolved direct
calls. Nonescaping managed allocations use stack storage. Unresolved indirect,
virtual, C, and blocking calls remain conservative. Field projections share
their base local, and overlapping loop allocations remain managed.

## Safepoints and Roots

Calls have one GC effect: `NoGc`, `ManagedSafepoint`, `RuntimeSafepoint`, or
`BlockingSafepoint`. Runtime entries must declare their effect. Managed bodies
receive an entry poll and enough loop polls to cover every CFG cycle.

Each collecting site records only initialized locals live at that site. Calls
retain values live across normal and cleanup continuations; runtime and
blocking calls also retain published GC-bearing arguments. Allocations retain
values live after the allocation. `std.runtime.keepAlive(value)` extends
liveness without emitting a call.

Aggregate fields are evaluated before their contiguous stores. A compiler-only
publication marker makes a completed tuple, struct, or closure visible to root
analysis. Enum payloads are stored before their discriminator. No safepoint may
split either publication sequence.

Every physical LLVM function containing a collecting site is `noinline`, has
tail-call elimination disabled, and includes synchronous unwind metadata. This
also applies to rootless polls: the collector must preserve and traverse the
physical frame. Functions without collecting sites remain eligible for LLVM
inlining.

## PC Metadata

Native Taro objects have a linked `.pcmeta.o` sidecar generated from LLVM stack
maps. The runtime consumes Taro's normalized format, not LLVM's experimental
section.

Each collecting frame publishes a nonzero selector before its stack-map anchor.
The return PC identifies the function; the selector identifies the executed
site. Sites sharing a machine address remain separate, preventing roots from
mutually exclusive paths from being combined.

Stack, heap, static, and buffer scanning share an indexed typed-layout graph.
It supports pointers, references, aggregates, fixed repeats, and tagged
variants. Tagged layouts scan only the active variant, and niche-pointer
optionals use their native representation. Raw and interior pointers are strong
roots resolved to their containing managed allocation. Static roots register an
address and exact descriptor.

## Outputs and LTO

`taro build` produces a native executable. `--emit llvm-bc` instead writes
verified, optimized package bitcode:

```bash
taro build examples/arithmetic.tr --release
taro build examples/arithmetic.tr --release --emit llvm-bc -o arithmetic.bc
```

Bitcode output is terminal and cannot be combined with LTO. Native builds
support:

| Mode | Behavior |
| --- | --- |
| `--lto off` | Compile packages independently |
| `--lto full` | Optimize participating package bitcode as one module |
| `--lto thin` | Import across packages with parallel cached backends |

Attached std, the Rust runtime, and native libraries remain optimization
boundaries.

## Incremental Builds

Incremental reuse is enabled for `build`, `run`, `test`, and `check`. Cache keys
include profile, target, compiler, options, source, and dependency metadata.
Artifacts live under `target/<profile>/`; `--no-incremental` bypasses reuse.
`.taro_meta` is an internal format and incompatible metadata is rejected.

## Attached Standard Library

The compiler loads target-specific std metadata and native code from:

```text
$TARO_HOME/lib/taro/std/<target-triple>/std.taro_meta
$TARO_HOME/lib/taro/std/<target-triple>/std.o
```

Rebuild `dist/` after compiler or metadata changes. To build std from source
explicitly:

```bash
TARO_HOME="$PWD/dist" \
  dist/bin/taro check examples/hello.tr --std-path std --build-std
```

## Cross-Compilation

`--target` selects LLVM output, std, runtime, and linking. Runtime archives have
an adjacent manifest containing their ABI, target, architecture, and checksum.

```bash
python3 development/scripts/build_dist.py --target x86_64-apple-darwin
```

Same-OS Darwin cross-architecture links use the host SDK. Linux cross targets
require a compatible linker or sysroot; cross-OS builds require both.
