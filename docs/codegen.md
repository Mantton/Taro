# Code Generation and Build Artifacts

Taro lowers typed source through HIR, THIR, and MIR before generating LLVM IR.
This document describes the user-visible build modes and artifact boundaries.

## Profiles and Optimization

Build profile and LLVM optimization level are independent:

- Debug builds use the fast baseline pipeline and retain overflow checks.
- Release builds use O2 and disable overflow checks by default.
- `-O0`, `-O1`, `-O2`, `-O3`, `-Os`, and `-Oz` override only LLVM's
  optimization pipeline.
- `--overflow-checks` and `--no-overflow-checks` override the language profile
  default.

LLVM owns instruction selection. On supported AArch64 targets, rootless O0
functions may use GlobalISel. Functions containing compiler PC stack maps use
LLVM's maintained per-function SelectionDAG fallback because GlobalISel does
not select `llvm.experimental.stackmap`; optimized builds use LLVM's maintained
target defaults.

## Canonical and final MIR

The compiler stores two MIR forms for every body, including synthesized async
constructors, poll thunks, and drop thunks:

- **canonical inline MIR** has completed local cleanup and async lowering, but
  has not run interprocedural optimization or inlining;
- **final codegen MIR** has completed global optimization, explicit allocation
  lowering, liveness-driven safepoints, and inlining.

Both forms are serialized in metadata format 28. Dependency loading hydrates
them into separate stores, and the MIR inliner reads only canonical bodies.
Consequently, an inline decision does not depend on whether a callee came from
source in the current build or from attached/cached metadata. Metadata retains
ordinary bodies through cost 115, the largest O3 threshold after loop and
constant-argument bonuses, as well as all explicit-inline and generic bodies.

MIR performs the only inlining that may cross a collecting site. It rejects
recursive-SCC edges, preserves `@noinline`, understands cleanup continuations,
and applies fixed profile-specific cost and growth budgets. LLVM may still
inline a physical function that contains no collecting operation. Any function
containing an entry/loop poll, managed or collecting-runtime call, allocation,
blocking transition, or panic site is marked `noinline` with LLVM tail-call
elimination disabled and a synchronous unwind-table entry after code
generation, even if precise liveness made every map at that site rootless. The
three constraints preserve and expose the physical frame assumed by PC metadata
and by managed-call root transfer.

## Output Modes

`taro build` normally produces a linked executable. Use `--emit llvm-bc` to
stop after verified, post-optimization LLVM bitcode:

```bash
taro build examples/arithmetic.tr --release
taro build examples/arithmetic.tr --release --emit llvm-bc -o arithmetic.bc
```

Bitcode output does not require the runtime archive, a linker, or a sysroot. It
is a terminal package-scoped artifact and cannot be combined with LTO.

## Link-Time Optimization

LTO is opt-in and applies to participating Taro packages:

| Mode | Behavior |
| --- | --- |
| `--lto off` | Compile packages independently and link native objects |
| `--lto full` | Merge user-package bitcode and emit one optimized native object |
| `--lto thin` | Import across package boundaries and run parallel cached backends |

```bash
taro build my-package --release --lto full
taro build my-package --release --lto thin
```

Attached std, the Rust runtime, and other native objects remain optimization
boundaries. Taro performs LTO inside the compiler, so the platform linker does
not need an LLVM plugin matching Taro's LLVM version.

Full LTO reuses package bitcode but regenerates the whole-program native object.
ThinLTO also maintains a profile-scoped backend cache under
`target/<profile>/objects/thinlto-cache/`. `--no-incremental` bypasses package
reuse and ThinLTO cache reads without deleting existing entries.

## Compiler PC Metadata

Every native Taro object has a compiler-owned stack-map descriptor and a linked
`.pcmeta.o` sidecar. After ordinary, full-LTO, or ThinLTO machine-code emission,
the compiler normalizes LLVM's target-specific stack-map records into the
versioned Taro format and strips the raw LLVM stack-map section from the native
object. The runtime never parses LLVM's experimental format.

The sidecar stores signed offsets relative to one module header instead of
absolute pointers. The linker resolves those differences statically, leaving
only the constructor's module pointer for the dynamic loader to rebase. Root
recipes, typed-layout nodes, root-location arrays, strings, and logical-frame
arrays are deduplicated within the sidecar. Nodes are copied into the PC object,
so that object never relocates against an internal node-table symbol from
another object. Runtime registration is constant-size; the first stack walk
indexes exact function address ranges.

Root storage is keyed by MIR `LocalId`. At each collecting operation the
compiler intersects temporal liveness with definite initialization and emits
only the applicable local subset. Calls retain values live across their normal
or cleanup continuation; runtime/blocking calls additionally retain their
GC-bearing arguments; allocations use values live after the allocation; polls
use values live at the poll. `std.runtime.keepAlive(value)` becomes a
compiler-only liveness use and emits neither a call nor another poll.

Aggregate lowering evaluates every field-producing expression before it writes
the destination. Tuple, struct, and closure fields are then stored contiguously
without a safepoint, followed by the compiler-only `SetInitialized(LocalId)`
publication marker. Definite-initialization analysis makes the whole local
scannable only after that marker; code generation emits no instruction for it.
Enums use their discriminator store as the equivalent publication event, with
the payload written first. This avoids both scanning partial aggregate storage
and dropping a completed aggregate from later root maps.

Every collecting site emits a machine record, including a rootless entry or loop
poll. Each collecting physical frame owns a selector slot. Immediately before a
site, generated code volatile-stores that site's nonzero selector and records
the slot as the first stack-map operand. The runtime reads the selector from the
parked frame and chooses the matching selector-table entry. The return PC only
identifies and bounds the physical function; machine-address order is not used
to identify a site. This remains correct when block layout places the executed
stack-map anchor after the return PC.

Records that optimize to the same machine PC remain distinct. In particular,
the compiler never unions typed roots from mutually exclusive control-flow
paths: doing so could interpret inactive enum or reference storage using the
wrong descriptor. Metadata validation requires one selector location per
function and identical GC semantics for machine duplicates of one selector.
Normalization collapses identical machine duplicates, then stores one strictly
selector-ordered entry per source site for binary runtime lookup. A missing or
invalid selector fails closed with the function and offset in the diagnostic.

Rootless sites still keep the physical LLVM function `noinline` with tail-call
elimination disabled and synchronous unwind metadata. The unwind entry lets the
stop-the-world stack walker cross that frame to mapped callers.

PC metadata schema 5 and pending-descriptor schema 3 encode the selector and one
indexed, tag-aware layout graph shared with heap, static, and buffer scanning.
Its node kinds are `Pointer`, `Reference`, `Aggregate`, `Repeat`, and `Tagged`;
a tagged node reads a 1-, 2-, 4-, or 8-byte discriminator and visits only the
active variant. Niche-pointer optionals use their native null/payload form.
Static roots register as `(address, descriptor)` rather than an untyped byte
range. Runtime ABI revision 17 is the matching consumer contract.

## Incremental Compilation

Incremental reuse is enabled for `build`, `run`, `test`, and `check`. Artifacts
are profile-, target-, compiler-, option-, and source-fingerprinted.

| Path | Contents |
| --- | --- |
| `target/<profile>/metadata/` | Internal semantic metadata |
| `target/<profile>/objects/*.o` | Native package objects |
| `target/<profile>/objects/*.pcmeta.o` | Linked Taro PC metadata sidecars |
| `target/<profile>/objects/*.stackmaps` | Compiler stack-map descriptors |
| `target/<profile>/objects/*.bc` | Package bitcode for bitcode/LTO modes |
| `target/<profile>/objects/*.lto.o` | Full-LTO output |
| `target/<profile>/objects/thinlto-*` | ThinLTO objects and cache |

Object and bitcode entries cannot satisfy one another's cache requirements.
`check` requires semantic metadata only. Final executables are relinked so the
current output path and native inputs are always honored.

Use `--no-incremental` for a cold build. `.taro_meta` is a binary internal
format, not a stable interchange format.

## Attached Standard Library

Std is an attached toolchain artifact. The compiler expects target-specific
metadata and native code under:

```text
$TARO_HOME/lib/taro/std/<target-triple>/std.taro_meta
$TARO_HOME/lib/taro/std/<target-triple>/std.o
```

It does not silently rebuild missing or incompatible std artifacts. Rebuild the
local distribution, or request an explicit source rebuild:

```bash
TARO_HOME="$PWD/dist" \
  dist/bin/taro check examples/hello.tr --std-path std --build-std
```

Attached std uses one canonical release-like configuration per target and is
shared by debug and release user builds.

## Cross-Compilation

`--target` controls LLVM output, attached std selection, runtime selection, and
linking. Runtime archives and their manifests live at:

```text
$TARO_HOME/lib/taro/runtime/libtaro_runtime.a
$TARO_HOME/lib/taro/runtime/<target-triple>/libtaro_runtime.a
```

Each archive has an adjacent `.manifest.toml` containing the runtime ABI,
target, architecture, and checksum contract. This validation also applies to
`--runtime-path` and `TARO_RUNTIME_LIB`.

Build a target-ready local distribution with:

```bash
python3 development/scripts/build_dist.py --target x86_64-apple-darwin
```

Same-OS Darwin cross-architecture links use the host SDK automatically. Linux
cross-architecture builds require a compatible `--linker` or `--sysroot`;
cross-OS Darwin/Linux builds require both.
