# Code Generation

Taro lowers typed source through HIR, THIR, MIR, and LLVM IR. LLVM performs
instruction selection and native optimization.

## Profiles

- Debug builds use the baseline pipeline and retain overflow checks.
- Release builds use O2 and disable overflow checks.
- `-O0`, `-O1`, `-O2`, `-O3`, `-Os`, and `-Oz` override LLVM optimization.
- `--overflow-checks` and `--no-overflow-checks` override the profile default.
- The integer `checked*`, `wrapping*` and `saturating*` methods ignore the
  overflow policy. They use the `__intrinsic_wrapping_*` and
  `__intrinsic_overflows_*` intrinsics, which lower to plain LLVM arithmetic or
  an overflow flag, so their meaning survives inlining and specialization into a
  checked package.

Functions containing diagnostic stack maps use SelectionDAG. Other O0
functions may use GlobalISel on supported AArch64 targets.

## MIR Pipeline

Source MIR tracks definite initialization, references, and control flow. The
compiler emits typed GC layouts and precise roots; asynchronous functions become
frame constructors and synthesized poll bodies.

1. **Canonical MIR** is locally simplified and transformed for async execution.
2. **Shared MIR** completes inlining, lowering, propagation and coalescing.
3. **Instance MIR** specializes generic arguments and simplifies concrete bodies
   before LLVM lowering.

Canonical/shared MIR and GC layout information are stored in dependency metadata.
Metadata format and runtime ABI identities reject incompatible artifacts; rebuild
the compiler and attached standard library after changing the reference format.

The deterministic MIR inliner avoids recursive call-graph edges, respects
`@noinline`, and treats `@inline` as a profitability override within ABI, depth
and growth limits. Safe references use one pointer word. Escaping references
keep their storage alive through GC reachability; raw pointers retain their
explicit unsafe lifetime and initialization obligations.

## Values and Call Boundaries

Structs and arrays copy as ordinary values. Class and collection headers share
their managed targets; strings copy their immutable pointer/length header.
There are no ARC retain/release operations, destructors or runtime borrow guards.
Enum payloads are initialized before publishing their discriminant.

A class-field reference points inside the selected managed object. Taking or
returning it does not require boxing the local class-handle slot. The field
access intrinsic's escape contract follows the handle to its object; taking a
reference to the handle variable itself still preserves that variable's storage.

Runtime calls are classified `Direct`, `Callback` or `Blocking`. These categories
control native call boundaries and collector cooperation. Foreign code cannot
create compiler intrinsic privileges by choosing a familiar symbol name.

## Shared-Memory Accesses

Places reached through a pointer (any MIR `Deref`, class fields and the
handles leading to them) may be shared with other threads. Their loads and
stores go through `build_shared_load`/`build_shared_store`. Typed raw-pointer
`read`/`write` operations use the same lowering. Typed `copyTo` and
`copyToNonoverlapping` use word-atomic copies for aligned pointer-bearing
elements; their intrinsic byte count must cover whole elements. Explicit byte
copies remain unsafe byte operations and provide no typed-pointer guarantee:

- A pointer leaf is accessed with one `unordered` atomic load or store at
  pointer alignment, which LLVM may not split, merge into wider accesses or
  re-read.
- Aggregates with up to eight scalar leaves are split per field. Only pointer
  leaves become atomic; other leaves stay plain.
- Larger pointer-bearing aggregates move through an entry-block temporary
  with `llvm.memmove.element.unordered.atomic` (element size 8). Large MIR
  assignments of pointer-bearing values use the same intrinsic instead of
  `memmove`. Its libcall, `__llvm_memmove_element_unordered_atomic_8`, lives
  in the runtime and copies one atomic word at a time.
- Pointer-free values, packed structs and thread-private locals keep plain
  accesses.

Codegen emits no `noalias` attributes, so shared references cannot be
miscompiled as unaliased. The rationale and the language-level contract are in
`docs/async-runtime.md` (Shared Memory). `valid/race_pointer_words_never_tear`
is the litmus test; `codegen::llvm::shared_access_tests` pins the emitted IR.

## PC Metadata

Native Taro objects have a linked `.pcmeta.o` sidecar generated from LLVM stack
maps. The runtime consumes Taro's normalized format, not LLVM's experimental
section. PC schema7 stores call/allocation/poll/blocking/panic sites, their selectors,
logical source frames and typed root locations. A shared layout graph describes
heap, static and stack storage, including tagged payloads and repeated elements.

Each diagnostic site publishes a nonzero selector before its stack-map anchor.
The return PC identifies the physical function; the selector identifies the
executed source site. LLVM may duplicate or coalesce machine locations without
combining distinct source diagnostics. Root operands identify live initialized storage; the selector distinguishes
source states when machine locations are shared.

Private local values of at most two pointer words use separate collector spill
slots. Their working storage can promote to registers; immediately before a
collecting call or on a poll's slow branch, codegen publishes the current value
with a volatile store into its typed root slot. The ordinary poll path does not
spill roots. Initialization of
partially constructed private values remains defined, including zero bytes in
fields not yet assigned. Larger inline values, address-taken locals, indirect
ABI storage, and value arguments whose addresses may be materialized by callable
shims retain stable storage and preserved initialization. References into that
storage continue to observe the actual value rather than a collector snapshot.

Physical functions carrying diagnostic sites preserve their frame, disable tail
calls and retain unwind metadata. Logical frames preserve source provenance when
MIR inlining places several Taro functions in one physical frame. Stack-overflow
protection is installed independently on native execution/callback threads.

## Outputs and LTO

`taro build` produces a native executable for source files and executable
package targets. Library packages emit object code and metadata without linking
an executable. `--emit llvm-bc` instead writes verified, optimized package bitcode:

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

Incremental reuse is enabled for `build`, `run`, `test`, `bench`, and `check`.
Cache keys include profile, target, compiler, options, source, and dependency
metadata. Package artifacts live under `target/<profile>/` in the package root;
single-file artifacts live under the system temporary directory at
`taro-scripts/<path-hash>/<profile>/`. `--no-incremental` bypasses reuse.
`.taro_meta` is an internal format and incompatible metadata is rejected.

## Attached Standard Library

The compiler loads target-specific std metadata and native code from:

```text
$TARO_HOME/lib/taro/std/<target-triple>/std::taro_meta
$TARO_HOME/lib/taro/std/<target-triple>/std::o
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

The distribution helper keeps the compiler executable on the host and builds
the runtime and attached std for the requested target. The Rust target must be
installed before building its runtime (for example,
`rustup target add x86_64-apple-darwin`).

Native linking currently supports Darwin and Linux. Same-OS Darwin
cross-architecture links use the host SDK. Cross-architecture Linux links
require a compatible `--linker` or `--sysroot`; cross-OS links require both.
LLVM object/bitcode emission does not require a native linker.

## Scanner Initialization and Root Publication

The following invariants apply to scanner bytes independently of source-level
initialization. A source value may still be uninitialized when all its potential
pointer slots have been made safe for the collector to inspect.

- `gc_sites::storage_live_covers_observations` may defer entry zeroing only when
  one `StorageLive` dominates every read, write and address formation.
  `Rvalue::addressed_place` exhaustively classifies address-forming rvalues;
  introducing a new rvalue requires updating that match. Call arguments can also
  expose storage and remain part of `gc_frame`'s address-taking analysis.
- `storage_live_is_fully_copied` crosses only explicitly harmless markers to a
  whole-slot copy in the same block. Unknown statements stop the proof. Partial
  stores, addresses, polls and erased copies that can allocate retain zeroing.
- `gc_storage::insert_temporary_storage_lifetimes` applies only to unescaped,
  unaddressed compiler temporaries with no existing lifetime boundary. Its first
  observation dominates every use. Async bodies and any cyclic CFG remain
  conservative; `gc_safepoints::has_cycle` checks the CFG before polls exist.
- Private values at most two pointer words may use a separate spill slot.
  Every collecting path publishes the current bytes before its selector/map;
  address-taken values retain their real storage. The size threshold is a
  profitability choice, never a relaxation of root liveness or initialization.
- `effects::is_pointer_offset_wrapper` admits only its explicit bounded set of
  scalar operations and one known noncollecting intrinsic. Every unrecognized
  statement, terminator, call or type rejects the exception. Loop and recursive
  cooperation must remain after inlining.
- Recursive wrapper inlining follows the actual source expansion ancestry and
  retains physical-owner, depth and growth stops. Shared dependency MIR stays
  immutable; concrete instance optimization must not depend on package order.
- A collecting site reads a fresh selector and current typed layout, including
  enum tags and reference indirections. No cache may retain live root values or
  a prior frame's base. Guarded matches retain their value snapshots.

`development/scripts/test_gc_stress.py` is the periodic focused stress gate for
these contracts. Run it after MIR/root-protocol changes and before accepting a
new optimization family; it is not required for every documentation edit.

Physical frame recovery is a separate platform contract. Apple libunwind's
`_Unwind_GetCFA` exposes the cursor's current SP; the reader must not subtract
LLVM's static frame size again. The native ARM64 frame regression checks this
against the live SP. Other targets retain their existing CFA recipe. PC root
maps alone do not describe every caller transition: a frameless witness thunk
can preserve FP while changing SP and the saved return PC. The
[frame-recipe probe](../development/benchmarks/stack_walker/README.md) inspects
LLVM stack maps, unwind data and machine code without replacing the production
reader. The rejected FP-only path is absent from the runtime.
