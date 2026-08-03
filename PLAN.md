# Compiler Stack Maps and PC Metadata

## Status

Phases 1-8 are implemented. Compiler PC maps are authoritative, the shadow
frame ABI and `ShadowResync` MIR have been removed, and compact panic reports
consume structured physical/inline frames from the same registered metadata.
Full-suite verification and paired final benchmarks remain in progress.

On AArch64 O0, functions containing PC maps intentionally take LLVM's
per-function SelectionDAG fallback because GlobalISel cannot select the stack
map intrinsic. Rootless functions remain eligible for GlobalISel; optimized
builds already use SelectionDAG. The codegen matrix therefore validates actual
debug/release emission and execution instead of making every selector fallback
fatal.

## Outcome

Replace Taro's per-function shadow-root maintenance with compiler-produced,
program-counter-indexed stack maps, and use the same always-on metadata pipeline
to produce useful compact panic stacks in debug and optimized builds.

At completion:

- a root-bearing function does not call `__rt__gc_push_frame` or
  `__rt__gc_pop_frame`;
- assignments do not copy GC pointers into parallel shadow slots;
- a parked mutator publishes its own precise roots before advertising that it
  is stopped, so the collector never reads another thread's live registers;
- the collector treats the new root snapshots as authoritative;
- compact panic reports identify debug frames whose resolver returns DWARF short
  names and expand compiler-recorded inline ancestry in release builds;
- the old shadow-frame and logical-stack runtime ABI is removed rather than
  retained as a compatibility path;
- rootless call and loop performance does not regress, and rooted call overhead
  improves against the round-one baseline.

## Non-goals

- A moving or generational collector. Taro remains a non-moving precise
  mark/sweep collector in this change.
- Asynchronous thread suspension. Threads continue to cooperate through the
  existing poll, allocation, blocking-call, and detach transitions.
- A general-purpose debugger or complete DWARF replacement. The PC table carries
  only information needed by GC and Taro diagnostics.
- Backward compatibility with previously compiled objects or runtime archives.
  The compiler/runtime ABI and incremental fingerprints will be revised.

## Design constraints

1. LLVM may keep requested values in registers, and another thread cannot
   safely reconstruct those registers from a stack pointer. Each mutator must
   therefore walk its own stack while it still owns its register state and
   publish resolved root values before setting `at_safepoint`.
2. LLVM's raw stack-map section is an experimental backend contract. The
   compiler will parse it immediately after machine-code emission and emit a
   versioned, target-neutral Taro metadata sidecar. The runtime will not parse
   LLVM's format.
3. Root locations passed to `llvm.experimental.stackmap` will be addresses of
   entry-block storage, not arbitrary pointer values. The compiler will reject
   a record that LLVM did not lower to a directly addressable frame location.
   This avoids restoring volatile registers during root discovery.
4. The PC table is always linked, including release builds. Full DWARF remains
   optional.
5. All map IDs are deterministic and unique across packages, generic
   instantiations, synthetic functions, full LTO, and ThinLTO imports.
6. The temporary comparison path may exist while implementing and testing, but
   the final runtime must have one authoritative root mechanism.

## Metadata model

The normalized table is versioned independently from package metadata and the
runtime ABI. It contains:

- **Module header**: schema version, target pointer width, architecture, and
  record counts.
- **Function record**: relocated function entry, function extent or sorted PC
  boundary, physical Taro symbol, package/frame kind, source definition, and
  root-layout reference.
- **PC record**: instruction offset, safepoint/callsite kind, root-map reference,
  source location, and inline-scope reference.
- **Root map**: direct frame locations in LLVM operand order plus the Taro root
  recipes for each local (field byte offsets and reference dereference depth).
- **Inline scope**: logical function, callsite source location, and parent scope.
- **String/file tables**: deduplicated UTF-8 names and source paths.

The compiler emits a small sidecar object whose globals contain relocations to
the associated generated functions. A constructor registers each table with the
runtime. This avoids platform-specific discovery of Mach-O/ELF stack-map
sections and works for dependency objects and incremental reuse.

## Implementation phases

### 1. Establish the baseline

- Write this plan.
- Commit the existing dirty tree in logical Conventional Commit batches without
  changing its behavior.
- Re-run focused checks if staging reveals overlap or an invalid intermediate
  batch.
- Record the current rooted-call, rootless call/loop, list-read, string-method,
  and Monkey benchmark medians using retained release binaries.

Files:

- `PLAN.md`
- `development/benchmarks/runtime_overhead/*`
- existing dirty files, committed by their already-completed feature scope.

### 2. Repair the panic-frame regression first

- Change `runtime/src/panic_unwind.rs::parse_backtrace_frames` and frame
  classification so a resolved continuation line whose path ends in `.tr`
  classifies an otherwise-unknown short symbol as a Taro user frame.
- Retain linkage-tag classification for stripped/no-debug configurations.
- Add unit coverage for short DWARF names with `.tr` locations.
- Strengthen one language panic fixture with a named `@noinline` helper so the
  assertion holds in both debug and release codegen-matrix runs.

Files/functions:

- `runtime/src/panic_unwind.rs`
  - `classify_frame`
  - `parse_backtrace_frames`
  - `render_native_taro_stack`
  - focused parser/render tests
- `language_tests/source_files/valid/panic_unwind_nested_defer.tr` (or a new
  dedicated panic-stack fixture)
- `language_tests/codegen_matrix.txt` if a new fixture is used

### 3. Preserve logical inline provenance in MIR

- Add a per-body inline-scope table containing callee definition, callsite span,
  and parent scope, with scope zero representing the physical function.
- Add a `SourceScope` marker statement at the beginning of each inlined MIR
  region. Code generation resets to scope zero at each basic block and treats
  markers as no-ops that update the active scope. This preserves provenance
  through block concatenation without adding a field to every MIR node.
- Have MIR inlining create/remap child scopes and markers for copied regions.
- Insert poll statements after a block's leading scope marker.
- Preserve/remap scopes through CFG simplification, async transformation,
  metadata serialization, and cross-package MIR loading.
- Extend MIR structural validation and pretty printing.

Files/functions:

- `compiler/src/mir/mod.rs`
  - `Body`, `StatementKind::SourceScope`
  - new `SourceScopeId` / `InlineSourceScope`
- `compiler/src/mir/builder.rs` and builder submodules
- `compiler/src/mir/optimize/inline.rs::inline_call` and remap helpers
- MIR passes that synthesize or clone statements/terminators
- `compiler/src/mir/optimize/validate.rs`
- `compiler/src/mir/pretty.rs`
- `compiler/src/metadata/wire.rs`
- `compiler/src/metadata/mod.rs` format revision

Focused tests must demonstrate nested and cross-package inline chains surviving
optimization and wire round trips.

### 4. Emit LLVM stack-map anchors and compiler descriptors

- Replace copied-value shadow slots with root-bearing local storage retained for
  direct frame addressing.
- Zero-initialize root-bearing storage before it can appear in a map.
- Compute per-site root liveness after final MIR optimization. Start with all
  initialized root-bearing locals only if the liveness analysis cannot prove a
  smaller safe set; never omit an uncertain root.
- Emit `llvm.experimental.stackmap`:
  - in the poll slow block immediately after `__gc__poll`;
  - at managed callsites so suspended caller frames have maps;
  - immediately after allocation calls that may initiate collection;
  - immediately after blocking transitions whose snapshot remains authoritative while
    native code runs.
- Attach deterministic IDs and collect the Taro root recipes and source scopes
  corresponding to each intrinsic operand.
- Keep functions containing maps physically intact after MIR's map-aware
  inliner; LLVM remains free to inline pure functions that contain no maps.

Files/functions:

- new `compiler/src/codegen/stack_maps.rs`
  - map ID generation
  - root recipe construction
  - pending map descriptors
- `compiler/src/codegen/llvm.rs`
  - `allocate_locals`
  - replacement for `setup_shadow_stack`
  - `emit_gc_poll`
  - direct/indirect call lowering
  - allocation and blocking-call lowering
- `compiler/src/mir/analysis/liveness.rs`

IR tests must prove rooted storage is passed directly to stack-map intrinsics,
rootless functions emit no root operands, and maps survive O0/O2 and inlining.

### 5. Normalize object metadata after code generation

- Extend the existing pinned-LLVM native shim with LLVM's maintained
  `ObjectFile` and `StackMapParser` APIs. Do not add a second object parser.
- Parse `.llvm_stackmaps` / `__llvm_stackmaps` after ordinary object emission,
  full-LTO emission, and each ThinLTO backend object.
- Validate stack-map version, architecture, unique IDs, record counts, operand
  order, and direct-location encoding. Treat mismatches as compiler errors, not
  runtime fallbacks.
- Join raw records with compiler descriptors by ID.
- Emit/register a compact Taro sidecar object with function relocations and the
  normalized tables.
- Include sidecars in link inputs, incremental metadata, cache validation, and
  artifact fingerprints.

Files/functions:

- `compiler/native/llvm_shims.cpp`
- `compiler/src/codegen/stack_maps.rs`
- new `compiler/src/codegen/pc_metadata.rs`
- `compiler/src/codegen/artifact.rs` (primary object plus metadata sidecar)
- `compiler/src/codegen/llvm.rs::emit_module_artifact`
- `compiler/src/codegen/lto.rs`
- `compiler/src/codegen/link.rs`
- `compiler-cli/src/command/build.rs`
- `compiler-cli/src/command/incremental.rs`
- `compiler/src/metadata/mod.rs` / `wire.rs` as needed for artifact reuse

Cross-target tests must parse x86-64 ELF and AArch64 Mach-O output without
executing it. Full LTO, ThinLTO, and incremental reuse each need a regression.

### 6. Publish roots cooperatively in the runtime

- Add a per-thread published-root buffer and its publication generation to
  `ThreadState`.
- Walk the current native stack on slow transitions, look up each return PC in
  registered Taro metadata, evaluate direct root recipes, normalize interior
  pointers through the existing heap lookup, and store the resulting root
  values.
- Publish the completed buffer with release ordering before
  `at_safepoint = true`; read it after acquire ordering in the collector.
- Capture the initiating collector thread as well as mutators that park in a
  poll/allocation.
- Capture before entering a blocking foreign call and retain that snapshot until
  managed execution resumes.
- Handle direct native/runtime entry, detach during a collection snapshot,
  nested collection requests, unwinding, and an empty Taro stack.

Files/functions:

- new `runtime/src/pc_metadata.rs`
  - ABI structs and registration
  - sorted module/function/PC lookup
- new `runtime/src/stack_walk.rs`
  - current-thread unwind abstraction for supported architectures
  - direct-location evaluation
- `runtime/src/garbage_collector.rs`
  - `ThreadState`
  - `enter_safepoint`, `leave_safepoint`, `park_at_safepoint`
  - `initiate_collection`
  - `mark_roots`
- `runtime/src/lib.rs`
- `runtime/Cargo.toml` / `Cargo.lock` if an established unwinding library is
  required
- `compiler/src/runtime_abi.rs` revision and symbol manifest

The root buffer is written only by its owning mutator and read only after the
existing stop-the-world handshake. It must not require a lock on the poll fast
path.

LLVM may place a zero-width map a few instructions after the architectural
return PC while finishing a call sequence. Runtime lookup therefore resolves a
suspended return PC forward to the adjacent post-call record in the same
mapped function.

### 7. Validate, switch authority, and remove shadow frames

- During development, scan both mechanisms and then run the root regression
  suite with compiler maps as the sole authority. Raw equality is not a valid
  oracle: alias mutation can leave conservative shadow slots pointing at a
  superseded object after the mapped local already contains its replacement.
- Add collection-at-every-safepoint stress coverage for:
  - nested calls and recursion;
  - aggregate/interior/reference roots;
  - indirect arguments and return storage;
  - panic/unwind/defer paths;
  - async suspension and worker migration;
  - blocking native calls;
  - thread attach/detach races;
  - full/Thin LTO and generic instantiations.
- Make published PC-map roots authoritative.
- Remove `GcShadowFrame`, `GC_SHADOW_TOP`, `__rt__gc_push_frame`,
  `__rt__gc_pop_frame`, `ShadowResync`, copied shadow slots, refreshes, and
  corresponding ABI entries/tests.
- Remove the temporary comparison mode and bump all relevant metadata/ABI
  versions.

Files/functions:

- `runtime/src/garbage_collector.rs`
- `compiler/src/codegen/llvm.rs`
- `compiler/src/mir/mod.rs` and every `ShadowResync` producer/consumer
- `compiler/src/metadata/wire.rs`
- `compiler/src/runtime_abi.rs`
- GC language fixtures and runtime unit tests

### 8. Use PC metadata for compact panic stacks

- Query the Taro PC table before symbol-name heuristics.
- Render the innermost inline chain followed by physical caller frames, with
  adjacent duplicate frames collapsed.
- Keep native backtrace formatting as the fallback for runtime/toolchain/native
  frames and for binaries lacking valid Taro metadata only because no Taro code
  is present.
- Preserve the 64-frame compact limit and omission count.
- Verify debug short names, stripped release binaries, MIR-inlined functions,
  recursion, async task traces, and double panic. Functions with PC records are
  not eligible for post-map LLVM inlining.

Files/functions:

- `runtime/src/panic_unwind.rs`
  - `render_native_taro_stack`
  - PC lookup/render helpers
- `runtime/src/pc_metadata.rs`
- panic language fixtures and runtime unit tests

### 9. Verification and performance acceptance

Correctness commands:

```text
make dist
make language-tests JOBS=8
make codegen-matrix JOBS=8
make std-tests
cargo test --workspace
cd showcase/monkey && taro test .
```

Additional gates:

- GC stress mode repeatedly collecting at every eligible slow transition.
- Debug and release panic reproducer must show named Taro frames; release must
  include `level1`, `level2`, and `level3` as inline logical frames.
- Object inspection for debug/release, full LTO, ThinLTO, x86-64 ELF, and
  AArch64 Mach-O.
- `git diff --check` on the feature diff.

Benchmark protocol:

- Build retained before/after release binaries from clean commits.
- Use paired, interleaved runs and report median plus spread over at least 15
  samples for short microbenchmarks.
- Measure:
  - `development/benchmarks/runtime_overhead/inline_additions.tr`
  - `function_calls.tr`
  - `rooted_function_calls.tr`
  - `list_reads.tr`
  - `string_byte_len.tr`
  - Monkey `--bench 30` for routine iteration
  - Monkey `--bench 35` for final headline comparison
- Report absolute time, percentage change, inferred bare-call surcharge,
  inferred rooted-frame surcharge, binary-size delta, and any GC pause/root-scan
  delta.

Acceptance criteria:

- no correctness or stress failures;
- no measurable regression beyond noise in rootless loop/call benchmarks;
- rooted wrapper surcharge materially below the current approximately 4.5 ns;
- compact panic stacks useful in both profiles;
- Monkey VM/tree numbers reported against the retained pre-feature binary, even
  if the change is neutral for that workload.

## Failure policy

- A malformed or unsupported compiler-produced map is a compile/link error.
- The runtime does not conservatively scan arbitrary stack words as a fallback;
  that would hide compiler omissions and can retain invalid addresses.
- If LLVM cannot provide direct root locations on a supported target, stop at
  the object-normalization gate and resolve that backend design explicitly
  before changing collector authority.
- If an authoritative-map stress test loses a live object, preserve the failing
  artifact and minimize it before continuing.
