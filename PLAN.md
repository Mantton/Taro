# Compiler Stack Maps and PC Metadata

## Status

Complete. Phases 1-9 are implemented. Compiler PC maps are authoritative, the
shadow-frame ABI and `ShadowResync` MIR have been removed, and compact panic
reports consume structured physical/inline frames from the same registered
metadata. The full compiler, language, standard-library, LTO, incremental, GC
stress, and showcase suites are green. Final results compare retained release
binaries from pre-feature commit `71f0fdc` with completed commit `d65c083`.

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

The compiler emits a compact sidecar object whose table references and function
entries are signed offsets from one module header. The linker resolves these
differences statically, and a constructor registers the header's single runtime
address. Identical root recipes, root-location arrays, strings, and logical
frames are deduplicated. The compiler strips LLVM's raw stack-map section after
normalization, while the runtime indexes function headers on the first walk and
decodes only the selected PC record. This avoids platform-specific runtime
discovery, unnecessary loader rebases, and eager standard-library table copies
while still supporting dependency objects and incremental reuse.

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
  recursion, async task traces, and double panic. Functions with retained PC
  records are not eligible for post-map LLVM inlining; zero-root poll-only
  functions emit no record and remain eligible.

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

## Final verification and benchmark results

All correctness gates passed on AArch64 macOS:

- `make dist`
- `make language-tests JOBS=8`: 227/227
- `make codegen-matrix JOBS=8`: 62/62 across debug and release
- `make std-tests`: 461 passed, 1 skipped, including compile, bitcode,
  incremental, full-LTO, and ThinLTO smoke tests
- `cargo test --workspace`: 663/663
- Monkey language suite: 108/108
- focused compiler-map fixture in release, GC stress, full LTO plus stress,
  ThinLTO plus stress, and incremental reuse plus stress
- debug and release panic fixtures exited with the expected panic status and
  rendered `namedPanicFrame -> inlinePanicFrame -> main`
- cross-format object tests normalized and stripped both x86-64 ELF and AArch64
  Mach-O stack-map sections

### Runtime microbenchmarks

The primary microbenchmark protocol used 31 paired, interleaved process samples.
Each cell reports `median (MAD; p95)` in milliseconds; a negative change is an
improvement.

| Workload | `71f0fdc` | `d65c083` | Change |
| --- | ---: | ---: | ---: |
| Inline additions | 7.094 (0.135; 8.025) | 7.189 (0.143; 8.485) | +1.33% |
| Rootless function calls | 10.284 (0.149; 11.745) | 10.491 (0.199; 12.148) | +2.01% |
| String byte length | 101.757 (0.454; 109.815) | 25.075 (0.221; 28.843) | -75.36% |
| Rooted function calls | 146.580 (0.604; 184.979) | 36.175 (0.335; 37.876) | -75.32% |
| List reads | 444.302 (21.012; 595.312) | 68.767 (0.683; 117.881) | -84.52% |

The inferred bare-call surcharge was 0.319 ns before and 0.330 ns after, a
0.011 ns difference inside the observed spread. The inferred rooted-wrapper
surcharge fell from 4.482 ns to 1.110 ns (-75.2%). The two rootless medians rose
1.3-2.0%, but their MAD bands overlap; this is not a measurable practical
regression under the acceptance protocol.

The retained microbenchmark executables grew from approximately 3.883 MB to
4.699 MB (+21.0%) because they now link always-on PC metadata and the stack
walker. The final attached `std.o` is 1,283,656 bytes and contains no raw LLVM
stack-map section; `std.pcmeta.o` is 2,457,648 bytes. The 7,497,926-byte
`std.stackmaps` descriptor is a compiler artifact and is not linked into user
executables.

### Monkey showcase

Three paired `--bench 30` samples produced these medians:

| Engine | `71f0fdc` | `d65c083` | Change |
| --- | ---: | ---: | ---: |
| Tree interpreter | 19,364 ms (MAD 263) | 19,933 ms (MAD 58) | +2.94% |
| Bytecode VM | 13,386 ms (MAD 124) | 7,932 ms (MAD 105) | -40.74% |

The VM advantage increased from 1.45x to 2.51x. The requested `--bench 35`
headline pair was 218.932 s to 233.109 s for the tree interpreter (+6.48%) and
150.407 s to 93.303 s for the VM (-37.97%), increasing the VM advantage from
1.46x to 2.50x. That long run is a single pair and is therefore secondary to
the three-pair result. Both produced 9,227,465. The retained Monkey executable
grew from 4,437,392 to 5,743,400 bytes (+29.43%).

### Collection-time tradeoff

Five paired Monkey `--bench 20` samples with `TARO_RUNTIME_STATS=1` performed
identical work in every process: 53 collections, 1,204,809 allocations, and
55,827,232 allocated bytes.

| GC pause statistic | `71f0fdc` | `d65c083` | Change |
| --- | ---: | ---: | ---: |
| p50 | 0.434 ms | 0.913 ms | +110.32% |
| p95 | 1.283 ms | 1.323 ms | +3.13% |
| Maximum | 1.401 ms | 1.647 ms | +17.54% |

This is the deliberate cost transfer: root discovery no longer runs on every
managed call or assignment, but stack walking and PC-record decoding now run at
collection time. The runtime does not yet expose a separate root-scan timer, so
GC pause is the observable proxy. The p50 increase (about 0.479 ms per
collection) is material and likely contributes to the tree-interpreter
slowdown; the p95 increase is about 0.040 ms. It should remain a tracked metric
for future collector work rather than being hidden by the throughput wins.

## Failure policy

- A malformed or unsupported compiler-produced map is a compile/link error.
- The runtime does not conservatively scan arbitrary stack words as a fallback;
  that would hide compiler omissions and can retain invalid addresses.
- If LLVM cannot provide direct root locations on a supported target, stop at
  the object-normalization gate and resolve that backend design explicitly
  before changing collector authority.
- If an authoritative-map stress test loses a live object, preserve the failing
  artifact and minimize it before continuing.
