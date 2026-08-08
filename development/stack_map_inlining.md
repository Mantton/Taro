# GC maps and MIR inlining

Taro inlines functions that contain collecting sites in MIR, before it computes
the final safepoints and roots. LLVM is still forbidden from inlining any
physical function that contains a collecting site. That split removes hot
wrapper calls without letting a backend transformation invalidate the physical
frames named by PC metadata.

Before this work, every function that emitted a stack-map record was `noinline`.
On the Monkey bytecode machine, 82% of samples in the hot dispatch loop landed
in wrappers such as `Opcode.fromByte`, `List.at`, `ptr.add`, `push`, `pop`, and
`readUint16`. Twenty million reads took 95 ms through `List.at` versus 40 ms as
inline pointer arithmetic on the original Apple M2 measurement.

## Pipeline and stored MIR

Every ordinary or synthesized async function has two stored representations:

1. **Canonical inline MIR** has completed local lowering and cleanup but has not
   run interprocedural optimization or inlining.
2. **Final codegen MIR** has completed global passes and is the body lowered to
   LLVM.

Metadata format 27 serializes both forms into separate stores. The inliner
always reads canonical bodies, including for cached dependencies, so a source
callee and the same attached callee produce the same decision. Retention is
computed from canonical inline candidates while final bodies still needed for
generic downstream codegen are retained independently. The ordinary-body
retention bound is 115 cost units, matching O3's threshold plus the maximum loop
and constant-argument bonuses; explicit-inline and generic bodies remain
independent retention roots.

The effective order is:

```text
canonical MIR -> MIR inlining -> explicit effects/allocations/polls
              -> precise roots -> LLVM -> PC metadata sidecar
```

Hidden existential boxes become explicit `Alloc`, payload store, and
non-allocating pack operations after inlining and before escape analysis. This
makes allocation and collection behavior visible to both optimizers and root
analysis.

## Deterministic inlining policy

The inliner builds direct-call strongly connected components and never inlines
an edge within a recursive SCC, including an `@inline` edge. `@noinline` is
absolute. `@inline` bypasses profitability but not recursion, ABI validity,
depth, or the forced-growth cap. Calls with cleanup edges are eligible when
their normal and unwind destinations can be remapped.

The fixed cost model assigns one unit per statement, two per basic block,
`1 + arm count` per switch, five per call, ten per allocation or panic, and 20
for a loop-containing callee. The base thresholds are:

| Profile | Threshold |
| --- | ---: |
| O0/debug | explicit `@inline` only |
| O1/O2 | 40 |
| O3 | 80 |
| Os | 20 |
| Oz | size-neutral/reducing, or explicit `@inline` |

A callsite inside a loop receives 20 more units. Constant arguments add five
each, capped at 15. Normal growth is capped at the greater of 200 units or 50%
of the caller's original cost; O3 permits 100%. Forced inline growth is capped
at 2,000 units and nesting depth at eight. Worklist order and all tie-breaking
are deterministic.

## Effects, polls, and the LLVM boundary

Every call has one authoritative effect: `NoGc`, `ManagedSafepoint`,
`RuntimeSafepoint`, or `BlockingSafepoint`. Direct, indirect, and virtual Taro
calls are managed safepoints. Intrinsics and ordinary C ABI calls default to
`NoGc`; native work that can block must use the blocking ABI. Missing runtime
ABI classifications are compile errors.

Every managed body has one entry poll. Loop polls are chosen by finding cyclic
CFG SCCs and selecting blocks until removing the selected blocks makes each SCC
acyclic. A verifier proves that every remaining cycle crosses a poll.

After MIR inlining and root-map emission, every physical function containing
an entry/loop poll, managed or collecting-runtime call, allocation, blocking
transition, or panic site is marked `noinline`, and LLVM tail-call elimination
is disabled for that function. It also receives synchronous unwind metadata so
the native walker can traverse the frame even when a poll has no roots. This is
based on collecting-site presence, not root count: even a rootless poll must
emit an empty record and preserve an unwindable managed frame boundary. Without
the tail-call barrier, the callee frame can disappear; without its unwind entry,
the walk can stop there and hide mapped callers. Either failure loses arguments
that a managed caller intentionally transferred to the callee. Functions with
no collecting site remain eligible for LLVM inlining and tail-call optimization.

## Precise roots

Liveness is tracked before and after each statement and terminator through
branches, loops, moves, `StorageLive`, normal edges, and cleanup edges. It is
whole-local rather than projection-sensitive. Definite initialization excludes
dead or uninitialized storage. `KeepAlive(operand)` is a compiler-only use that
extends liveness without emitting a call or poll.

Root storage is keyed by `LocalId`, and each site selects its own subset:

- polls use values live at the site;
- managed calls use values live across either continuation, excluding the full
  destination and arguments protected by the callee's managed frame;
- collecting runtime helpers add their GC-bearing arguments;
- blocking calls add their published arguments;
- allocations use values live after the allocation and values used across it;
- panic sites use cleanup-live values and GC-bearing arguments.

Every collecting site emits a record, including rootless polls. A collecting
physical frame has one selector slot, and each site volatile-stores a distinct
nonzero value before its stack-map anchor. The runtime reads that value from the
parked frame. Records that resolve to one machine PC therefore remain distinct
instead of unioning typed roots from mutually exclusive paths; PC order selects
only among machine duplicates of the observed selector. The stack-map intrinsic
is `nounwind`, so an enclosing unwind edge never converts it to an invalid LLVM
`invoke`. Blocking-call codegen publishes its selector and map before calling
`__rt__gc_enter_blocking`, because that transition parks and walks the frame.

The precise-liveness language regression uses the test-only runtime pair
`__rt__test_gc_probe_create` and `__rt__test_gc_collect_probe_is_live`. The
second entry collects and reads its weak probe before returning to generated
code, so a later entry poll cannot erase evidence of over-retention. It returns
only a boolean and is declared directly through `extern "taro_rt"`; inserting a
managed wrapper would add another collecting frame and invalidate the oracle.
The raw-pointer declarations are unsafe and remain confined to `std.testing`.
The inactive-variant case forces a non-NPO enum and deliberately seeds its
inactive payload bytes while preserving the `.empty` tag, ensuring the test
actually distinguishes tagged traversal from a flat offset union.

## Typed layout and PC metadata contract

PC schema 4, pending-descriptor schema 3, and runtime ABI 16 share one indexed
`GcLayoutNode` graph for stack, heap, static, and buffer traversal. The graph
supports pointer, reference, aggregate, fixed-repeat, and tagged nodes. Tagged
nodes visit only the variant selected by a 1-, 2-, 4-, or 8-byte discriminator;
niche-pointer optionals use null/payload representation directly. Invalid live
tags abort with descriptor, value, and address information. Recursive reference
traversal tracks `(address, node)` and enforces visit/depth limits.

Dynamic buffers repeat their element descriptor over their registered scan
capacity. Raw and interior pointers remain strong candidates; the page map
resolves them to their containing managed allocation. Static roots register an
address plus its exact descriptor rather than an untyped range.

The PC sidecar remains a separate linked object. Normalization records exact
machine-function bounds, attributes moved/duplicated records to their final
function, and preserves selector-disambiguated same-PC records. It rejects
selector-location disagreement and machine duplicates whose GC semantics have
changed. Layout nodes and recipes are copied and deduplicated inside the
sidecar, so it never relocates against an internal layout symbol in another
object file.

## Runtime consequences

Small allocations use one TLS checked-out span per size class and scan/no-scan
lane. A warm allocation removes a slot under owner-exclusive access, zeroes it,
writes metadata, and release-publishes the allocation bit without acquiring the
global collector lock. Mutators flush checked-out spans before safepoint
publication, blocking, detach, or collection.

Adaptive pacing uses 64 KiB per-mutator debt quanta, `TARO_GC_PERCENT`, and the
soft `TARO_GC_MEMORY_LIMIT`. Once surviving live data exceeds that limit, the
percentage goal backs off by at least 1 MiB rather than remaining immediately
due; future segment growth still receives one collect-and-scavenge pressure
attempt. Sweep releases empty segments and, on Unix, `DontNeed`s only wholly
free native-OS-page ranges. See `docs/async-runtime.md` for the full environment
and publication contract.

The collector deliberately remains stop-the-world, non-moving mark-sweep.
Generational or concurrent collection, compaction, pinning, write barriers, and
MMTk integration are deferred.

## Verification and benchmark method

Correctness is covered by MIR liveness/effect/inliner tests, codegen schema and
selector-disambiguated same-PC tests, typed scanner and allocator tests,
language weak-reference and unwind regressions, the debug/release codegen
matrix, and runtime stress. Release
performance is measured as medians from repeated runs on an otherwise idle
machine, recording the exact command and `TARO_GC_STATS=1` output. Optimized MIR
or LLVM output must also show the target wrapper call absent; elapsed time alone
is not proof that inlining occurred.

### Final release measurements

These measurements were taken on the same Apple M2 as the handoff, with
`TARO_WORKERS=1`, an otherwise idle machine, and the default release/O2 profile.
The Fibonacci rows are medians of five runs for 28 and three runs for 35. The
list fixture performs nine timed samples in one process and reports the median.

| Fixture | Handoff | Final median | Change |
| --- | ---: | ---: | ---: |
| `fibonacci(28)`, VM | 605 ms | 154 ms | 3.93x faster |
| `fibonacci(35)`, tree walker | 156.5 s | 99.706 s | 1.57x faster |
| `fibonacci(35)`, VM | 18.1 s | 4.342 s | 4.17x faster |
| 20M `List.at` reads | 95 ms | 11.024 ms | 8.62x faster |

The final `fibonacci(28)` tree-walker median was 3.238 s. The same-machine Go VM
measurement remains 3.7 s for `fibonacci(35)`, so it is context rather than a
hardware-independent gate: the final Taro median is 1.17x slower.

After adding selector-disambiguated records, native-page scavenging, and the
soft-limit backoff, a fresh five-run `fibonacci(28)` regression check measured a
147 ms VM median and a 3.276 s tree-walker median. The selector publication did
not regress the prior 154 ms VM result.

Optimized LLVM for the list fixture contains the element load and bounds guard
inside `main` and no call to `List.at`. Optimized `VM.run` contains no calls to
`Opcode.fromByte`, `readUint16`, `Instructions.raw`, `VM.push`, `VM.pop`, or
`ptr.add`; the fixed caller-growth cap still leaves less-profitable `List.at`
and `Object.clone` sites in some opcode arms. This distinction is intentional:
the benchmark evidence demonstrates the hot wrapper elimination without
pretending that `@inline` may violate the 2,000-unit hard cap.

With `TARO_GC_STATS=1`, a VM-only `fibonacci(35)` run reported 118 allocations,
1 collection, 13 cached-span refills, 1,611,472 allocated bytes, 40,960 scavenged
bytes, and no soft-limit exceedance. A full two-engine `fibonacci(28)` run
reported 18,119,562 allocations, 1,944,083,072 allocated bytes, 1,683,783,680
scavenged bytes, 1,048,576 released bytes, and no soft-limit exceedance. Stats
were captured separately because per-collection diagnostics perturb timing.
