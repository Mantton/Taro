# Instance-aware escape analysis

Taro decides stack versus managed-heap placement on concrete codegen
instances. A generic definition is not a sufficient analysis key: the same
body can call an interface requirement whose selected implementation captures
an argument for one type and does not capture it for another.

This pass deliberately changes only compiler-created placement. Dictionary
layout, hashing, aggregate ABI, allocator batching, GC pacing, and application
source are outside its scope.

## MIR boundary

The compiler has three relevant representations:

1. Canonical inline MIR is locally cleaned and is the only input to MIR
   inlining.
2. Shared optimized MIR has completed inlining, existential and aggregate
   lowering, propagation, coalescing, and cleanup. It contains explicit
   allocations but no placement decisions or safepoints.
3. Instance-final MIR is an ephemeral clone of shared MIR keyed by `Instance`.
   It receives escape placement, focused cleanup, safepoint insertion, and
   safepoint merging before LLVM lowering.

Metadata format 29 serializes canonical and shared MIR. It never serializes
instance-final MIR or escape summaries. Source and cached dependencies therefore
run the same finalizer over the same shared representation. The codegen guard
requires the exact body cached for the requested instance, so witness-table or
late-discovered instances cannot silently fall back to generic shared MIR.

## Graph and data flow

One graph owns both address-taken-local heapification and explicit-allocation
promotion. Its nodes represent local storage, parameter values, statement and
terminator definitions, individual `Alloc` locations, the heap sink, and the
logical return sink. Allocation identity is the statement location rather than
the destination local, because several allocations may reuse one pointer local.

Edges carry a dereference weight:

| Operation | Weight |
| --- | ---: |
| assignment, move, cast, aggregate membership | 0 |
| address-of | -1 |
| dereference or load | +1 |

Projected fields are merged with their base local in this milestone. A forward
CFG fixed point tracks the definitions that can reach every local through
branches, loops, normal and cleanup edges, moves, `StorageLive`, and
`StorageDead`. Raw-pointer casts preserve provenance. Ordinary scalar
loads/stores do not: concrete types are inspected structurally, so arrays,
tuples, structs, enums, closures, `Span`, strings, pointers, references, and
existentials carry provenance only when their concrete contents can. Unresolved
or recursive types remain conservative.

Tracing from the heap and return sinks determines placement and the minimum
return dereference depth. Graph-distance saturation or unsupported MIR makes
every parameter capturing/returning and leaves allocations managed.

## Calls and summaries

Direct calls are resolved after substituting the caller's concrete generic
arguments. Interface requirements are resolved to the selected implementation,
so `Hashable.hash` in `Dictionary[string, Value]` analyzes the string
implementation and its concrete `SipHasher13` argument rather than the abstract
requirement.

Each concrete callee has only this summary:

```text
InstanceEscapeSummary {
  params: [
    ParamEscapeSummary {
      heap_capture: bool,
      return_deref: optional u8,
    }
  ]
}
```

The compiler builds a deterministic direct-call graph, partitions it into
strongly connected components, and iterates each component to a monotone fixed
point. Summaries are compilation-session data keyed by `Instance`.

Every compiler-known runtime and intrinsic parameter has one effect:
`NoCapture`, `Capture`, `Return`, or `CaptureAndReturn`. Missing Taro-runtime
classifications are compiler errors. Raw `memcpy` and `memmove` synchronously
copy bytes and do not retain either pointer; typed element writes remain the
operation that establishes a captured element value. Genuinely indirect,
virtual, arbitrary C, and blocking calls remain conservative.

## Applying placement

An address-taken local is heapified only when its address reaches the heap or an
escaping return/call path. A nonescaping `Alloc` becomes independent stack
storage; overlapping instances of one allocation site in a loop remain managed
because one stack slot could not represent their simultaneous lifetimes.

Promoted storage is explicitly zeroed before its reference is published. If
the promoted type can contain a managed reference, a separate typed backing
reference is null-initialized at entry and assigned at the allocation site.
Compiler-only `KeepAlive` uses retain that backing reference only in blocks
where graph provenance says an alias is live. This gives precise GC liveness
enough type information to scan the stack object without retaining it for the
entire function. Pointer-free promoted values require no backing root.

The rewrite preserves projected destinations, moves, source/debug scopes, and
cleanup edges. Dead-store and dead-local cleanup runs immediately afterward;
safepoints and their live-root subsets are computed only from the rewritten
body. `Body.escape_locals` remains temporary transformation storage rather than
a serialized analysis interface.

## Async bridge

Source async bodies need safe local placement before coroutine-frame lowering,
when concrete poll instances do not yet exist. They use the same graph in a
conservative bridge mode: unknown generic and virtual calls capture reference
arguments, and only required heap-local decisions are applied. Allocation-site
promotion is disabled there. Synthesized constructor, poll, and drop instances
later use normal instance finalization.

## Current limits and deferred work

- Projection fields share base-local provenance; field-sensitive escape is not
  implemented.
- Indirect, unresolved virtual, arbitrary C, and blocking calls conservatively
  capture and return relevant arguments.
- Overlapping loop allocations are not transformed into dynamic stack arenas.
- Summaries are recomputed per compilation session rather than persisted.
- Dictionary layout, SipHash intrinsics, aggregate ABI, List growth, allocator
  batching, and GC pacing require separate evidence-based plans.

Focused coverage lives in `compiler/src/mir/optimize/escape_graph.rs`; runtime
and intrinsic contract coverage lives in `compiler/src/runtime_abi.rs`. The
release checkpoint and generated-MIR evidence are recorded in
`development/benchmarks/monkey_host_gap/README.md`.
