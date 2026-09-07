# Async Runtime

Taro uses a multithreaded work-stealing executor integrated with its precise,
stop-the-world garbage collector.

## Async ABI

Compiler-generated async functions create an opaque handle from a frame, poll
function, drop function, and mobility flag.

- Poll reports pending, completion, or cancellation; successful completion
  writes the result through the output pointer.
- The frame is a persistent GC root until its async handle is destroyed.
- Completion, cancellation, panic, and destruction drop the frame exactly once.
- Cancellation gives suspended language futures one poll so active cleanup can
  run before destruction.
- An async root installs an executor session and drives its handle to completion.

The compiler-visible ABI is defined in `compiler/src/runtime_abi.rs`.
`compiler/src/mir/optimize/async_transform.rs` uses those declarations when
lowering async bodies into frames and poll/drop functions.

## Tasks

A task token contains a slot and generation. Generations prevent stale handles
from observing reused slots.

- A task is owned by at most one queue or worker.
- Waking a running task records a pending wake; waking an already queued task is
  a no-op.
- Pending tasks register a wait reason or are cooperatively requeued.
- Completion, cancellation, and panic clear timers and waits, release owned
  synchronization state, remove GC roots, and destroy the async handle.
- `Task[T]` is one-shot. Awaiting consumes its result.
- Dropping a live owned task cancels it. `Task.detach()` transfers it to the
  executor and discards its result.
- Automatic ownership cleanup covers direct `Task` locals and parameters.
  Containers of tasks must be drained by awaiting or detaching each element.
- Task panics remain observable through `Task.result()`. Detached or abandoned
  panics are reported once.

Movable tasks may run on any worker. A frame containing non-`Sendable` state is
pinned to its owner worker. Async closures with borrowed captures are also
pinned.

## Waiting

Timers use a heap plus a latest-registration table. Entries whose deadline or
sequence no longer matches the table are ignored. Finalization removes the
task's active registration.

`std.task.select`, `race`, and `withTimeout` run owned branches concurrently.
The first branch wins a simultaneous tie. Losing work is cancelled and drained
before the operation returns. A panic encountered while draining a loser is
returned as a task error even if the winning branch succeeded.

Unix I/O sources map readiness to task tokens. Linux uses one-shot epoll and
macOS uses one-shot kqueue. Closing a source removes its waiters, closes the
descriptor, and wakes each affected task once.

Channels, mutexes, and rwlocks track logical task ownership rather than OS
threads. Cancelling or panicking tasks are removed from waiter queues and
release locks they own. Rwlocks prefer queued writers. Public synchronization
handles are GC-managed; low-level manual destruction is confined to `std.sys`.

## Blocking Work

`std.task.blocking` runs a `Sendable` closure on a bounded native pool without
blocking an executor worker. A full queue suspends producers. Cancelling queued
work prevents it from starting; cancelling running work abandons delivery but
does not terminate the native thread.

- `TARO_BLOCKING_THREADS` sets the positive worker count. The default is host
  parallelism capped at 32.
- `TARO_BLOCKING_QUEUE` sets the positive queue capacity. The default is four
  jobs per worker.
- `TARO_BLOCKING_WARN_MS` warns when one async poll occupies a worker for at
  least the configured duration. It is disabled when absent or zero.

Invalid or zero blocking-thread/queue settings fall back to their defaults.
Invalid warning durations disable warnings.

Foreign declarations that may block must use `extern "blocking"`. Generated
code publishes roots before parking the mutator, and the foreign function must
not call back into Taro.

## GC Integration

Executor workers and the I/O driver attach to the GC. Workers leave the safepoint
while polling Taro code and re-enter it immediately afterward; idle workers
remain parked.

Managed MIR bodies normally have an entry poll and loop polls covering every
CFG cycle. Bounded, acyclic, non-allocating synchronous leaves can omit the
entry poll when they have no calls or escaping locals; they return to their
caller's polls instead.
Calls declare one of four effects: `NoGc`, `ManagedSafepoint`,
`RuntimeSafepoint`, or `BlockingSafepoint`. Missing runtime classifications are
compiler errors.

Stack maps contain initialized locals live at each collecting site. Typed
descriptors scan only the active enum variant. `std.runtime.keepAlive(value)`
extends liveness through its source location without emitting a call.

Each collecting function retains its physical frame and unwind information,
including at rootless sites. A frame-local selector distinguishes sites that
share a machine PC.

Small allocations use per-mutator cached spans. Warm allocation removes and
zeroes a slot, writes metadata, and publishes its allocation bit without the
global GC lock. Mutators flush cached spans before parking, detaching, entering
blocking work, or collecting.

Managed buffers are scanned to capacity, so owners must clear vacated elements.
Allocation metadata is written before the allocation bit is release-published;
scanners acquire-load the bit before reading metadata.

The collector is non-moving, non-generational mark-sweep. After sweep it
releases empty segments and advises wholly free page-aligned ranges on Unix.

### GC Configuration

- `TARO_GC_PERCENT` defaults to `100`, accepts `0` through `10000`, and accepts
  `off` to disable percentage-triggered collection.
- `TARO_GC_MEMORY_LIMIT` accepts `off` or bytes suffixed by `B`, `KiB`, `MiB`,
  `GiB`, or `TiB`. It is a soft limit: collection and scavenging are attempted
  before growth, but live data may exceed it.
- `TARO_GC_STRESS=1` requests collection at every generated poll.
- `TARO_GC_STATS=1` prints heap, allocation, collection, cache, scavenging, and
  soft-limit counters.

With percentage collection enabled, the base heap goal is
`max(1 MiB, live + live * percent / 100)`. While live data is at or below the
soft limit, the goal is capped by that limit but kept at least one byte above
live data. If live data exceeds the limit, the goal backs off to at least
`live + 1 MiB` to avoid repeatedly collecting an unchanged live heap. Setting
the percentage to `off` disables this trigger; soft-limit checks before heap
growth still apply. Mutators publish allocation debt in 64 KiB quanta.

Invalid percentage or memory-limit settings terminate with
`runtime configuration error: ...`. `TARO_GC_STATS` enables its report only
for the exact value `1`. `TARO_GC_STRESS` is disabled when absent, empty,
`0`, or `false` (case-insensitive, with surrounding whitespace ignored);
other nonempty values enable it.

## Diagnostics

`std.task.dump()` writes live tasks, source locations, wait reasons, and task
dependencies to stderr. Panics include the bounded causal spawn chain.

- `TARO_DEADLOCK_TIMEOUT_MS` enables the deadlock watchdog when a positive
  integer; absent, zero, or invalid values disable it.
- `taro run --runtime-stats` prints executor and GC totals.
- `taro run --runtime-trace` prints recent scheduler, I/O, synchronization, and
  GC events.
- `TARO_RUNTIME_TRACE_CAPACITY` sets the retained event count from 1 to 65,536.
- `TARO_WORKERS` sets the positive executor worker count.

The CLI flags set `TARO_RUNTIME_STATS=1` and `TARO_RUNTIME_TRACE=1` for the
child process. These two variables accept `1`/`0`, `true`/`false`, and
`yes`/`no`, ignoring case and surrounding whitespace. Invalid values for
these flags, trace capacity, or worker count terminate with
`runtime configuration error: ...`.

## Sessions

Async `main` and async tests use rooted sessions. Synchronous programs can
create a rootless session by spawning work. Rootless work is completed after a
successful synchronous root or discarded after a panicking test. Rooted and
rootless schedulers never run simultaneously.
