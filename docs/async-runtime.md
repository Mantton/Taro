# Async Runtime Invariants

This document records the contracts that the compiler, standard library, and
runtime rely on for Taro async execution. The current runtime intentionally
keeps these language-level semantics in Taro-owned code; dependency-backed
reactor work, such as a future `mio` migration, should preserve these
invariants before changing behavior.

## Async Handle ABI

Compiler-generated async functions return an opaque runtime handle created by
`__rt__async_create(frame, poll_fn, drop_fn, mobility)`.

- `frame` is the compiler-generated async frame. Non-null frames are registered
  as GC persistent roots while the handle or scheduled task is live.
- `poll_fn(frame, ctx, out)` returns `0` for pending and nonzero for ready. The
  runtime currently passes a null `ctx`.
- `drop_fn(frame)` must destroy the frame exactly once when the handle is
  completed, cancelled, panicked, reclaimed, or otherwise torn down.
- `__rt__async_poll(handle, out)` owns the one-shot transition to completed for
  a handle and calls `drop_fn` once on readiness.
- `__rt__async_destroy(handle)` is the final handle cleanup path. It also
  destroys the suspended frame and removes its persistent root.
- `__rt__async_cancel(handle)` gives a suspended compiler-generated child one
  cancellation poll so its active language-level cleanups run, then destroys
  the handle. Runtime-provided leaf futures without cleanup state are destroyed
  directly if that poll remains pending.
- `__rt__async_run_root(handle, out)` installs a rooted scheduler session and
  drives the root handle to completion.

The compiler-visible async ABI names live in
`compiler/src/mir/optimize/async_transform.rs`. Runtime changes must not rename
or reshape these symbols without a compiler/std migration.

## Task Lifecycle

A scheduled task occupies a `(slot index, generation)` token. The generation
prevents stale task handles from observing a reused slot.

- New tasks start `occupied=true`, `completed=false`, `queued=false`,
  `running=false`, and are immediately scheduled.
- `queued=true` means exactly one scheduler queue owns the task token.
- `running=true` means exactly one worker is polling the task. A running task
  cannot also be queued; wakeups during polling set `wake_requested`.
- Pending polls must register a typed wait reason, or the executor requeues the
  task cooperatively. Reasons cover task/group joins, timers, I/O, channels,
  mutexes, and rwlocks.
- Completion, cancellation, and panic all pass through task finalization:
  I/O waits are cancelled, sync ownership/waiters are finalized, timers are
  cleared, GC roots are removed, and the async handle is destroyed.
- An owned `Task[T]` is cancelled and transferred to the executor when its
  live handle leaves scope without being consumed. Hidden move-aware compiler
  flags ensure only the current owner performs this cleanup.
- `Task.detach()` transfers an existing handle without cancellation, while
  `std.task.detached(...)` provides the same behavior at the launch site.
  Detached output is discarded and its slot is reclaimed at completion.
- Until recursive `Drop` support is available, automatic ownership cleanup is
  limited to direct `Task` locals and parameters. A container of tasks must be
  drained so each handle is awaited or detached before the container is lost.
- Completed, still-owned tasks remain occupied until the awaiter consumes and
  reclaims the result. This preserves one-shot `Task[T]` result ownership.
- A panic remains silent while an owned task can still be observed. Calling
  `Task.result()` moves its report into a GC-backed `PanicPayload`; detaching or
  abandoning the handle reports it exactly once as `unobserved task panic`.
- `PanicPayload.message()` borrows its original message, and
  `PanicPayload.rethrow()` restores the captured report. The serialized backing
  storage is reclaimed by the GC even when a payload is nested or discarded.
- Reclaimed slots are put on `free_slots` and may be reused only after the
  generation is advanced.

## Task Diagnostics

Every spawned task retains a bounded causal chain containing its parent spawn
sites. `std.task.dump()` writes a stable snapshot of live task states, source
locations, wait reasons, and task-to-task dependencies to stderr. Captured task
panics include the same causal chain after the synchronous Taro stack.

Set `TARO_DEADLOCK_TIMEOUT_MS` to a positive millisecond value to enable the
watchdog. After that interval without a task poll, the runtime prints one
snapshot. A definitive internal wait cycle fails the async root with
`executor deadlock detected`; timer, I/O, and unmatched channel waits are
reported as external waits and continue running. The watchdog is disabled when
the variable is absent or zero.

### Runtime metrics and tracing

`taro run --runtime-stats` writes a human-readable executor and GC summary to
stderr when the executor session ends. It includes the effective worker count,
task lifecycle and queue counters, steals and parks, timer and I/O wakes, live
and peak task counts, allocation and heap totals, and percentiles over up to the
newest 1,024 GC pause samples. A
synchronous program that never starts the executor still prints a zero-task
summary with its process GC totals.

`taro run --runtime-trace` writes a timestamped event trace to stderr. Events
cover task spawning, polling, completion, cancellation, panic, queue targets,
steals, parks, timer registration and wakeup, I/O and synchronization waits,
I/O wakeups, and GC pauses. The trace retains the newest 4,096 events by
default. Set `TARO_RUNTIME_TRACE_CAPACITY` between 1 and 65,536 to change the
bound; the trace heading reports how many older events were dropped.

The CLI flags set `TARO_RUNTIME_STATS=1` and `TARO_RUNTIME_TRACE=1` for the
child process. Those variables can also be set directly for an already-built
program and accept `1`/`0`, `true`/`false`, or `yes`/`no`. Diagnostic output is
intentionally line-oriented and grep-friendly. When tracing is disabled, event
strings are not formatted or allocated.

`TARO_WORKERS` must be a positive integer. Invalid worker or diagnostic values
fail with a `runtime configuration error` instead of being silently ignored.

## Wake Contract

All wakes are token-based and deduplicated by task slot state.

- Waking a non-live, stale, completed, or already queued task is a no-op.
- Waking a running task sets `wake_requested`; after the poll returns pending,
  the task is scheduled again.
- Pinned tasks always target their owner worker.
- Movable tasks prefer the last worker on external wakes and may enter the
  global injector on cooperative suspension.
- Batched wakes unpark touched worker queues and a bounded number of global
  workers.

## Timers

Timers are stored as heap entries plus a latest-registration table.

- Registering the same deadline for the same task is a no-op.
- Registering a new deadline pushes a new heap entry and updates
  `TimerState.latest`.
- Stale heap entries are ignored unless their deadline and sequence match the
  latest table entry.
- Completion, cancellation, panic, and teardown clear the task's latest timer
  entry so old heap entries cannot wake finalized tasks.

## Selection And Deadlines

`std.task.select(first, second)` runs heterogeneous async closures concurrently
and returns `Result[SelectResult[A, B], TaskError>`. `std.task.race` applies the
same behavior to two branches with one result type. The runtime selection future
registers one parent as waiter on both owned tasks and checks the first branch
before the second; if both are ready in the same observation, the first wins.

`std.task.withTimeout(duration, operation)` returns `Result[T, TimeoutError>`.
`TimeoutError.timedOut` is distinct from `TimeoutError.operation(TaskError)`.
The task/deadline future yields once on initial registration, so immediately
ready work wins a zero-duration tie, then observes task completion before the
deadline on subsequent polls.

All three APIs cancel and drain losing work before returning. Selection-handle
destruction removes every child waiter, and deadline-handle destruction also
invalidates its timer entry. A winner error has precedence; otherwise a panic
raised while cancelling the losing operation is returned rather than hidden.

## I/O Waits

The Unix reactor owns adopted file descriptors and maps readiness events back to
task tokens.

- `register_wait(source_id, task, interest)` adds the task to the source's
  read/write waiter set and arms platform readiness.
- Linux uses epoll one-shot rearming; macOS uses kqueue one-shot events.
- `cancel_task(task)` removes the task from every source waiter set.
- `close_source(source_id)` removes the source, closes the file descriptor, and
  returns each affected waiter once so the executor can wake them.
- Readiness delivery drains the relevant waiter list and must never emit the
  same task token twice for one event batch.

## Sync Waits

Runtime sync primitives are task-token based rather than OS-thread based.

- `std.sync.bounded[T]` and `unbounded[T]` return separate `Sender[T]` and
  `Receiver[T]` handles. Only senders can send or close, and only receivers can
  receive. Both endpoints are cheap shared copies; closure is explicit rather
  than inferred from the last sender.
- Sending to a closed channel is an expected concurrency outcome represented by
  `ChannelSendError.closed` or `ChannelTrySendError.closed`, not a panic.
- Channels track send and receive waiters separately. Buffered values carry GC
  roots until received or until the channel storage is reclaimed.
- Mutexes and rwlocks track logical task ownership so finalization can release
  locks held by cancelled or panicked tasks.
- Public sync handles are GC-managed. Once all endpoint or lock references are
  unreachable, a post-sweep runtime reclaimer releases the backing slot. Manual
  `destroy` functions remain available only through the low-level `std.sys`
  layer.
- Direct guards use explicit `defer { guard.unlock() }`. `withLock`, `withRead`,
  and `withWrite` install that deferred unlock internally.
- Rwlocks prefer queued writers over new readers.
- `task_finalized(task)` removes the task from all waiter queues, releases
  owned mutex/rwlock state, and wakes the next eligible waiters.
- `collect_ready_waiters` is the final pass that catches waiters made ready by
  the cleanup itself.

## GC Safepoints

Executor threads participate in the non-moving, stop-the-world mark-sweep
collector. Safepoints are explicit MIR effects rather than an accidental
property of calls:

- Every managed MIR body has an entry poll. The compiler also places a
  deterministic set of loop polls that covers every CFG cycle, and a verifier
  rejects a body if any cycle remains that does not cross a poll.
- Calls are classified as `NoGc`, `ManagedSafepoint`, `RuntimeSafepoint`, or
  `BlockingSafepoint`. Every runtime ABI entry has an authoritative
  classification; an unclassified entry is a compiler error. Taro calls are
  managed safepoints, ordinary C ABI calls and intrinsics do not collect, and
  foreign work that may block must use `extern "blocking"`.
- Stack roots are selected per site from whole-local temporal liveness and
  definite initialization, including normal and cleanup continuations. The
  analysis is intentionally not field-sensitive. Typed root descriptors do,
  however, visit only the active enum variant and handle niche-pointer
  optionals without inventing a tag.
- Lowered tuple, struct, and closure construction publishes whole-local
  initialization only after its contiguous field stores complete; the
  compiler-only marker emits no code. Enum construction instead publishes with
  its final discriminator store after the payload. No safepoint may split
  either publication sequence.
- `std.runtime.keepAlive(value)` is a compiler-only liveness use. It extends the
  lifetime of `value` through that point but emits no native call or safepoint.
- A physical function containing any collecting site remains `noinline`, with
  LLVM tail-call elimination disabled and synchronous unwind metadata, even
  when that site has no live roots. MIR inlining may inline across those sites
  before the final root maps are computed. Preserving and exposing the frame is
  required because managed callers transfer responsibility for GC-bearing call
  arguments to the callee's entry map, and the collector must walk across a
  rootless callee to reach mapped callers.
- Every collecting site, including a rootless poll, publishes a nonzero
  frame-local selector and an exact selector-table entry. The return PC
  identifies the physical function, and the runtime reads its selector from the
  parked frame instead of treating machine-address order as execution order.
  Same-PC alternatives remain separate, so descriptors from inactive
  control-flow paths are never unioned.

- Worker and I/O threads attach to the GC before they are exposed to the
  scheduler.
- Workers leave the safepoint while polling user async code and re-enter it
  immediately after polling returns or panics.
- Idle workers remain parked at a safepoint.
- `TARO_GC_STRESS=1` keeps the collection-needed flag set so every generated
  poll takes the slow path and starts a collection; this is intended for root
  and rendezvous regression tests.
- Rooted and spawned async frames are persistent roots while live. Finalization
  destroys their compiler frames before removing those roots.
- A foreign declaration using `extern "blocking"` is wrapped with
  `__rt__gc_enter_blocking`/`__rt__gc_exit_blocking`. Its compiler stack-map
  selector and roots are published before `__rt__gc_enter_blocking` parks and
  walks the frame; collection does not wait for the foreign call to return.
  Blocking functions must not call back into Taro before the annotated call
  returns.

Each mutator checks out at most one small-object span for every size class and
scan/no-scan lane. Removing a free slot from a warm checked-out span is
owner-exclusive and takes no global GC mutex. Checkout/refill, large
allocations, and collection still use the global collector lock. A mutator
flushes all checked-out spans before it publishes `at_safepoint`, detaches,
enters blocking work, or begins collection; root walking starts only after
every parked mutator owns no span.

Every allocation is explicitly zeroed, including reused slots and scavenged
pages. The allocator writes slot metadata first and then release-stores the
allocation bit. Scanners acquire-load that bit before reading the metadata.
This publication order, rather than memory-map freshness, is the correctness
contract. Managed buffers continue to scan their full capacity, so collection
owners must clear every vacated element slot.

### GC pacing and memory controls

GC configuration is parsed once, before the collector is used. Invalid values
terminate immediately with `runtime configuration error: ...`.

- `TARO_GC_PERCENT` defaults to `100`, accepts an integer from `0` through
  `10000`, and accepts `off` to disable percentage-triggered automatic
  collection. The normal heap goal is
  `max(1 MiB, live + live * percent / 100)`.
- `TARO_GC_MEMORY_LIMIT` defaults to unlimited. It accepts `off`, or decimal
  bytes suffixed by `B`, `KiB`, `MiB`, `GiB`, or `TiB`. This is a soft limit:
  before segment growth would cross it, the runtime performs one collection
  and scavenging attempt. If live data still requires growth, allocation
  continues above the limit and records a soft-limit exceedance instead of
  repeatedly collecting or reporting an artificial OOM. When surviving live
  bytes already exceed the limit, the normal percentage trigger is set at
  least 1 MiB above live bytes; later segment growth still gets its one pressure
  attempt.
- Mutators publish allocation debt in 64 KiB quanta and flush any remainder at
  refill, safepoint, detach, and collection. Percentage-trigger overshoot is
  therefore bounded by 64 KiB times the number of active mutators.
- `TARO_GC_STATS=1` prints collection count, live and freed bytes, the current
  heap goal and configured limit, cached-span refills, released and scavenged
  bytes, soft-limit exceedances, and cumulative allocation totals.

After sweep, the runtime releases wholly empty segments while retaining one
minimum segment and rebuilds its page map. On Unix it queries the native VM page
size and applies `DontNeed` only to wholly free, native-page-aligned subranges.
It tracks advice at that same granularity, so a 16 KiB Darwin page is never
partially advised or double-counted when allocator pages are 8 KiB. Other
platforms retain whole-segment release and treat partial-page advice as a no-op.
Reuse clears every overlapping native-page scavenged bit; explicit zeroing
remains mandatory.

The collector is intentionally still stop-the-world, non-moving, and
non-generational. Concurrent collection, compaction, pinning, write barriers,
and MMTk integration are outside this runtime contract.

## Blocking Work

`std.task.blocking(|| T)` moves a synchronous `Sendable` closure onto a bounded
native pool and suspends only the calling task. Its `T` result must also be
`Sendable`. The compiler-generated adapter frame roots closure captures while
queued or running; completed output remains in a typed GC root until consumed.

- `TARO_BLOCKING_THREADS` sets the positive worker count. The default is the
  host's available parallelism, capped at 32.
- `TARO_BLOCKING_QUEUE` sets the positive queued-job capacity. The default is
  four jobs per blocking worker.
- `TARO_BLOCKING_WARN_MS` emits a source-attributed warning when one async task
  poll occupies an executor worker for at least the configured duration. It is
  disabled when absent or zero.
- A full queue suspends producers until a worker accepts another job.
- Cancelling queued work prevents it from starting. Cancelling running work
  abandons delivery but never attempts to terminate the native thread.
- Scheduler shutdown detaches workers that are still inside native calls; they
  hold only weak scheduler references and clean their rooted job state if they
  eventually return.

## Mobility

The compiler infers async task mobility from stored async-frame locals.

- Frames containing only `Sendable` data are marked movable.
- Frames containing non-`Sendable` state are marked pinned.
- Pinned tasks must always execute on their owner worker across all waits and
  wakeups.
- Movable tasks may migrate between workers after pending polls.

## Rooted And Rootless Sessions

Async `main` and async tests use rooted sessions. Synchronous code can lazily
create a rootless session by spawning async work.

- `run_root` installs a rooted session, schedules the root task, runs worker 0,
  and lets `SessionGuard` shut down and tear down remaining work.
- `__rt__executor_finish_rootless` runs any lazily-created rootless work after a
  synchronous root returns.
- `__rt__executor_abort_rootless` drops queued rootless work without polling it;
  the test harness uses this after a panicking synchronous test.
- A rooted and rootless scheduler must never be active at the same time.
