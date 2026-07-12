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
  unlinks shadow frames and removes persistent roots.
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
- Pending polls must either mark `current_task_blocked` by registering a
  runtime wait, or the executor will requeue the task cooperatively.
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

- Channels track send and receive waiters separately.
- Mutexes and rwlocks track logical task ownership so finalization can release
  locks held by cancelled or panicked tasks.
- Rwlocks prefer queued writers over new readers.
- `task_finalized(task)` removes the task from all waiter queues, releases
  owned mutex/rwlock state, and wakes the next eligible waiters.
- `collect_ready_waiters` is the final pass that catches waiters made ready by
  the cleanup itself.

## GC Safepoints

Executor threads participate in the stop-the-world collector.

- Worker and I/O threads attach to the GC before they are exposed to the
  scheduler.
- Workers leave the safepoint while polling user async code and re-enter it
  immediately after polling returns or panics.
- Idle workers remain parked at a safepoint.
- Rooted and spawned async frames are persistent roots while live. Finalization
  unlinks shadow frames before removing roots.

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
