# Async Runtime

Taro uses a multithreaded work-stealing executor on top of a non-moving
tracing collector. Async frames, class objects, collections and erased values
live in the collected heap. Collection is cooperative stop-the-world: every
mutator reaches a safepoint (an allocation, a poll in a loop or function entry,
or a parked worker) before marking starts.

## Async ABI

Compiler-generated async functions create an opaque handle from a frame, poll
function, cleanup function, and mobility flag. The cleanup entry runs registered
defers and cancels native waits; it does not destroy ordinary Taro values.

- Poll reports pending, completion, or cancellation; successful completion
  writes the result through the output pointer.
- Poll tag1 alone publishes an initialized output. The compiler-owned Task
  observer and group cursor also use tag3 for completion without a value:
  failed/cancelled Task results and exhausted groups. Their MIR has a separate
  no-output edge; it never reads uninitialized output. This
  protocol is not permission for arbitrary foreign futures to omit output.
- The frame is a collected object with the exact layout of its saved locals.
  The handle holds a persistent root on it from allocation until destruction,
  so the executor, wakers and queues never need to trace frames themselves;
  they hold handles and task tokens only.
- Completion, cancellation, panic, and handle cleanup claim the frame's
  cleanup callback once, so unwinding cannot re-enter it.
  Poll/drop use the C-unwind boundary; a missing poll thunk still completes the
  frame's cleanup, and cancellation owns the handle through a final poll unwind.
- Native adapters use the same unwind-capable boundary. A pending adapter is
  destroyed during unwind before the original panic state is reset. Registration
  rejection and explicit cancellation also preserve exact once-only cleanup.
- Cancellation may remain pending. `__rt__async_cancel_poll` retains a pending
  child and consumes it only after terminal cleanup; generated parents preserve
  their saved state and return Pending until that happens. The executor must not
  turn a pending cancellation into completion or free its frame.
- Native work retaining frame storage registers an independent completion
  token with its unpolled handle before submission. Cancellation requests stop;
  only the backend's final acknowledgment releases the frame's root. Tokens
  and their wake capabilities never contain pointers into a Taro frame. A late
  completion wakes only the original executor/task generation.
- Synchronous destruction waits for acknowledgment without holding a runtime lock. Backend acknowledgment must not depend on Taro
  execution. There is no timeout or early-release fallback. Ordinary awaited
  cancellation returns Pending to the scheduler instead of blocking a worker.
- Runtime readiness/sleep/synchronization waitables retain IDs, not caller buffer
  addresses, and can cancel through their audited drop path. Blocking jobs own
  their captures and output independently; abandonment leaves running work with
  its worker. This exemption does not apply to native I/O retaining caller buffers.
- An async root installs an executor session and drives its handle to completion.

Native request registration is an internal Rust backend contract, not a general
source FFI permission. Register with the actual unpolled owner before submission;
move the completion token into the backend request and release it only after the
last buffer access and native cleanup. Submission failure must release it too.
The token grants no thread-safety or pointer-validity guarantee for payload access.

Current reactor reads/writes perform their descriptor syscalls synchronously;
readiness waits retain only source/task identities. Filesystem/resolver/process
services copy wire inputs or finish using caller output slots before returning.
Their async blocking wrappers own their inputs independently. A future backend
that retains a caller buffer must use completion registration rather than the
ID-only/drop cancellation exemption.

The compiler-visible ABI is defined in `compiler/src/runtime_abi.rs`.
`compiler/src/mir/optimize/async_transform.rs` uses those declarations when
lowering async bodies into frames and poll/drop functions.

### Frames and the Collector

`$nativeAsyncFrameAllocate` emits the frame tuple's GC descriptor and calls
`__gc__async_frame_allocate`, which returns zeroed storage with a persistent
root. Every local that is live at the start of the body, live across some
`await`, or address-taken is a frame field, and it stays at that address
for the frame's lifetime, so references into a frame remain valid while it is
suspended or moves between workers.

Before an `await` returns pending, the poll function zeroes the fields of
locals that are dead at that await and not address-taken. A suspended frame
therefore traces only what its resumption can read. Zero is the frame's
never-initialized state, which tracing accepts for every type.

A frame becomes collectable when its handle is destroyed: after completion,
after a panic unwinds out of its poll, after cancellation finishes, or when a
task is cancelled before its first poll. An awaited child whose poll unwinds
is destroyed by `__rt__async_poll` itself, because no other owner is left.
Destruction first drains native requests, then runs the frame's drop callback,
then releases the root. Nothing closes a resource when its frame is reclaimed:
cleanup is explicit (`defer`, `close()`), and the collector runs no user code.

## Tasks

Internal queue tokens contain a slot and generation. Generations prevent stale
wakes from observing reused slots. A source `Task[T]` holds a pointer to one
collected handle object that every copy shares. The object traces the task's
result storage and owns a native outcome record, which keeps a weak binding to
the task's executor and its internal token. Control resolves through that
binding, never against an unrelated ambient executor.

Work runs independently of its handles: discarding, overwriting or collecting
every copy of a `Task` never cancels it, and there is no `detach()`. A spawned
task's slot retires as soon as the task finishes. The executor publishes the
terminal outcome (completed, cancelled or panicked) into the outcome record
after task cleanup finishes and wakes every registered waiter.

- A task is owned by at most one queue or worker.
- Waking a running task records a pending wake; waking an already queued task is
  a no-op.
- Pending tasks register a wait reason or are cooperatively requeued.
- Completion, cancellation, and panic clear timers and waits, release owned
  synchronization state and destroy the async handle.
- `result(&self)` does not consume the handle. Each observer copies the cached
  outcome as an ordinary value copy: references inside the result keep their
  identity. Repeated and concurrent observations see the same outcome.
  Abandoning one wait removes only that observer; the task and other observers
  continue. Cancelling the task itself needs `cancel()`.
- A retained handle keeps its outcome after its executor session ends. Work
  whose session ended before it published an outcome reports cancellation.
- A spawned task's panic is reported once, as `task panic: ...`, when it
  escapes the task body, whether or not any handle observes it. The payload
  stays available to every observer.
- Result publication waits for frame cleanup. A first panic during cancellation
  cleanup becomes task failure; another panic in the same unwind is fatal.
  Abandoning successful output releases its GC root without running a language
  destructor. Cancellation of an already completed task preserves its outcome;
  success also wins a cancellation request that its body never observed.
- Group tasks install their group membership and notification metadata before
  publishing runnable work. A fast movable task cannot complete ahead of its
  registration. Completion transfers the GC result-buffer root lease into
  the group's ready queue; the allocation stays at a stable address.
- Closing a group cancels its remaining children. Its numeric
  identity stays reserved until every child finalizes, including a poll that
  returns Ready after cancellation. Late results are discarded outside scheduler
  locks, and completed group-child task slots are reclaimed immediately.
- Native blocking workers retain a weak binding to their originating executor
  through adapter and result cleanup. They do not retain an indefinitely blocked
  executor, and an expired binding cannot resolve task tokens against a later
  executor session. Original-session teardown has already disposed those slots.
- Spawned/group results use exact GC layout descriptors and persistent roots.
  Successful polling publishes initialization before frame cleanup;
  pending/cancelled bytes never become initialized output.
- Retrieval copies ordinary values. Abandoning a result releases its root;
  embedded Task handles are ordinary shared values, so losing them does not
  cancel their work. Scheduler state transitions and native cleanup callbacks
  complete outside slot/group locks and executor TLS scopes.

Movable tasks may run on any worker; frames are collected objects, and managed
values cross workers freely, including closures with shared reference captures.
All compiler-generated source frames are movable; worker affinity is available
only to internal native task protocols. A wake for a movable task goes to its last
worker's queue unless that worker is mid-poll, in which case it goes to the
global injector so an idle worker can run it.

Any value may cross workers: tasks, channels and blocking work capture
references, raw pointers and shared class values without a transfer bound, and
the program synchronizes them itself (mutexes, channels, or its own protocol).
The native queue publishes and receives one message under synchronization; its
opaque storage and native handle fields use package visibility.
External safe code cannot retag an endpoint or fabricate a native lock handle. Raw
channel creation and byte transfer require unsafe contracts.

## Waiting

Timers use a heap plus a latest-registration table. Entries whose deadline or
sequence no longer matches the table are ignored. Finalization removes the
task's active registration.

`std::task::select`, `race`, and `withTimeout` run their branches concurrently.
The first branch wins a simultaneous tie. Losing work is cancelled and drained
before the operation returns. A panic encountered while draining a loser is
returned as a task error even if the winning branch succeeded. Draining is
cooperative: a timed-out operation that never reaches a cancellation
checkpoint keeps `withTimeout` waiting past its deadline until it finishes.

Scoped children are drained even when their scope ends early. The tasks behind
a `select`/`race`/`withTimeout`, and task-group children still live when their
scope ends, are scoped to the task that created them. A task's terminal outcome
is published only after its scoped children have finished; cancellation or a
panic that ends the parent first cancels them. The parent's remaining defers
have already run by then, since a cancelled or panicking task never resumes
ordinary code. Repeated cancellation is idempotent and cannot skip this drain.
Group identities carry a creation serial, so a group reference that escaped its
scope is rejected (`task group used after its scope ended`) rather than reaching
a later group that reuses the slot.

Unix I/O sources map readiness to task tokens. Linux uses one-shot epoll and
macOS uses one-shot kqueue. Closing a source removes its waiters, closes the
descriptor, and wakes each affected task once.

Channels, mutexes, and rwlocks track logical task ownership rather than OS
threads. Cancelling or panicking tasks are removed from waiter queues and
release locks they own. Rwlocks prefer queued writers. Public synchronization
handles retain native shared owners; low-level manual destruction is confined
to internal unsafe APIs. Queued values retain their GC payloads. Native lock
leases may keep registry state alive until their holding task finalizes.

Mutex/RwLock are inline `@NoCopy` values: share references, not value copies.
`taro vet` diagnoses accidental copies without changing normal compilation.
Mutex uses `tryLock`/`lock`/`unlock`; RwLock uses `tryReadLock`/`readLock`/
`readUnlock` and `tryWriteLock`/`writeLock`/`writeUnlock`. Try operations return
false for contention. Access protected storage with `value()` while holding the
appropriate acquisition, or use `withLock`/`withRead`/`withWrite` for scoped
release. There are no public acquisition guard types.
Read acquisitions do not impose immutability; callers synchronize shared access
and use write acquisitions before modifying data visible to other readers.

## Blocking Work

`std::task::blocking` runs a closure on a bounded native pool without
blocking an executor worker. A full queue suspends producers. Cancelling queued
work prevents it from starting; cancelling running work abandons delivery but
does not terminate the native thread.

Adapter polling, frame cleanup and result publication share one panic boundary.
A first cleanup panic is reported through the job; another panic during unwind
is fatal. The running worker retains the adapter and result roots independently
of the observer. Cancellation marks running work abandoned without reclaiming
its live storage. Completed results become observable or lose their root after
abandonment; ordinary values have no destructor. Queued work that never starts
never publishes an initialized result. Neither the closure nor its result has
a language transfer bound.

- `TARO_BLOCKING_THREADS` sets the positive worker count. The default is host
  parallelism capped at 32.
- `TARO_BLOCKING_QUEUE` sets the positive queue capacity. The default is four
  jobs per worker.
- `TARO_BLOCKING_WARN_MS` warns when one async poll occupies a worker for at
  least the configured duration. It is disabled when absent or zero.

Invalid or zero blocking-thread/queue settings fall back to their defaults.
Invalid warning durations disable warnings.

Foreign declarations that may block must use `extern "blocking"`. Generated
code records the native blocking boundary; the foreign function must not call
back into Taro. Pointer targets need an explicit liveness and completion contract.

## Native Execution Boundaries

Workers, blocking adapters and static initializers install independent
stack-overflow protection. Scheduler-identity scopes preserve the originating
session through callbacks and cleanup, including after a producer thread has
adopted a different ambient session.

Threads that run Taro code are registered mutators. A thread parked in a
runtime wait has published its roots and counts as stopped for a collection.
Generated code also parks around every `extern "blocking"` call, passing its
frame's stack pointer instead of walking its own stack: a collection that runs
while the call is blocked scans the frozen stack above that point
conservatively, which the non-moving heap makes safe, so a call that never
returns cannot stall collection and an unblocked call pays no stack walk.
Either way the thread waits for any collection in progress before touching
managed memory again. Functions passed directly to foreign calls are entered
through a compiler-generated callback shim: the first callback on a thread the
runtime did not create registers it, and every callback parks its thread again
on return (with no roots for an idle foreign thread, or with the blocked
frame's range when a blocking call called back), so a foreign thread idling in
C never stalls collection. Foreign code holds managed values across calls only
through `std::runtime::Handle`, a persistent root keyed by a never-reused id;
`std::runtime::keepAlive` is a compiler liveness use with no runtime cost. Cycles are reclaimed like any other unreachable object.
`std::weak::Weak[T]` reads return `none` once their target has been collected.
`TARO_RUNTIME_STATS=1` reports collections, allocation totals, pause
percentiles and phase times alongside the scheduler counters.

## Resource Handles

Files, process pipes, sockets and async streams are shared handles: copies use
one descriptor. Each native operation leases the descriptor for exactly its own
system call, and `close` stops new leases and releases the descriptor once the
last in-flight operation returns (Go's `poll.FD` discipline). A read blocked on
a pipe therefore keeps the descriptor open and still delivers its bytes; later
operations on any copy report `closed`, and no operation can reach a descriptor
number the kernel has handed to a later open. Reactor sources close
immediately because their waits hold no lease, and closing wakes their waiters.
Lease ids, async source ids and directory cursor ids are never reused, so a
stale copy fails with `closed` rather than touching another resource. Copies of
a `ReadDir` share one cursor and receive distinct entries; a close by any copy,
including one reaching the end, ends iteration for all of them. Locks hold
native ownership per task: `withLock` unlocks through `defer` on panic or
cancellation, and a task that finishes while holding or waiting for a lock
releases it so the next waiter can proceed.

## Diagnostics

`std::task::dump()` writes live tasks, source locations, wait reasons, and task
dependencies to stderr. Panics include the bounded causal spawn chain.

- `TARO_DEADLOCK_TIMEOUT_MS` enables the deadlock watchdog when a positive
  integer; absent, zero, or invalid values disable it.
- `taro run --runtime-stats` prints executor totals.
- `taro run --runtime-trace` prints recent scheduler, I/O and synchronization events.
- `TARO_RUNTIME_TRACE_CAPACITY` sets the retained event count from 1 to 65,536.
- `TARO_WORKERS` sets the positive executor worker count.

The CLI flags set `TARO_RUNTIME_STATS=1` and `TARO_RUNTIME_TRACE=1` for the
child process. These two variables accept `1`/`0`, `true`/`false`, and
`yes`/`no`, ignoring case and surrounding whitespace. Invalid values for
these flags, trace capacity, or worker count terminate with
`runtime configuration error: ...`.

## Sessions

Async `main` and async tests use rooted sessions. Synchronous programs can
create a rootless session by spawning work. Rooted and rootless schedulers never
run simultaneously.

A standalone program exits once `main` and its own defers return, as in Go.
Unfinished background tasks are neither cancelled nor drained: their defers do
not run, a task that never yields cannot hold the process open, and the process
exits while other workers may still be running. The main thread does not run a
worker in this mode; it waits for the root and returns to the entry shim, which
writes the diagnostics report and exits with main's status. A main panic prints
its original report and exits nonzero the same way. Retain and await a task, or
synchronize with it, when its completion or cleanup is required. Resources that
must be closed are closed explicitly before main returns.

Tasks spawned from synchronous main never start: rootless sessions begin running
only when drained, and standalone exit does not drain. Use async main to run
concurrent work.

Test and benchmark sessions keep the full teardown below, because one process
runs many of them: returning a test's root cancels its unfinished work and keeps
workers running until cancellation cleanup and native request acknowledgment
finish. Async expected-panic tests retain the outer harness catch after the
worker scope ends. There is no teardown deadline.

External wakeups retain the registered waiter's executor identity, rather than
using the native producer's current context. A retained channel or I/O source
can therefore wake a waiter in a later executor session. Global synchronization
ownership and I/O cancellation also distinguish equal-numbered tasks from
different schedulers; diagnostics show only dependencies in the relevant one.

At the final worker-stop/emergency-teardown boundary, public task registration
is closed. Native work that finishes late cannot publish new tasks into the
completed teardown snapshot. Attempting to spawn into that stopped or expired
native session panics after admission/producer locks have been released. Its
closure environment loses its root; there is no source destructor.

The earlier drain phase of a test session keeps admission open for cleanup callbacks. Newly
spawned work is registered as cancelled before its first poll, so it releases
capture roots without entering its body or registering body defers. Native
frame and wait cleanup completes before admission closes. A temporary live work
count prevents worker shutdown while those callbacks may create more work.
The final zero-work check and admission close serialize with registration.

Unobserved task panics are reported once to stderr and do not by themselves
change the process exit status. Cancellation without a cleanup panic is quiet.
The first cancellation-cleanup panic becomes that task's failure; a second panic
in the same unwind remains fatal. Initialized statics are never destroyed at
exit.


## Shared Memory

Taro follows the Go memory model: programs synchronize conflicting accesses
themselves, data-race-free programs behave as some sequentially consistent
interleaving of their tasks, and racy programs are still constrained. These
operations order memory (A *happens before* B means B observes every write
that precedes A):

- **Spawn.** Everything before `spawn`/`detached` happens before the task body
  starts.
- **Completion.** A task's body, including its defers, happens before an
  `await`/`result()` that observes its outcome returns. Select, race, timeout
  and group observations follow the same rule for the branch they report.
- **Blocking work.** The `std::task::blocking` call happens before its closure
  starts, and the closure's return happens before the `await` returns.
- **Channels.** A send happens before the receive that takes that message
  completes. For a channel of capacity C, the k-th receive happens before the
  (k+C)-th send completes. Closing happens before a receive that reports the
  channel closed.
- **Locks.** A `Mutex` unlock happens before the next lock acquisition. For a
  `RwLock`, a write unlock happens before every later read or write
  acquisition, and a read unlock happens before the next write acquisition.
- **Static initialization.** A static's initializer returns before any access
  that observes the initialized value, on every thread.

`std::sync::atomic` exposes signed/unsigned integer, bool and strong reference
slots. All operations are sequentially consistent: a load observing a store
publishes the writes before that store. `add` wraps and returns the new value;
`swap` returns the old value; `compareExchange` compares scalars or reference
identity and returns success. `Reference[T]` stores `Optional[&T]` and keeps its
current target alive. A loaded reference is independently strong. Atomics
synchronize their slot, not arbitrary mutation of the referenced object.

Share atomics by reference and do not copy after first use. Their `@NoCopy`
attribute lets `taro vet` diagnose accidental copies, like locks. Zero storage
is valid; `::new()` also constructs zero/false/empty slots. WaitGroup is deferred.

Under a race, a read of a managed pointer observes some whole pointer written
to that location: codegen accesses shared pointer words with one unordered
atomic access and copies large pointer-bearing values word by word (see
`docs/codegen.md`), so racing tasks never follow a torn pointer. Other
word-sized scalars are single aligned accesses. Multiword values (strings,
slices, existentials, enum tag/payload pairs, structs) may be observed one
component at a time. A racy read of coupled fields, such as a pointer and its
length, can produce an inconsistent value and corrupt memory; the GC does not
make such a program safe.

## Executor Publication Boundaries

The executor retains its crossbeam work-stealing queues and mutex-protected
slot transitions. These are Rust/native resource protocols, separate from
Taro's ordinary copy semantics.

| Boundary | Protection | Regression evidence |
| --- | --- | --- |
| Poll versus cancellation | TaskSlot claims running state before removing a frame pointer; cancellation records a request | cancellation_and_duplicate_queue_claims_cannot_poll_or_drop_a_running_frame |
| Migration | Movable work may change workers; internal pinned work retains its worker | movable_tasks_can_migrate |
| Result publication | GC result storage stays rooted through delivery or abandonment; unpublished bytes are never observed | result_roots_survive_delivery_and_retire_on_abandonment, failed_task_result_does_not_publish_uninitialized_value_bytes |
| Repeated observation | Shared Task handles observe one cached terminal outcome | terminal_result_is_observed_repeatedly |
| Stale wakes and groups | Generation-checked task tokens and retained group identities reject stale work | stale_token_rejected_after_slot_reuse, destroyed_group_reserves_its_id_until_live_children_finalize |

Unsafe Rust Send/Sync implementations rely on these synchronized publication
and claimant contracts. They grant no unsynchronized access permission to user
code. Native callbacks and session teardown preserve their explicit panic and
cleanup boundaries; GC reachability determines ordinary value liveness.

### Descriptor close completion

Resource-handle copies share a descriptor lease. `close()` rejects new native
operations immediately. If no operation is in flight it performs OS close and
returns its error. Otherwise success acknowledges a deferred close request; the
last in-flight native call performs OS close. A deferred close error is reported
on stderr and counted in `TARO_RUNTIME_STATS` as `deferred_close_errors`.
`live_leases` and `pending_close` expose remaining descriptor leases. Handles
require explicit close; garbage collection has no resource finalizers.

Close does not wait for an arbitrary synchronous syscall to return. Waiting
while a syscall needs application work on the same worker, or while holding a
reactor lock, can deadlock. Async source close still cancels readiness waiters.
The process-wide lease table remains deliberately simple; sharding or per-lease
handles should follow a measured descriptor-heavy workload, not the Monkey CPU
benchmark.

### Foreign callback panics

A panic in a Taro callback runs its Taro cleanup, restores the foreign-thread
GC state, and terminates the process with a diagnostic. It cannot unwind through
a plain C ABI boundary. Blocking foreign calls restore their GC state on both
normal return and unwind before continuing Taro cleanup.
