pub(crate) mod outcome;
pub use outcome::*;
mod output;
mod shutdown;
use output::TaskOutput;

use crossbeam_deque::{Injector, Steal, Stealer, Worker};
use crossbeam_utils::sync::{Parker, Unparker};
use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};
use std::fmt::Write as _;
use std::io::Write;
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU8, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock, RwLock, Weak};
use std::thread::{self, JoinHandle};
use std::time::{Duration as StdDuration, Instant};

use crate::garbage_collector::{GcDesc, GcStatsSnapshot, stats_snapshot};
use crate::hot_mutex::HotMutex;
use crate::io_poller::{self, Interest};
use crate::observability::{RuntimeDiagnostics, RuntimeDiagnosticsConfig, quote_field};
use crate::task::{__rt__async_destroy, TaskMobility, async_handle_mobility};

type TaskIndex = usize;
type TaskGeneration = u32;
pub(crate) type TaskToken = u64;

/// Scheduler-local task numbers are not process-wide identities. Global
/// synchronization/I/O registries must retain this pair through finalization.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct TaskIdentity {
    scheduler: u64,
    token: TaskToken,
}

impl TaskIdentity {
    pub(crate) fn belongs_to(self, scheduler: u64) -> bool {
        self.scheduler == scheduler
    }
    #[cfg(test)]
    pub(crate) const fn fixture(scheduler: u64, token: u64) -> Self {
        Self { scheduler, token }
    }
}

static NEXT_SCHEDULER_ID: AtomicU64 = AtomicU64::new(1);

fn allocate_scheduler_identity() -> u64 {
    NEXT_SCHEDULER_ID
        .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
        .expect("executor identity space exhausted")
}

/// A wake-only capability bound to the executor that registered a waiter.
/// External producers can outlive their own executor or run without any TLS
/// context. Clone this under their registry lock and dispatch after unlocking.
#[derive(Clone)]
pub(crate) struct TaskWake {
    scheduler: Weak<Scheduler>,
    identity: TaskIdentity,
}

#[cfg(all(test, unix))]
pub(crate) fn test_task_wake(token: TaskToken) -> TaskWake {
    TaskWake {
        scheduler: Weak::new(),
        identity: TaskIdentity {
            scheduler: u64::MAX,
            token,
        },
    }
}

impl TaskWake {
    fn new(scheduler: &Arc<Scheduler>, token: TaskToken) -> Self {
        Self {
            scheduler: Arc::downgrade(scheduler),
            identity: scheduler.task_identity(token),
        }
    }

    pub(crate) fn token(&self) -> TaskToken {
        self.identity.token
    }

    pub(crate) fn identity(&self) -> TaskIdentity {
        self.identity
    }

    pub(crate) fn wake(&self) {
        if let Some(scheduler) = self.scheduler.upgrade() {
            scheduler.wake_tasks(&[self.identity.token], false);
        }
    }

    /// Wake a task whose I/O is ready.
    pub(crate) fn wake_for_io(&self) {
        if let Some(scheduler) = self.scheduler.upgrade() {
            scheduler.wake_tasks(&[self.identity.token], true);
        }
    }
}

struct ReactorCheck {
    polls: u32,
    at: Instant,
}
impl ReactorCheck {
    fn new() -> Self {
        Self {
            polls: 0,
            at: Instant::now(),
        }
    }
}

const IDLE_YIELDS: usize = 8;
/// One worker in `YIELD_FAIRNESS_INTERVAL` turns takes a yielded task first, so
/// tasks that give way to other work aren't overtaken forever by work that keeps coming.
const YIELD_FAIRNESS_INTERVAL: usize = 16;
/// How often the I/O thread reviews whether workers are keeping up.
const LOAD_REVIEW_INTERVAL: StdDuration = StdDuration::from_millis(1);
/// The wait for a turn at which a worker's yielded tasks are shared with its peers.
const MAX_YIELD_DELAY: StdDuration = StdDuration::from_millis(1);
/// Tasks woken by the reactor run here while it keeps up, so the fewest workers
/// stay awake for the load. A busy core costs every other core: on a machine with
/// few fast cores, a worker polling sockets for little gain slows everything else.
const GATHERING_WORKER: usize = 0;
/// While the reactor's tasks gather on one worker, that worker reads it too: it
/// sleeps there rather than behind a second thread, which would add a thread wake
/// to every wait. It also looks in after this many polls or this long, whichever
/// comes first, so a queue that never empties doesn't leave sockets unread.
const READS_REACTOR: bool = cfg!(unix);
const REACTOR_CHECK_POLLS: u32 = 61;
const REACTOR_CLOCK_POLLS: u32 = 8;
const REACTOR_CHECK_INTERVAL: StdDuration = StdDuration::from_micros(200);
// Who is reading the reactor. Two threads blocked on one kqueue slow each other.
const POLLER_NONE: u8 = 0;
const POLLER_WORKER: u8 = 1;
const POLLER_IO_THREAD: u8 = 2;

/// Tasks that gave up their turn on one worker. They look runnable without
/// necessarily having work to do, so unlike other queued tasks they neither wake
/// peers nor let peers take them. The load review shares them when they wait too long.
#[repr(align(128))]
struct YieldQueue {
    tasks: Injector<TaskToken>,
    // Written by the owning worker alone. The review compares successive `polls`.
    polls: AtomicU64,
    turns: AtomicUsize,
}

impl YieldQueue {
    fn new() -> Self {
        Self {
            tasks: Injector::new(),
            polls: AtomicU64::new(0),
            turns: AtomicUsize::new(0),
        }
    }

    fn pop(&self) -> Option<TaskToken> {
        loop {
            match self.tasks.steal() {
                Steal::Success(task_id) => return Some(task_id),
                Steal::Empty => return None,
                Steal::Retry => std::hint::spin_loop(),
            }
        }
    }
}

/// Where a scheduled task should run.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Placement {
    /// Whichever worker gets to it first.
    Anywhere,
    /// This worker if it can get to it soon.
    Prefer(usize),
    /// A terminal publisher is returning to this worker's queue. A movable
    /// observer can continue there without waking another worker mid-poll.
    Continuation(usize),
    /// Behind the other work of the worker that just polled it.
    Yielded(usize),
    /// The gathering worker.
    Gather,
}

impl From<Option<usize>> for Placement {
    fn from(preferred_worker: Option<usize>) -> Self {
        preferred_worker.map_or(Placement::Anywhere, Placement::Prefer)
    }
}
/// How long a worker out of tasks keeps looking before it sleeps. A short gap
/// between tasks costs less to wait out than a sleep and wake.
const IDLE_SPIN: StdDuration = StdDuration::from_micros(20);
const TASK_TOKEN_INDEX_BITS: u32 = 32;
const TASK_TOKEN_INDEX_MASK: u64 = (1u64 << TASK_TOKEN_INDEX_BITS) - 1;
const TASK_INITIAL_GENERATION: TaskGeneration = 1;
const MAX_TASK_TRACE_FRAMES: usize = 32;
// Spawn sites are immutable native diagnostics. Descendants share their
// parents' owned strings; materialize value frames only for a panic report.
type SpawnTrace = Vec<Arc<crate::panic_unwind::TaskTraceFrame>>;
#[cfg(test)]
use crate::test_layout::noscan as test_gc_layout;

#[derive(Clone, Debug, PartialEq, Eq)]
enum WaitReason {
    Task(TaskToken),
    Tasks([TaskToken; 2]),
    TaskTimeout {
        task: TaskToken,
        deadline: Instant,
    },
    TaskGroup(u64),
    Sleep(Instant),
    Io {
        source_id: usize,
        interest: Interest,
    },
    Sync {
        sync_id: usize,
        kind: crate::sync::WaitKind,
    },
    BlockingCapacity,
    BlockingWork,
    NativeRequest,
    /// A task owned by a different executor session.
    ForeignTask,
}

#[derive(Clone, Debug)]
struct SpawnMetadata {
    frame: Arc<crate::panic_unwind::TaskTraceFrame>,
}

thread_local! {
    // Spawn sites repeat, so a request-per-task server would otherwise copy the
    // same two strings for every task it starts. Reuse needs equal content: a
    // name can be a managed string, whose address says nothing about its bytes.
    static RECENT_SPAWN_SITES: RefCell<[Option<Arc<crate::panic_unwind::TaskTraceFrame>>; 8]> =
        const { RefCell::new([const { None }; 8]) };
}

impl SpawnMetadata {
    fn new(name: String, file: String, line: usize, column: usize) -> Self {
        Self {
            frame: Arc::new(crate::panic_unwind::TaskTraceFrame {
                name,
                file,
                line,
                column,
            }),
        }
    }

    fn root() -> Self {
        Self::new("<async root>".into(), String::new(), 0, 0)
    }

    fn anonymous() -> Self {
        Self::new("<runtime task>".into(), String::new(), 0, 0)
    }

    fn from_runtime(
        name: crate::panic_unwind::RtString,
        file: crate::panic_unwind::RtString,
        line: usize,
        column: usize,
    ) -> Self {
        let bytes = |text: crate::panic_unwind::RtString| -> &[u8] {
            if text.ptr.is_null() || text.len == 0 {
                &[]
            } else {
                unsafe { std::slice::from_raw_parts(text.ptr, text.len) }
            }
        };
        let name_bytes = bytes(name);
        let name_bytes = if name_bytes.is_empty() {
            b"<runtime task>".as_slice()
        } else {
            name_bytes
        };
        let file_bytes = bytes(file);
        let index = (line ^ column.rotate_left(3) ^ name_bytes.len() ^ file_bytes.len()) & 7;
        let recent = RECENT_SPAWN_SITES.try_with(|sites| {
            sites.borrow()[index]
                .as_ref()
                .filter(|site| {
                    site.line == line
                        && site.column == column
                        && site.name.as_bytes() == name_bytes
                        && site.file.as_bytes() == file_bytes
                })
                .cloned()
        });
        if let Ok(Some(frame)) = recent {
            return Self { frame };
        }
        let metadata = Self::new(
            String::from_utf8_lossy(name_bytes).into_owned(),
            String::from_utf8_lossy(file_bytes).into_owned(),
            line,
            column,
        );
        let _ = RECENT_SPAWN_SITES.try_with(|sites| {
            sites.borrow_mut()[index] = Some(Arc::clone(&metadata.frame));
        });
        metadata
    }
}

#[derive(Clone, Debug)]
struct TaskDiagnosticSnapshot {
    token: TaskToken,
    state: &'static str,
    spawn_trace: SpawnTrace,
    wait_reason: Option<WaitReason>,
}

#[derive(Debug)]
struct TaskDump {
    text: String,
    cycle: Option<Vec<TaskToken>>,
}

// Frozen native-backend panic carrier. The GC entry produces managed bytes
// directly instead; it never passes this owner through the source string ABI.

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct TimerEntry {
    deadline: Instant,
    sequence: u64,
    task_token: TaskToken,
}

#[derive(Clone, Copy)]
struct TimerRegistration {
    deadline: Instant,
    sequence: u64,
}

struct TimerState {
    heap: BinaryHeap<Reverse<TimerEntry>>,
    latest: Vec<Option<TimerRegistration>>,
}

struct TaskSlot {
    inner: HotMutex<TaskSlotInner>,
}

struct TaskSlotInner {
    // `occupied` plus `generation` is the authority for whether a task token is
    // live. Queue/running/completed flags must be updated while holding this
    // lock so stale wakeups cannot resurrect a finalized slot.
    generation: TaskGeneration,
    occupied: bool,
    handle: *mut u8,
    // Output storage remains independently owned through terminal cleanup.
    out_ptr: *mut u8,
    out_buf: Option<TaskOutput>,
    completed: bool,
    cancelled: Arc<AtomicBool>,
    detached: bool,
    polled: bool,
    queued: bool,
    running: bool,
    wake_requested: bool,
    // Set once the terminal outcome is published. Completion may wait for
    // scoped children between `completed` and publication.
    published: bool,
    // Spawned tasks publish their terminal outcome here for every handle.
    shared: Option<Arc<TaskShared>>,
    owner_worker: usize,
    last_worker: usize,
    mobility: TaskMobility,
    group_id: Option<u64>,
    is_spawned: bool,
    panic_info: Option<crate::panic_unwind::PanicReport>,
    spawn_trace: SpawnTrace,
    wait_reason: Option<WaitReason>,
    // Whether finishing has to clear this task out of the I/O reactor.
    waited_on_io: bool,
    // Whether finishing has a timer to clear, under a lock every task would take.
    registered_sleep: bool,
}

// SAFETY: inner serializes generation/queue/running transitions. Exactly one
// running worker owns handle/frame/output access; completion takes those
// pointers out under the lock before cleanup runs outside it. Movable frames
// are GC-traced and may run on any worker; pinned frames stay on owner_worker.
// Raw pointer representation itself supplies no transfer or alias guarantee.
unsafe impl Send for TaskSlot {}
unsafe impl Sync for TaskSlot {}

/// Clear the slot before unwinding destroys its worker-owned handle. This is
/// needed for root panics too: session teardown must not destroy a stale pointer
/// after the original unwind has already released it. This guard owns the
/// handle and releases the slot lock before running its cleanup.
struct TaskPollUnwind<'a> {
    slot: &'a TaskSlot,
    owner: Option<crate::task::OwnedAsyncHandle>,
}
impl Drop for TaskPollUnwind<'_> {
    fn drop(&mut self) {
        if let Some(owner) = self.owner.take() {
            self.slot
                .inner
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .handle = std::ptr::null_mut();
            // Every poll now has a catch continuation. Keep its running
            // claim through cleanup; terminal publication releases it after
            // preserving a root report or a spawned-task failure.
            drop(owner);
        }
    }
}

impl TaskSlot {
    fn new(
        generation: TaskGeneration,
        handle: *mut u8,
        out_ptr: *mut u8,
        out_buf: Option<TaskOutput>,
        owner_worker: usize,
        mobility: TaskMobility,
    ) -> Self {
        Self {
            inner: HotMutex::new(TaskSlotInner {
                generation,
                occupied: true,
                handle,
                out_ptr,
                out_buf,
                completed: false,
                cancelled: Arc::new(AtomicBool::new(false)),
                detached: false,
                polled: false,
                queued: false,
                running: false,
                wake_requested: false,
                published: false,
                shared: None,
                owner_worker,
                last_worker: owner_worker,
                mobility,
                group_id: None,
                is_spawned: false,
                panic_info: None,
                spawn_trace: vec![SpawnMetadata::anonymous().frame],
                wait_reason: None,
                waited_on_io: false,
                registered_sleep: false,
            }),
        }
    }
}

#[derive(Default)]
struct RuntimeStats {
    // Only a diagnostics report reads these. Without one, workers shouldn't be
    // sharing and writing a cache line many times per task.
    enabled: bool,
    tasks_created: AtomicU64,
    task_polls: AtomicU64,
    task_completions: AtomicU64,
    task_cancellations: AtomicU64,
    task_panics: AtomicU64,
    peak_live_tasks: AtomicU64,
    queue_enqueues: AtomicU64,
    pinned_enqueues: AtomicU64,
    worker_enqueues: AtomicU64,
    steals: AtomicU64,
    parks: AtomicU64,
    wakeups: AtomicU64,
    global_injects: AtomicU64,
    worker_unparks: AtomicU64,
    global_unparks: AtomicU64,
    timer_wakeups: AtomicU64,
    timer_registrations: AtomicU64,
    io_wakeups: AtomicU64,
}

#[derive(Debug, Default)]
struct RuntimeStatsSnapshot {
    tasks_created: u64,
    task_polls: u64,
    task_completions: u64,
    task_cancellations: u64,
    task_panics: u64,
    peak_live_tasks: u64,
    queue_enqueues: u64,
    pinned_enqueues: u64,
    worker_enqueues: u64,
    steals: u64,
    parks: u64,
    wakeups: u64,
    global_injects: u64,
    worker_unparks: u64,
    global_unparks: u64,
    timer_wakeups: u64,
    timer_registrations: u64,
    io_wakeups: u64,
}

impl RuntimeStats {
    #[inline]
    fn add(&self, counter: &AtomicU64, amount: u64) {
        if self.enabled {
            counter.fetch_add(amount, Ordering::Relaxed);
        }
    }

    fn snapshot(&self) -> RuntimeStatsSnapshot {
        RuntimeStatsSnapshot {
            tasks_created: self.tasks_created.load(Ordering::Relaxed),
            task_polls: self.task_polls.load(Ordering::Relaxed),
            task_completions: self.task_completions.load(Ordering::Relaxed),
            task_cancellations: self.task_cancellations.load(Ordering::Relaxed),
            task_panics: self.task_panics.load(Ordering::Relaxed),
            peak_live_tasks: self.peak_live_tasks.load(Ordering::Relaxed),
            queue_enqueues: self.queue_enqueues.load(Ordering::Relaxed),
            pinned_enqueues: self.pinned_enqueues.load(Ordering::Relaxed),
            worker_enqueues: self.worker_enqueues.load(Ordering::Relaxed),
            steals: self.steals.load(Ordering::Relaxed),
            parks: self.parks.load(Ordering::Relaxed),
            wakeups: self.wakeups.load(Ordering::Relaxed),
            global_injects: self.global_injects.load(Ordering::Relaxed),
            worker_unparks: self.worker_unparks.load(Ordering::Relaxed),
            global_unparks: self.global_unparks.load(Ordering::Relaxed),
            timer_wakeups: self.timer_wakeups.load(Ordering::Relaxed),
            timer_registrations: self.timer_registrations.load(Ordering::Relaxed),
            io_wakeups: self.io_wakeups.load(Ordering::Relaxed),
        }
    }
}

/// Current runtime limitations:
/// - Unannotated synchronous blocking calls still occupy an async worker;
///   callers must use `std.task.blocking` or the explicit blocking FFI ABI.
/// - TLS-affine foreign code remains unsafe for movable tasks unless future
///   runtime pinning support is added.
struct Scheduler {
    // Serialize public task registration with teardown's task snapshot. The
    // lock is never held during source cleanup or an arbitrary native call.
    admission: HotMutex<()>,
    identity: u64,
    rooted: bool,
    test_mode: bool,
    worker_count: usize,
    tasks: RwLock<Vec<Arc<TaskSlot>>>,
    task_index: TaskSlotIndex,
    free_slots: HotMutex<Vec<TaskIndex>>,
    injector: Injector<TaskToken>,
    local_workers: Mutex<Vec<Option<Worker<TaskToken>>>>,
    stealers: Vec<Stealer<TaskToken>>,
    pinned_queues: Vec<WorkerQueue>,
    remote_queues: Vec<WorkerQueue>,
    // Private tokens survive unrelated thread::park calls during GC root
    // publication, native cleanup or standard-library synchronization.
    worker_parkers: Mutex<Vec<Option<Parker>>>,
    worker_unparkers: Vec<Unparker>,
    worker_registered: Vec<AtomicBool>,
    // Set while a worker polls a task. Movable wakes avoid a busy worker's
    // private queue, which only that worker drains.
    worker_polling: Vec<AtomicBool>,
    // Published before the final queue check, so an enqueue either becomes
    // visible to that check or leaves a token for a worker committed to park.
    worker_idle: Vec<AtomicBool>,
    worker_joins: Mutex<Vec<JoinHandle<()>>>,
    io_join: Mutex<Option<JoinHandle<()>>>,
    watchdog_join: Mutex<Option<JoinHandle<()>>>,
    blocking_pool: OnceLock<BlockingPool>,
    timers: HotMutex<TimerState>,
    next_timer_sequence: AtomicU64,
    idle_workers: AtomicUsize,
    searching_workers: AtomicUsize,
    yielded: Vec<YieldQueue>,
    // Whether the gathering worker keeps up, as of the last load review.
    gathering: AtomicBool,
    // The I/O thread is blocked with no review due, because every worker slept.
    review_asleep: AtomicBool,
    reactor_poller: AtomicU8,
    io_unparker: Unparker,
    io_parker: Mutex<Option<Parker>>,
    incomplete_tasks: AtomicUsize,
    shutdown: AtomicBool,
    started: AtomicBool,
    wake_cursor: AtomicUsize,
    progress_epoch: AtomicU64,
    // Draining permits cleanup registration; shutdown finally closes it.
    draining: AtomicBool,
    // A standalone `main` ends the process when its root finishes: background
    // tasks are neither cancelled nor drained, as in Go.
    exit_on_root: AtomicBool,
    root_exited: Mutex<bool>,
    root_exit_signal: Condvar,
    root_panic: Mutex<Option<crate::panic_unwind::PanicReport>>,
    worker_panic: Mutex<Option<String>>,
    fatal_runtime_error: Mutex<Option<String>>,
    deadlock_timeout: Option<StdDuration>,
    blocking_warn_threshold: Option<StdDuration>,
    stats: RuntimeStats,
    diagnostics: RuntimeDiagnostics,
    diagnostics_reported: AtomicBool,
    gc_stats_baseline: GcStatsSnapshot,
    task_groups: Mutex<Vec<Option<TaskGroupState>>>,
    free_group_slots: Mutex<Vec<usize>>,
    scope_links: HotMutex<ScopeLinks>,
    // How many tasks `scope_links` has a parent for. Zero means a finishing task
    // can have no parent or children, with no need for the lock or its maps.
    scope_link_count: AtomicUsize,
}

/// Terminal outcome of a task whose publication may wait for scoped children.
enum Terminal {
    Completed(Option<TaskOutput>),
    Cancelled,
    Panicked(crate::panic_unwind::PanicReport),
}

struct PendingTerminal {
    terminal: Terminal,
    shared: Option<Arc<TaskShared>>,
    group_id: Option<u64>,
    detached: bool,
}

// SAFETY: a pending terminal is only moved between scheduler locks; group
// output was fully published before the move, as for CompletedGroupTask.
unsafe impl Send for PendingTerminal {}

/// Children scoped to a parent task: group children still live when their
/// scope ends and the tasks behind select/race/withTimeout. A parent's terminal
/// outcome is published only after its scoped children have finished, so a
/// cancelled or panicking parent drains them instead of leaving them running.
#[derive(Default)]
struct ScopeLinks {
    // Keyed by runtime-issued tokens, updated for every scoped task.
    children: rustc_hash::FxHashMap<TaskToken, ChildList>,
    parent: rustc_hash::FxHashMap<TaskToken, TaskToken>,
    pending: rustc_hash::FxHashMap<TaskToken, PendingTerminal>,
}

/// A parent's scoped children, almost always the one behind a withTimeout.
#[derive(Clone, Default)]
struct ChildList {
    first: Option<TaskToken>,
    rest: Vec<TaskToken>,
}
impl ChildList {
    fn push(&mut self, child: TaskToken) {
        if self.first.is_none() {
            self.first = Some(child);
        } else {
            self.rest.push(child);
        }
    }
    fn remove(&mut self, child: TaskToken) {
        if self.first == Some(child) {
            self.first = (!self.rest.is_empty()).then(|| self.rest.remove(0));
        } else {
            self.rest.retain(|other| *other != child);
        }
    }
    fn is_empty(&self) -> bool {
        self.first.is_none()
    }
    fn len(&self) -> usize {
        usize::from(self.first.is_some()) + self.rest.len()
    }
    fn iter(&self) -> impl Iterator<Item = TaskToken> + '_ {
        self.first.iter().chain(&self.rest).copied()
    }
}

struct TaskGroupState {
    // Slot index in the low 32 bits plus a creation serial, so an alias that
    // escaped a finished scope cannot reach a later group in the same slot.
    id: u64,
    // A hash set, as a server group can hold every open connection.
    tasks: rustc_hash::FxHashSet<TaskToken>,
    completed: VecDeque<CompletedGroupTask>,
    discard_results: bool,
    result_size: usize,
    waiter: Option<TaskToken>,
    spawning_closed: bool,
    // A destroyed group keeps its identity until every registered child has
    // delivered its terminal notification. A running poll may still return a
    // value after cancellation, so cancellation alone cannot permit ID reuse.
    destroy_pending: bool,
    cancelled: bool,
    cancel_on_panic: bool,
    ready_status: u8,
    panic_report: Option<crate::panic_unwind::PanicReport>,
}

const GROUP_INDEX_MASK: u64 = u32::MAX as u64;
static NEXT_GROUP_SERIAL: AtomicU64 = AtomicU64::new(1);

fn group_index(group_id: u64) -> usize {
    (group_id & GROUP_INDEX_MASK) as usize
}

fn live_group_slot(
    groups: &mut [Option<TaskGroupState>],
    group_id: u64,
) -> Option<&mut Option<TaskGroupState>> {
    groups
        .get_mut(group_index(group_id))
        .filter(|slot| slot.as_ref().is_some_and(|group| group.id == group_id))
}

fn live_group_mut(
    groups: &mut [Option<TaskGroupState>],
    group_id: u64,
) -> Option<&mut TaskGroupState> {
    live_group_slot(groups, group_id).and_then(Option::as_mut)
}

struct CompletedGroupTask {
    buf: TaskOutput,
}

// SAFETY: publication finishes every write before transfer into this queue.
// The scheduler mutex serializes the transfer of independently owned output.
// No payload access or destructor runs on a Rust queue move. This is the
// opaque scheduler boundary; synchronization of source values remains explicit.
unsafe impl Send for CompletedGroupTask {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BlockingJobPhase {
    New,
    Queued,
    Running,
    Completed,
    Panicked,
}

struct BlockingJobInner {
    adapter: *mut u8,
    output: Option<TaskOutput>,
    phase: BlockingJobPhase,
    abandoned: bool,
    waiter: Option<TaskToken>,
    panic_report: Option<crate::panic_unwind::PanicReport>,
}

struct BlockingJob {
    inner: Mutex<BlockingJobInner>,
}

// GC roots retain the closure frame and result. Raw pointer publication and
// phase transitions occur under inner. The Running
// worker alone dereferences the extracted pointers outside that lock; abandon
// records a request and leaves cleanup to that claimant. No registry or phase
// lock surrounds a callback; user data needs its own synchronization.
unsafe impl Send for BlockingJob {}
unsafe impl Sync for BlockingJob {}

struct BlockingQueueState {
    jobs: VecDeque<Arc<BlockingJob>>,
    capacity_waiters: VecDeque<TaskToken>,
}

struct BlockingPoolState {
    scheduler: Weak<Scheduler>,
    queue_capacity: usize,
    queue: Mutex<BlockingQueueState>,
    available: Condvar,
    shutdown: AtomicBool,
    test_mode: bool,
}

struct BlockingPool {
    state: Arc<BlockingPoolState>,
    // Dropping a JoinHandle detaches the thread. Shutdown deliberately does
    // not join workers because native work already in progress may never
    // return; those workers retain only `BlockingPoolState` and a weak
    // scheduler reference.
    _joins: Mutex<Vec<JoinHandle<()>>>,
}

enum BlockingEnqueue {
    Accepted,
    Full,
    Shutdown,
}

#[repr(C)]
struct BlockingFutureFrame {
    pool: Arc<BlockingPoolState>,
    job: Arc<BlockingJob>,
    waiter: Option<TaskToken>,
    enqueued: bool,
}

thread_local! {
    static WORKER_CONTEXT: RefCell<Option<WorkerContext>> = const { RefCell::new(None) };
    // Native work may finish after its executor has been torn down. Preserve
    // identity without retaining the executor across an indefinitely blocking
    // call. Some(expired Weak) must never fall back to a later ambient session.
    static NATIVE_SCHEDULER: RefCell<Option<Weak<Scheduler>>> = const { RefCell::new(None) };
}

struct WorkerContext {
    scheduler: Arc<Scheduler>,
    worker_id: usize,
    current_task: Option<TaskToken>,
    // Cached while polling/cleaning this identity. Cancellation publication
    // remains in the slot; nested polls only need an acquire load.
    current_cancellation: Option<Arc<AtomicBool>>,
    current_wait_reason: Option<WaitReason>,
}

struct WorkerContextGuard;

impl Drop for WorkerContextGuard {
    fn drop(&mut self) {
        WORKER_CONTEXT.with(|cell| {
            *cell.borrow_mut() = None;
        });
    }
}

/// Frame destruction is still task execution. Restore its identity only for
/// that callback, before finalization retires sync ownership and slot metadata.
/// Never hold a TLS RefCell borrow while generated cleanup can reenter runtime.
struct TaskCleanupContextGuard {
    previous: Option<(
        Option<TaskToken>,
        Option<Arc<AtomicBool>>,
        Option<WaitReason>,
    )>,
    _thread_bound: std::marker::PhantomData<std::rc::Rc<()>>,
}

impl TaskCleanupContextGuard {
    fn new(scheduler: &Scheduler, task: TaskToken) -> Self {
        let previous = WORKER_CONTEXT.with(|cell| {
            let mut context = cell.borrow_mut();
            let context = context.as_mut()?;
            if !std::ptr::eq(context.scheduler.as_ref(), scheduler) {
                return None;
            }
            let (index, _) = unpack_task_token(task);
            let cancellation = scheduler.lookup_task_slot(index).map(|slot| {
                slot.inner
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .cancelled
                    .clone()
            });
            crate::task::set_polled_cancellation(
                cancellation.as_ref().map_or(std::ptr::null(), Arc::as_ptr),
            );
            Some((
                context.current_task.replace(task),
                std::mem::replace(&mut context.current_cancellation, cancellation),
                context.current_wait_reason.take(),
            ))
        });
        Self {
            previous,
            _thread_bound: std::marker::PhantomData,
        }
    }
}

impl Drop for TaskCleanupContextGuard {
    fn drop(&mut self) {
        if let Some((task, cancellation, wait)) = self.previous.take() {
            WORKER_CONTEXT.with(|cell| {
                let mut context = cell.borrow_mut();
                let context = context.as_mut().expect("cleanup lost its worker context");
                context.current_task = task;
                crate::task::set_polled_cancellation(
                    cancellation.as_ref().map_or(std::ptr::null(), Arc::as_ptr),
                );
                context.current_cancellation = cancellation;
                context.current_wait_reason = wait;
            });
        }
    }
}

pub(crate) struct NativeSchedulerGuard {
    previous: Option<Weak<Scheduler>>,
    _thread_bound: std::marker::PhantomData<std::rc::Rc<()>>,
}

impl NativeSchedulerGuard {
    fn new(scheduler: Weak<Scheduler>) -> Self {
        let previous = NATIVE_SCHEDULER.with(|cell| cell.replace(Some(scheduler)));
        Self {
            previous,
            _thread_bound: std::marker::PhantomData,
        }
    }
}

impl Drop for NativeSchedulerGuard {
    fn drop(&mut self) {
        NATIVE_SCHEDULER.with(|cell| {
            cell.replace(self.previous.take());
        });
    }
}

struct SessionGuard {
    scheduler: Arc<Scheduler>,
}

struct WorkerRuntimeGuard;

impl Drop for WorkerRuntimeGuard {
    fn drop(&mut self) {
        crate::panic_unwind::set_test_harness_active(false);
    }
}

impl Drop for SessionGuard {
    fn drop(&mut self) {
        if !self.scheduler.shutdown.load(Ordering::Acquire) {
            self.scheduler.force_shutdown();
        }
        self.scheduler.join_background_threads();
        self.scheduler.write_diagnostics_report();
        self.scheduler.teardown_remaining_tasks();
        clear_scheduler_if_current(&self.scheduler);
    }
}

impl BlockingJob {
    fn new(adapter: *mut u8, output: TaskOutput) -> Arc<Self> {
        Arc::new(Self {
            inner: Mutex::new(BlockingJobInner {
                adapter,
                output: Some(output),
                phase: BlockingJobPhase::New,
                abandoned: false,
                waiter: None,
                panic_report: None,
            }),
        })
    }

    fn abandon(&self) -> (*mut u8, Option<TaskOutput>) {
        let mut inner = self.inner.lock().unwrap();
        inner.abandoned = true;
        match inner.phase {
            BlockingJobPhase::New => {
                let adapter = std::mem::replace(&mut inner.adapter, std::ptr::null_mut());
                let output = inner.output.take();
                (adapter, output)
            }
            BlockingJobPhase::Completed | BlockingJobPhase::Panicked => {
                let output = inner.output.take();
                inner.panic_report = None;
                (std::ptr::null_mut(), output)
            }
            BlockingJobPhase::Queued | BlockingJobPhase::Running => (std::ptr::null_mut(), None),
        }
    }
}

impl BlockingPoolState {
    fn try_enqueue(&self, job: &Arc<BlockingJob>, waiter: TaskToken) -> BlockingEnqueue {
        let mut queue = self.queue.lock().unwrap();
        queue.capacity_waiters.retain(|token| *token != waiter);
        if self.shutdown.load(Ordering::Acquire) {
            return BlockingEnqueue::Shutdown;
        }
        if queue.jobs.len() >= self.queue_capacity {
            queue.capacity_waiters.push_back(waiter);
            return BlockingEnqueue::Full;
        }
        {
            let mut inner = job.inner.lock().unwrap();
            debug_assert_eq!(inner.phase, BlockingJobPhase::New);
            inner.phase = BlockingJobPhase::Queued;
            inner.waiter = Some(waiter);
        }
        queue.jobs.push_back(Arc::clone(job));
        drop(queue);
        self.available.notify_one();
        BlockingEnqueue::Accepted
    }

    fn remove_capacity_waiter(&self, waiter: TaskToken) {
        self.queue
            .lock()
            .unwrap()
            .capacity_waiters
            .retain(|token| *token != waiter);
    }

    fn pop_job(&self) -> Option<Arc<BlockingJob>> {
        let (job, capacity_waiter) = {
            let mut queue = self.queue.lock().unwrap();
            loop {
                if let Some(job) = queue.jobs.pop_front() {
                    break (Some(job), queue.capacity_waiters.pop_front());
                }
                if self.shutdown.load(Ordering::Acquire) {
                    break (None, None);
                }
                queue = crate::garbage_collector::idle_wait(|| self.available.wait(queue)).unwrap();
            }
        };
        if let Some(waiter) = capacity_waiter
            && let Some(scheduler) = self.scheduler.upgrade()
        {
            scheduler.wake_tasks(&[waiter], false);
        }
        job
    }

    fn shutdown(&self) {
        if self.shutdown.swap(true, Ordering::AcqRel) {
            return;
        }
        let queue = self.queue.lock().unwrap();
        for job in &queue.jobs {
            job.inner.lock().unwrap().abandoned = true;
        }
        drop(queue);
        self.available.notify_all();
    }
}

impl BlockingPool {
    fn new(scheduler: &Arc<Scheduler>) -> Self {
        let worker_count = configured_blocking_thread_count();
        let state = Arc::new(BlockingPoolState {
            scheduler: Arc::downgrade(scheduler),
            queue_capacity: configured_blocking_queue_capacity(worker_count),
            queue: Mutex::new(BlockingQueueState {
                jobs: VecDeque::new(),
                capacity_waiters: VecDeque::new(),
            }),
            available: Condvar::new(),
            shutdown: AtomicBool::new(false),
            test_mode: scheduler.test_mode,
        });

        let mut joins: Vec<JoinHandle<()>> = Vec::with_capacity(worker_count);
        for worker_id in 0..worker_count {
            let worker_state = Arc::clone(&state);
            let join = thread::Builder::new()
                .name(format!("taro-blocking-{worker_id}"))
                .spawn(move || {
                    let scheduler = worker_state.scheduler.clone();
                    if panic::catch_unwind(AssertUnwindSafe(|| blocking_worker_loop(worker_state)))
                        .is_err()
                        && let Some(scheduler) = scheduler.upgrade()
                    {
                        scheduler
                            .record_fatal_runtime_error("blocking pool worker panicked".into());
                    }
                });
            let join = match join {
                Ok(join) => join,
                Err(error) => {
                    state.shutdown();
                    for join in joins {
                        let _ = join.join();
                    }
                    panic!("failed to spawn blocking worker thread: {error}");
                }
            };
            joins.push(join);
        }
        Self {
            state,
            _joins: Mutex::new(joins),
        }
    }
}

/// Both owners stay outside job/queue locks. Adapter cleanup runs first, with
/// initialized output edges retained through callbacks and any unwind.
fn destroy_abandoned_blocking_resources(adapter: *mut u8, output: Option<TaskOutput>) {
    let _output = output;
    let _adapter = unsafe { crate::task::OwnedAsyncHandle::from_raw(adapter) };
}

fn destroy_abandoned_blocking_resources_on_worker(adapter: *mut u8, output: Option<TaskOutput>) {
    if crate::panic_unwind::is_unwinding() {
        destroy_abandoned_blocking_resources(adapter, output);
    } else if let Err(report) = crate::panic_unwind::catch_executor_panic(|| {
        destroy_abandoned_blocking_resources(adapter, output)
    }) {
        crate::panic_unwind::write_unobserved_task_panic(&report);
    }
}

fn poll_blocking_adapter(
    adapter: *mut u8,
    output: TaskOutput,
) -> Result<(u8, TaskOutput), crate::panic_unwind::PanicReport> {
    crate::stack_guard::guard_current_thread();
    crate::panic_unwind::catch_executor_panic(|| {
        let mut output = output;
        let owner = unsafe { crate::task::OwnedAsyncHandle::from_raw(adapter) };
        let data = output.as_mut_ptr();
        let tag = crate::task::poll_with_output_publication(
            owner.as_ptr(),
            data,
            Some(output.publication()),
        );
        // Even an invalid pending adapter must finish destruction while the
        // output owner is inside this same panic boundary.
        drop(owner);
        (tag, output)
    })
}

fn blocking_worker_loop(state: Arc<BlockingPoolState>) {
    let _scheduler_guard = NativeSchedulerGuard::new(state.scheduler.clone());
    crate::panic_unwind::set_test_harness_active(state.test_mode);
    let _runtime_guard = WorkerRuntimeGuard;

    while let Some(job) = state.pop_job() {
        let (adapter, output, should_run) = {
            let mut inner = job.inner.lock().unwrap();
            debug_assert_eq!(inner.phase, BlockingJobPhase::Queued);
            inner.phase = BlockingJobPhase::Running;
            (
                inner.adapter,
                inner
                    .output
                    .take()
                    .expect("blocking output has one worker claimant"),
                !inner.abandoned && !state.shutdown.load(Ordering::Acquire),
            )
        };

        if !should_run {
            {
                let mut inner = job.inner.lock().unwrap();
                inner.adapter = std::ptr::null_mut();
                inner.phase = BlockingJobPhase::Completed;
            }
            destroy_abandoned_blocking_resources_on_worker(adapter, Some(output));
            continue;
        }

        let poll_result = poll_blocking_adapter(adapter, output);

        let (poll_result, mut release_output) = match poll_result {
            Ok((tag, output)) => (Ok(tag), Some(output)),
            Err(report) => (Err(report), None),
        };
        let mut wake = None;
        let mut unobserved_panic = None;
        {
            let mut inner = job.inner.lock().unwrap();
            inner.adapter = std::ptr::null_mut();
            match poll_result {
                Ok(1) => inner.phase = BlockingJobPhase::Completed,
                Ok(tag) => {
                    inner.phase = BlockingJobPhase::Panicked;
                    inner.panic_report = Some(crate::panic_unwind::PanicReport {
                        message: format!(
                            "blocking closure suspended unexpectedly (poll tag {tag}); blocking work must be synchronous"
                        ),
                        backtrace: String::new(),
                        location: None,
                        logical_stack: Vec::new(),
                        task_trace: Vec::new(),
                    });
                }
                Err(report) => {
                    inner.phase = BlockingJobPhase::Panicked;
                    inner.panic_report = Some(report);
                }
            }
            if inner.abandoned {
                unobserved_panic = inner.panic_report.take();
            } else {
                if inner.phase == BlockingJobPhase::Completed {
                    inner.output = release_output.take();
                }
                wake = inner.waiter;
            }
        }
        drop(release_output);
        if let Some(report) = unobserved_panic {
            crate::panic_unwind::write_unobserved_task_panic(&report);
        }
        if let Some(waiter) = wake
            && let Some(scheduler) = state.scheduler.upgrade()
        {
            scheduler.wake_tasks(&[waiter], false);
        }
    }
}

fn set_current_blocking_wait(reason: WaitReason) {
    WORKER_CONTEXT.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let context = borrow
            .as_mut()
            .expect("blocking future polled outside executor worker");
        context.current_wait_reason = Some(reason);
    });
}

unsafe extern "C-unwind" fn blocking_future_poll(
    frame: *mut u8,
    _ctx: *mut u8,
    out: *mut u8,
) -> u8 {
    if frame.is_null() {
        return 1;
    }
    let frame = unsafe { &mut *(frame as *mut BlockingFutureFrame) };
    let waiter = current_task_token().expect("blocking future polled with no current task");
    match frame.waiter {
        Some(existing) => assert_eq!(
            existing, waiter,
            "blocking future moved between owning tasks"
        ),
        None => frame.waiter = Some(waiter),
    }

    if frame.enqueued {
        let mut inner = frame.job.inner.lock().unwrap();
        match inner.phase {
            BlockingJobPhase::Completed => {
                let output = inner.output.take();
                drop(inner);
                if let Some(output) = output {
                    unsafe { output.copy_into(out) };
                }
                return 1;
            }
            BlockingJobPhase::Panicked => {
                let report =
                    inner
                        .panic_report
                        .take()
                        .unwrap_or_else(|| crate::panic_unwind::PanicReport {
                            message: "blocking closure panicked".into(),
                            backtrace: String::new(),
                            location: None,
                            logical_stack: Vec::new(),
                            task_trace: Vec::new(),
                        });
                inner.abandoned = true;
                drop(inner);
                crate::panic_unwind::restore_panic_report(report);
                crate::panic_unwind::rethrow_restored_panic();
            }
            BlockingJobPhase::Queued | BlockingJobPhase::Running => {
                drop(inner);
                set_current_blocking_wait(WaitReason::BlockingWork);
                return 0;
            }
            BlockingJobPhase::New => {
                panic!("ICE: enqueued blocking future still has a new job")
            }
        }
    }

    match frame.pool.try_enqueue(&frame.job, waiter) {
        BlockingEnqueue::Accepted => {
            frame.enqueued = true;
            set_current_blocking_wait(WaitReason::BlockingWork);
            0
        }
        BlockingEnqueue::Full => {
            set_current_blocking_wait(WaitReason::BlockingCapacity);
            0
        }
        BlockingEnqueue::Shutdown => {
            set_current_blocking_wait(WaitReason::BlockingWork);
            0
        }
    }
}

unsafe extern "C-unwind" fn blocking_future_drop(frame: *mut u8) {
    if frame.is_null() {
        return;
    }
    let frame = unsafe { Box::from_raw(frame as *mut BlockingFutureFrame) };
    if let Some(waiter) = frame.waiter {
        frame.pool.remove_capacity_waiter(waiter);
    }
    let (adapter, output) = frame.job.abandon();
    destroy_abandoned_blocking_resources(adapter, output);
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_blocking(adapter: *mut u8, output_desc: *const u8) -> *mut u8 {
    let scheduler = current_worker_scheduler()
        .expect("std.task.blocking must be constructed on an executor worker");
    let pool = scheduler.blocking_pool_state();
    let descriptor =
        unsafe { output_desc.cast::<GcDesc>().as_ref() }.expect("blocking result descriptor");
    let output = unsafe { TaskOutput::new(descriptor) };
    let job = BlockingJob::new(adapter, output);
    let frame = Box::into_raw(Box::new(BlockingFutureFrame {
        pool,
        job,
        waiter: None,
        enqueued: false,
    }));
    crate::task::create_runtime_wait(
        frame as *mut u8,
        blocking_future_poll as *const () as *const u8,
        blocking_future_drop as *const () as *const u8,
        TaskMobility::Movable as u8,
    )
}

#[derive(Clone, Copy)]
struct WakeRequest {
    task_token: TaskToken,
    placement: Placement,
}

struct WakeBatch {
    worker_touched: Vec<bool>,
    worker_count: usize,
    global_count: usize,
}

impl WakeBatch {
    fn new(worker_count: usize) -> Self {
        Self {
            // Global-only wakes need no per-worker state. Allocate flags on
            // the first targeted wake, keeping the common injector path local.
            worker_touched: Vec::new(),
            worker_count,
            global_count: 0,
        }
    }

    fn note_worker(&mut self, worker_id: usize) {
        if worker_id >= self.worker_count {
            return;
        }
        if self.worker_touched.is_empty() {
            self.worker_touched.resize(self.worker_count, false);
        }
        self.worker_touched[worker_id] = true;
    }

    fn note_global(&mut self) {
        self.global_count += 1;
    }

    fn touched_workers(&self) -> impl Iterator<Item = usize> + '_ {
        self.worker_touched
            .iter()
            .enumerate()
            .filter_map(|(worker_id, touched)| touched.then_some(worker_id))
    }
}

fn pack_task_token(index: TaskIndex, generation: TaskGeneration) -> TaskToken {
    let raw_index = u32::try_from(index)
        .unwrap_or_else(|_| panic!("task slot index {index} exceeds token width"));
    (u64::from(generation) << TASK_TOKEN_INDEX_BITS) | u64::from(raw_index)
}

fn unpack_task_token(token: TaskToken) -> (TaskIndex, TaskGeneration) {
    let index = (token & TASK_TOKEN_INDEX_MASK) as TaskIndex;
    let generation = (token >> TASK_TOKEN_INDEX_BITS) as TaskGeneration;
    (index, generation)
}

fn format_task_token(token: TaskToken) -> String {
    let (index, generation) = unpack_task_token(token);
    format!("{index}@{generation}")
}

fn find_wait_cycle(graph: &HashMap<TaskToken, Vec<TaskToken>>) -> Option<Vec<TaskToken>> {
    fn visit(
        task: TaskToken,
        graph: &HashMap<TaskToken, Vec<TaskToken>>,
        states: &mut HashMap<TaskToken, u8>,
        stack: &mut Vec<TaskToken>,
    ) -> Option<Vec<TaskToken>> {
        states.insert(task, 1);
        stack.push(task);

        let mut dependencies = graph.get(&task).cloned().unwrap_or_default();
        dependencies.sort_unstable();
        for dependency in dependencies {
            if !graph.contains_key(&dependency) {
                continue;
            }
            match states.get(&dependency).copied().unwrap_or(0) {
                0 => {
                    if let Some(cycle) = visit(dependency, graph, states, stack) {
                        return Some(cycle);
                    }
                }
                1 => {
                    let start = stack.iter().position(|entry| *entry == dependency)?;
                    let mut cycle = stack[start..].to_vec();
                    cycle.push(dependency);
                    return Some(cycle);
                }
                _ => {}
            }
        }

        stack.pop();
        states.insert(task, 2);
        None
    }

    let mut tasks: Vec<_> = graph.keys().copied().collect();
    tasks.sort_unstable();
    let mut states = HashMap::new();
    let mut stack = Vec::new();
    for task in tasks {
        if states.get(&task).copied().unwrap_or(0) == 0
            && let Some(cycle) = visit(task, graph, &mut states, &mut stack)
        {
            return Some(cycle);
        }
    }
    None
}

/// Finds a task's slot without a lock. The scheduler touches a slot several times
/// per task from any worker, so a shared lock or reference count here is a cache
/// line that every worker fights over.
///
/// Slots are only ever added, and `Scheduler::tasks` keeps each alive for as long
/// as the scheduler, so a published pointer stays valid while it is reachable from
/// here. Chunks double in size and never move.
struct TaskSlotIndex {
    chunks: [AtomicPtr<AtomicPtr<TaskSlot>>; TaskSlotIndex::CHUNKS],
}

impl TaskSlotIndex {
    const FIRST_CHUNK_BITS: u32 = 6;
    const CHUNKS: usize = (usize::BITS - Self::FIRST_CHUNK_BITS) as usize;

    fn new() -> Self {
        Self {
            chunks: [const { AtomicPtr::new(std::ptr::null_mut()) }; Self::CHUNKS],
        }
    }

    /// (Chunk number, position within that chunk, that chunk's length.)
    fn position(index: TaskIndex) -> (usize, usize, usize) {
        let first = 1_usize << Self::FIRST_CHUNK_BITS;
        // Biasing makes each chunk start at a power of two.
        let biased = index
            .checked_add(first)
            .expect("task index space exhausted");
        let chunk = biased.ilog2() - Self::FIRST_CHUNK_BITS;
        let len = first << chunk;
        (chunk as usize, biased - len, len)
    }

    fn get(&self, index: TaskIndex) -> Option<*const TaskSlot> {
        let (chunk, position, _) = Self::position(index);
        let entries = self.chunks[chunk].load(Ordering::Acquire);
        if entries.is_null() {
            return None;
        }
        let slot = unsafe { &*entries.add(position) }.load(Ordering::Acquire);
        (!slot.is_null()).then_some(slot.cast_const())
    }

    /// The caller holds `Scheduler::tasks` for writing, so publishers are serial.
    fn publish(&self, index: TaskIndex, slot: *const TaskSlot) {
        let (chunk, position, len) = Self::position(index);
        let mut entries = self.chunks[chunk].load(Ordering::Acquire);
        if entries.is_null() {
            let allocated: Box<[AtomicPtr<TaskSlot>]> = (0..len)
                .map(|_| AtomicPtr::new(std::ptr::null_mut()))
                .collect();
            entries = Box::into_raw(allocated).cast();
            self.chunks[chunk].store(entries, Ordering::Release);
        }
        unsafe { &*entries.add(position) }.store(slot.cast_mut(), Ordering::Release);
    }
}

impl Drop for TaskSlotIndex {
    fn drop(&mut self) {
        for (chunk, entries) in self.chunks.iter_mut().enumerate() {
            let entries = *entries.get_mut();
            if !entries.is_null() {
                let len = (1_usize << Self::FIRST_CHUNK_BITS) << chunk;
                drop(unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(entries, len)) });
            }
        }
    }
}

fn next_task_generation(generation: TaskGeneration) -> TaskGeneration {
    let next = generation.wrapping_add(1);
    if next == 0 { 1 } else { next }
}

impl Scheduler {
    fn lock_admission(&self) -> crate::hot_mutex::HotMutexGuard<'_, ()> {
        // This mutex serializes publication with teardown; it protects no
        // mutable payload. A normal validation panic can unwind through its
        // caller, and must not disable later registration or cleanup.
        let guard = self.admission.lock().unwrap_or_else(|poison| {
            self.admission.clear_poison();
            poison.into_inner()
        });
        guard
    }

    fn open_admission(&self) -> crate::hot_mutex::HotMutexGuard<'_, ()> {
        let guard = self.lock_admission();
        if self.shutdown.load(Ordering::Acquire) {
            // Rejection is recoverable through the task panic boundary. Do
            // not poison admission or run captured cleanup while holding it.
            drop(guard);
            panic!("spawn called after executor shutdown");
        }
        guard
    }

    fn task_identity(&self, token: TaskToken) -> TaskIdentity {
        TaskIdentity {
            scheduler: self.identity,
            token,
        }
    }

    #[cfg(test)]
    fn new(rooted: bool, worker_count: usize) -> Arc<Self> {
        Self::new_with_diagnostics(rooted, worker_count, RuntimeDiagnostics::disabled())
    }

    fn new_with_diagnostics(
        rooted: bool,
        worker_count: usize,
        diagnostics: RuntimeDiagnostics,
    ) -> Arc<Self> {
        let mut locals = Vec::with_capacity(worker_count);
        let mut stealers = Vec::with_capacity(worker_count);
        let mut pinned_queues = Vec::with_capacity(worker_count);
        let mut remote_queues = Vec::with_capacity(worker_count);
        let mut worker_parkers = Vec::with_capacity(worker_count);
        let mut worker_unparkers = Vec::with_capacity(worker_count);
        let io_parker = Parker::new();
        let mut worker_registered = Vec::with_capacity(worker_count);
        let mut worker_polling = Vec::with_capacity(worker_count);
        for _ in 0..worker_count {
            let local = Worker::new_lifo();
            stealers.push(local.stealer());
            locals.push(Some(local));
            pinned_queues.push(WorkerQueue::new());
            remote_queues.push(WorkerQueue::new());
            let parker = Parker::new();
            worker_unparkers.push(parker.unparker().clone());
            worker_parkers.push(Some(parker));
            worker_registered.push(AtomicBool::new(false));
            worker_polling.push(AtomicBool::new(false));
        }

        Arc::new(Self {
            admission: HotMutex::new(()),
            identity: allocate_scheduler_identity(),
            rooted,
            test_mode: crate::panic_unwind::in_test_harness(),
            worker_count,
            tasks: RwLock::new(Vec::new()),
            task_index: TaskSlotIndex::new(),
            free_slots: HotMutex::new(Vec::new()),
            injector: Injector::new(),
            local_workers: Mutex::new(locals),
            stealers,
            pinned_queues,
            remote_queues,
            worker_parkers: Mutex::new(worker_parkers),
            worker_unparkers,
            worker_registered,
            worker_polling,
            worker_idle: (0..worker_count).map(|_| AtomicBool::new(false)).collect(),
            worker_joins: Mutex::new(Vec::new()),
            io_join: Mutex::new(None),
            watchdog_join: Mutex::new(None),
            blocking_pool: OnceLock::new(),
            timers: HotMutex::new(TimerState {
                heap: BinaryHeap::new(),
                latest: Vec::new(),
            }),
            next_timer_sequence: AtomicU64::new(0),
            idle_workers: AtomicUsize::new(0),
            searching_workers: AtomicUsize::new(0),
            yielded: (0..worker_count).map(|_| YieldQueue::new()).collect(),
            gathering: AtomicBool::new(true),
            review_asleep: AtomicBool::new(false),
            reactor_poller: AtomicU8::new(POLLER_NONE),
            io_unparker: io_parker.unparker().clone(),
            io_parker: Mutex::new(Some(io_parker)),
            incomplete_tasks: AtomicUsize::new(0),
            shutdown: AtomicBool::new(false),
            started: AtomicBool::new(false),
            wake_cursor: AtomicUsize::new(0),
            progress_epoch: AtomicU64::new(0),
            draining: AtomicBool::new(false),
            exit_on_root: AtomicBool::new(false),
            root_exited: Mutex::new(false),
            root_exit_signal: Condvar::new(),
            root_panic: Mutex::new(None),
            worker_panic: Mutex::new(None),
            fatal_runtime_error: Mutex::new(None),
            deadlock_timeout: configured_deadlock_timeout(),
            blocking_warn_threshold: configured_blocking_warn_threshold(),
            stats: RuntimeStats {
                enabled: cfg!(test) || diagnostics.stats_enabled,
                ..RuntimeStats::default()
            },
            diagnostics,
            diagnostics_reported: AtomicBool::new(false),
            gc_stats_baseline: stats_snapshot(),
            task_groups: Mutex::new(Vec::new()),
            free_group_slots: Mutex::new(Vec::new()),
            scope_links: HotMutex::new(ScopeLinks::default()),
            scope_link_count: AtomicUsize::new(0),
        })
    }

    fn blocking_pool_state(self: &Arc<Self>) -> Arc<BlockingPoolState> {
        Arc::clone(
            &self
                .blocking_pool
                .get_or_init(|| BlockingPool::new(self))
                .state,
        )
    }

    fn start(self: &Arc<Self>) -> Worker<TaskToken> {
        if self.started.swap(true, Ordering::AcqRel) {
            panic!("ICE: scheduler started twice");
        }

        io_poller::initialize().expect("async io reactor initialization failed");

        // A lone worker can read the reactor and fire timers itself, and nothing
        // else could run what they wake while it's busy.
        if self.worker_count > 1 || !READS_REACTOR {
            let io_scheduler = Arc::clone(self);
            let io_join = thread::Builder::new()
                .name("taro-io".into())
                .spawn(move || io_scheduler.io_driver_loop())
                .expect("failed to spawn io driver thread");
            *self.io_join.lock().unwrap() = Some(io_join);
        }

        if let Some(timeout) = self.deadlock_timeout {
            let watchdog_scheduler = Arc::clone(self);
            let watchdog_join = thread::Builder::new()
                .name("taro-deadlock-watchdog".into())
                .spawn(move || watchdog_scheduler.deadlock_watchdog_loop(timeout))
                .expect("failed to spawn deadlock watchdog thread");
            *self.watchdog_join.lock().unwrap() = Some(watchdog_join);
        }

        let mut joins = Vec::with_capacity(self.worker_count.saturating_sub(1));
        for worker_id in 1..self.worker_count {
            let scheduler = Arc::clone(self);
            let local = self.take_local_worker(worker_id);
            let join = thread::Builder::new()
                .name(format!("taro-worker-{worker_id}"))
                .spawn(move || scheduler.worker_thread_entry(worker_id, local))
                .expect("failed to spawn worker thread");
            joins.push(join);
        }
        *self.worker_joins.lock().unwrap() = joins;

        self.take_local_worker(0)
    }

    fn take_local_worker(&self, worker_id: usize) -> Worker<TaskToken> {
        self.local_workers.lock().unwrap()[worker_id]
            .take()
            .expect("ICE: missing worker deque")
    }

    fn worker_loop(self: Arc<Self>, worker_id: usize, local: Worker<TaskToken>) {
        // Native stack-overflow reporting is per-thread and independent of
        // scheduler admission or allocation ownership.
        crate::stack_guard::guard_current_thread();
        let parker = self.take_worker_parker(worker_id);
        self.register_worker_thread(worker_id);
        crate::panic_unwind::set_test_harness_active(self.test_mode);
        let _runtime_guard = WorkerRuntimeGuard;

        WORKER_CONTEXT.with(|cell| {
            *cell.borrow_mut() = Some(WorkerContext {
                scheduler: Arc::clone(&self),
                worker_id,
                current_task: None,
                current_wait_reason: None,
                current_cancellation: None,
            });
        });
        let _guard = WorkerContextGuard;

        // Between polls this loop is all that's running on this thread, so the
        // frames beneath it are all a collection needs to see.
        let outer_roots = crate::garbage_collector::OuterRoots::capture();
        let reads_reactor = READS_REACTOR && worker_id == GATHERING_WORKER;
        let mut reactor_check = ReactorCheck::new();
        loop {
            if reads_reactor {
                self.check_reactor(&mut reactor_check);
            }
            if let Some(task_id) = self.next_task(worker_id, &local) {
                self.wake_for_remaining_work(&local);
                self.run_task(worker_id, task_id);
                continue;
            }

            if self.shutdown.load(Ordering::Acquire) {
                break;
            }

            // Claimed before this worker looks idle: whoever sees it idle has to
            // know where it's sleeping. Sleeping there needs no spin first, which only
            // saved the wake of a sleep behind a second thread.
            let polling = reads_reactor
                && (self.worker_count == 1 || self.gathering.load(Ordering::Relaxed))
                && self.claim_reactor(POLLER_WORKER);

            if !polling && self.enter_search() {
                if self.spin_for_work(worker_id, &local) {
                    continue;
                }

                let mut found = false;
                for _ in 0..IDLE_YIELDS {
                    thread::yield_now();
                    if let Some(task_id) = self.next_task(worker_id, &local) {
                        self.leave_search(true);
                        self.run_task(worker_id, task_id);
                        found = true;
                        break;
                    }
                }
                if found {
                    continue;
                }
                self.leave_search(false);
            }

            self.worker_idle[worker_id].store(true, Ordering::SeqCst);
            if let Some(task_id) = self.next_task(worker_id, &local) {
                if polling {
                    self.release_reactor();
                }
                self.leave_idle_for_task(worker_id);
                self.run_task(worker_id, task_id);
                continue;
            }
            self.stats.add(&self.stats.parks, 1);
            self.record_trace("worker_park", || format!("worker={worker_id}"));
            self.idle_workers.fetch_add(1, Ordering::SeqCst);
            let ready = if polling {
                let timeout = self.next_timer_timeout();
                let ready = outer_roots.idle_wait(|| io_poller::wait(timeout));
                self.release_reactor();
                ready
            } else {
                outer_roots.idle_wait(|| parker.park());
                Vec::new()
            };
            self.worker_idle[worker_id].store(false, Ordering::SeqCst);
            self.idle_workers.fetch_sub(1, Ordering::SeqCst);
            if self.review_asleep.load(Ordering::SeqCst)
                && self.review_asleep.swap(false, Ordering::SeqCst)
            {
                // It's asleep in the reactor while tasks aren't gathering.
                if self.reactor_poller.load(Ordering::SeqCst) == POLLER_IO_THREAD {
                    io_poller::notify();
                }
                self.io_unparker.unpark();
            }
            if polling {
                self.wake_ready(ready);
                self.wake_due_timers();
            }
            self.record_trace("worker_resume", || format!("worker={worker_id}"));
        }
    }

    /// Run whatever turns up in the next moment.
    /// Become one of the workers looking for work, of which up to half may spin at
    /// a time. Work that turns up meanwhile needs to wake nobody else.
    fn enter_search(&self) -> bool {
        let mut current = self.searching_workers.load(Ordering::SeqCst);
        loop {
            if current * 2 >= self.worker_count {
                return false;
            }
            match self.searching_workers.compare_exchange_weak(
                current,
                current + 1,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => return true,
                Err(actual) => current = actual,
            }
        }
    }

    /// A searcher that found work may leave more behind it with nobody looking.
    /// One that found none goes on to its final check before it sleeps.
    fn leave_search(&self, found: bool) {
        let previous = self.searching_workers.fetch_sub(1, Ordering::SeqCst);
        if found && previous == 1 {
            self.unpark_next_worker();
        }
    }

    /// Hand off what this worker can't get to while it runs the task it just took.
    fn wake_for_remaining_work(&self, local: &Worker<TaskToken>) {
        if self.idle_workers.load(Ordering::Relaxed) != 0
            && self.searching_workers.load(Ordering::Relaxed) == 0
            && (!local.is_empty() || !self.injector.is_empty())
        {
            self.unpark_next_worker();
        }
    }

    fn spin_for_work(&self, worker_id: usize, local: &Worker<TaskToken>) -> bool {
        let until = Instant::now() + IDLE_SPIN;
        loop {
            if let Some(task_id) = self.next_task(worker_id, local) {
                self.leave_search(true);
                self.run_task(worker_id, task_id);
                return true;
            }
            if Instant::now() >= until {
                return false;
            }
            std::hint::spin_loop();
        }
    }

    fn leave_idle_for_task(&self, worker_id: usize) {
        // A notifier may have reserved this searching worker after its idle
        // publication. Its final check found different work, so hand off the
        // consumed reservation before entering an arbitrary, non-yielding poll.
        if !self.worker_idle[worker_id].swap(false, Ordering::SeqCst) {
            self.unpark_next_worker_except(Some(worker_id));
        }
    }

    fn claim_reactor(&self, poller: u8) -> bool {
        self.reactor_poller
            .compare_exchange(POLLER_NONE, poller, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
    }

    fn release_reactor(&self) {
        self.reactor_poller.store(POLLER_NONE, Ordering::SeqCst);
    }

    fn wake_ready(&self, ready: Vec<TaskWake>) {
        if ready.is_empty() {
            return;
        }
        self.stats.add(&self.stats.io_wakeups, ready.len() as u64);
        for target in ready {
            self.record_trace("io_wake", || format!("task={}", target.token()));
            target.wake_for_io();
        }
    }

    /// Between polls, on the worker that reads the reactor.
    fn check_reactor(&self, check: &mut ReactorCheck) {
        check.polls += 1;
        // The clock is too slow to read for every poll of a short request.
        if check.polls < REACTOR_CHECK_POLLS
            && (check.polls % REACTOR_CLOCK_POLLS != 0 || check.at.elapsed() < REACTOR_CHECK_INTERVAL)
        {
            return;
        }
        *check = ReactorCheck::new();
        self.wake_due_timers();
        self.read_reactor_without_waiting();
    }

    fn read_reactor_without_waiting(&self) {
        if self.claim_reactor(POLLER_WORKER) {
            let ready = io_poller::wait(Some(StdDuration::ZERO));
            self.release_reactor();
            self.wake_ready(ready);
        }
    }

    /// Watches over the workers, and reads the reactor when the worker that
    /// normally does can't: tasks no longer gather, or it's stuck in a long poll.
    fn io_driver_loop(self: Arc<Self>) {
        crate::panic_unwind::set_test_harness_active(self.test_mode);
        let _runtime_guard = WorkerRuntimeGuard;
        let parker = self
            .io_parker
            .lock()
            .unwrap()
            .take()
            .expect("ICE: missing io driver parker");
        let mut reviewed_polls = vec![0; self.worker_count];
        let mut reviewed_at = Instant::now();
        // Review once after each wake, or a worker waking for each short request
        // would wake this thread every time too.
        let mut reviewed_since_wake = false;
        while !self.shutdown.load(Ordering::Acquire) {
            let mut timeout = self.next_timer_timeout();
            // Pairs with a worker leaving its sleep: either that worker sees this
            // flag and unparks, or this thread sees it awake.
            self.review_asleep.store(true, Ordering::SeqCst);
            let resting =
                reviewed_since_wake && self.idle_workers.load(Ordering::SeqCst) == self.worker_count;
            if resting {
                reviewed_since_wake = false;
            } else {
                self.review_asleep.store(false, Ordering::SeqCst);
                timeout = Some(
                    timeout.map_or(LOAD_REVIEW_INTERVAL, |due| due.min(LOAD_REVIEW_INTERVAL)),
                );
            }
            let gathering = self.gathering.load(Ordering::Relaxed);
            let worker_polling = self.reactor_poller.load(Ordering::SeqCst) == POLLER_WORKER;
            // It went to sleep while this thread had the reactor. Let it take over.
            if gathering
                && !worker_polling
                && self.worker_idle[GATHERING_WORKER]
                    .compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst)
                    .is_ok()
            {
                self.unpark_worker(GATHERING_WORKER);
            }
            if !gathering && self.claim_reactor(POLLER_IO_THREAD) {
                let ready = io_poller::wait(timeout);
                self.release_reactor();
                self.review_asleep.store(false, Ordering::SeqCst);
                self.wake_ready(ready);
            } else {
                match timeout {
                    Some(timeout) => parker.park_timeout(timeout),
                    None => parker.park(),
                }
                self.review_asleep.store(false, Ordering::SeqCst);
            }
            self.wake_due_timers();
            let elapsed = reviewed_at.elapsed();
            if elapsed >= LOAD_REVIEW_INTERVAL {
                reviewed_at += elapsed;
                self.review_load(&mut reviewed_polls, elapsed);
                reviewed_since_wake = true;
            }
        }
    }

    /// Share out yielded tasks that are waiting too long for their worker.
    fn review_load(&self, reviewed_polls: &mut [u64], elapsed: StdDuration) {
        for (worker_id, yielded) in self.yielded.iter().enumerate() {
            let polls = yielded.polls.load(Ordering::Relaxed);
            let finished = polls.wrapping_sub(reviewed_polls[worker_id]);
            reviewed_polls[worker_id] = polls;
            let waiting = yielded.tasks.len() as u64;
            let stuck = finished == 0 && !self.worker_idle[worker_id].load(Ordering::Relaxed);
            let delay = elapsed.as_nanos() * waiting as u128 / finished.max(1) as u128;
            let share = if stuck {
                // It's in one long poll, and nothing says that will end soon.
                waiting
            } else if waiting >= 2 && delay > MAX_YIELD_DELAY.as_nanos() {
                waiting / 2
            } else {
                0
            };
            if worker_id == GATHERING_WORKER {
                self.gathering
                    .store(!stuck && share == 0, Ordering::Relaxed);
            }
            if share == 0 {
                continue;
            }
            for _ in 0..share {
                let Some(task_id) = yielded.pop() else {
                    break;
                };
                self.injector.push(task_id);
            }
            self.unpark_next_worker();
        }
    }

    fn deadlock_watchdog_loop(self: Arc<Self>, timeout: StdDuration) {
        let mut last_epoch = self.progress_epoch.load(Ordering::Acquire);
        let mut reported_epoch = None;
        while !self.shutdown.load(Ordering::Acquire) {
            thread::park_timeout(timeout);
            if self.shutdown.load(Ordering::Acquire) {
                break;
            }
            if self.incomplete_tasks.load(Ordering::Acquire) == 0 {
                reported_epoch = None;
                last_epoch = self.progress_epoch.load(Ordering::Acquire);
                continue;
            }

            let epoch = self.progress_epoch.load(Ordering::Acquire);
            if epoch != last_epoch {
                last_epoch = epoch;
                reported_epoch = None;
                continue;
            }
            if reported_epoch == Some(epoch) {
                continue;
            }

            let heading = format!(
                "stuck task diagnostic after {} ms without executor progress",
                timeout.as_millis()
            );
            let dump = self.build_task_dump(&heading);
            let mut stderr = std::io::stderr().lock();
            let _ = stderr.write_all(dump.text.as_bytes());
            // A stuck runnable task needs its enqueue/park history as well as
            // the wait graph. Only emit it when tracing was requested.
            if let Some(trace) = self.diagnostics.trace_report(self.worker_count) {
                let _ = stderr.write_all(trace.as_bytes());
            }
            let _ = stderr.flush();
            drop(stderr);

            if dump.cycle.is_some() {
                self.record_fatal_runtime_error("executor deadlock detected".into());
                break;
            }
            reported_epoch = Some(epoch);
        }
    }

    fn worker_thread_entry(self: Arc<Self>, worker_id: usize, local: Worker<TaskToken>) {
        if self.test_mode {
            if let Err(_panic) = panic::catch_unwind(AssertUnwindSafe(|| {
                Arc::clone(&self).worker_loop(worker_id, local);
            })) {
                self.record_worker_panic();
            }
        } else {
            self.worker_loop(worker_id, local);
        }
    }

    /// Whether `next_task` could find something, for the worker that polls right now.
    fn has_runnable(&self, worker_id: usize) -> bool {
        !self.pinned_queues[worker_id].is_empty()
            || !self.yielded[worker_id].tasks.is_empty()
            || !self.injector.is_empty()
            || self.remote_queues.iter().any(|queue| !queue.is_empty())
            || self.stealers.iter().any(|stealer| !stealer.is_empty())
    }

    fn next_task(&self, worker_id: usize, local: &Worker<TaskToken>) -> Option<TaskToken> {
        if let Some(task_id) = self.pop_pinned_task(worker_id) {
            return Some(task_id);
        }
        self.drain_remote_queue(worker_id, local);

        let yielded = &self.yielded[worker_id];
        let turns = yielded.turns.load(Ordering::Relaxed).wrapping_add(1);
        yielded.turns.store(turns, Ordering::Relaxed);
        if turns % YIELD_FAIRNESS_INTERVAL == 0 {
            if let Some(task_id) = yielded.pop() {
                return Some(task_id);
            }
        }

        if let Some(task_id) = local.pop() {
            return Some(task_id);
        }
        if let Some(task_id) = self.steal_batch_and_pop(&self.injector, local) {
            return Some(task_id);
        }
        if let Some(task_id) = yielded.pop() {
            return Some(task_id);
        }

        for offset in 1..self.worker_count {
            let victim = (worker_id + offset) % self.worker_count;
            // Remote queues contain movable tasks only. The preferred worker
            // may begin a long poll after enqueue selected it; peers must still
            // be able to make progress. Pinned queues remain private.
            if let Some(task_id) = self.remote_queues[victim].pop_front() {
                self.stats.add(&self.stats.steals, 1);
                return Some(task_id);
            }
            if let Some(task_id) = self.steal_batch_and_pop(&self.stealers[victim], local) {
                self.stats.add(&self.stats.steals, 1);
                self.record_trace("task_steal", || {
                    format!("worker={worker_id} victim={victim} task={task_id}")
                });
                return Some(task_id);
            }
        }

        None
    }

    fn pop_pinned_task(&self, worker_id: usize) -> Option<TaskToken> {
        self.pinned_queues[worker_id].pop_front()
    }

    fn drain_remote_queue(&self, worker_id: usize, local: &Worker<TaskToken>) {
        let drained = self.remote_queues[worker_id].drain();
        if drained.is_empty() {
            return;
        }

        for task_id in drained.into_iter().rev() {
            local.push(task_id);
        }

        // Remote work only becomes stealable here. Peers may have parked
        // before it was published, even when its owner received an enqueue
        // wake. Leave one task for this worker and wake at most one peer per
        // remaining task. Unpark tokens also cover peers about to park.
        let peer_count = local.len().saturating_sub(1).min(self.worker_count - 1);
        for offset in 1..=peer_count {
            self.unpark_worker((worker_id + offset) % self.worker_count);
        }
        self.stats
            .add(&self.stats.worker_unparks, peer_count as u64);
    }

    fn steal_batch_and_pop<S>(&self, stealer: &S, local: &Worker<TaskToken>) -> Option<TaskToken>
    where
        S: StealSource,
    {
        loop {
            match stealer.steal_batch_and_pop(local) {
                Steal::Success(task_id) => return Some(task_id),
                Steal::Empty => return None,
                Steal::Retry => std::hint::spin_loop(),
            }
        }
    }

    fn take_worker_parker(&self, worker_id: usize) -> Parker {
        self.worker_parkers.lock().unwrap()[worker_id]
            .take()
            .expect("ICE: worker parker already taken")
    }

    fn register_worker_thread(&self, worker_id: usize) {
        self.worker_registered[worker_id].store(true, Ordering::Release);
    }

    // `trace` is storage to reuse. Finding the parent's frames can wait on its
    // slot, so this runs with no other slot locked.
    fn trace_for_spawn(&self, metadata: SpawnMetadata, mut trace: SpawnTrace) -> SpawnTrace {
        trace.clear();
        if let Some(parent_token) = current_task_token() {
            let (parent_index, parent_generation) = unpack_task_token(parent_token);
            if let Some(inner) = self
                .lookup_task_slot(parent_index)
                .and_then(|slot| slot.inner.lock().ok())
                .filter(|inner| inner.occupied && inner.generation == parent_generation)
            {
                let start = inner
                    .spawn_trace
                    .len()
                    .saturating_sub(MAX_TASK_TRACE_FRAMES - 1);
                trace.extend_from_slice(&inner.spawn_trace[start..]);
            }
        }
        trace.push(metadata.frame);
        trace
    }

    #[cfg(test)]
    fn add_task(
        &self,
        handle: *mut u8,
        out_ptr: *mut u8,
        out_buf: Option<TaskOutput>,
        owner_worker: usize,
        preferred_worker: Option<usize>,
        is_spawned: bool,
    ) -> TaskToken {
        self.add_task_with_metadata(
            handle,
            out_ptr,
            out_buf,
            owner_worker,
            preferred_worker,
            is_spawned,
            SpawnMetadata::anonymous(),
        )
    }

    fn add_task_with_metadata(
        &self,
        handle: *mut u8,
        out_ptr: *mut u8,
        out_buf: Option<TaskOutput>,
        owner_worker: usize,
        preferred_worker: Option<usize>,
        is_spawned: bool,
        metadata: SpawnMetadata,
    ) -> TaskToken {
        let task_token = self.prepare_task_with_metadata(
            handle,
            out_ptr,
            out_buf,
            owner_worker,
            is_spawned,
            metadata,
        );
        self.schedule_task(task_token, preferred_worker);
        task_token
    }

    /// Install ownership, accounting and slot state without publishing runnable
    /// work. Group registration must finish before any worker can poll a task.
    fn prepare_task_with_metadata(
        &self,
        handle: *mut u8,
        out_ptr: *mut u8,
        out_buf: Option<TaskOutput>,
        owner_worker: usize,
        is_spawned: bool,
        metadata: SpawnMetadata,
    ) -> TaskToken {
        debug_assert!(owner_worker < self.worker_count);

        let mobility = async_handle_mobility(handle);

        // Release the global free-list mutex before waiting on one slot or
        // preparing its state. Reclamation takes its slot before the free list.
        let recycled_slot = self.free_slots.lock().unwrap().pop();
        let (task_index, task_generation) = if let Some(task_index) = recycled_slot {
            let slot = self
                .lookup_task_slot(task_index)
                .unwrap_or_else(|| panic!("ICE: recycled task slot {task_index} missing"));
            let reused = std::mem::take(&mut slot.inner.lock().unwrap().spawn_trace);
            let spawn_trace = self.trace_for_spawn(metadata, reused);
            let mut inner = slot.inner.lock().unwrap();
            assert!(
                !inner.occupied,
                "ICE: recycled task slot {task_index} is still occupied"
            );
            let generation = next_task_generation(inner.generation);
            inner.generation = generation;
            inner.occupied = true;
            inner.handle = handle;

            inner.out_ptr = out_ptr;
            inner.out_buf = out_buf;
            inner.completed = false;
            inner
                .cancelled
                .store(self.draining.load(Ordering::Acquire), Ordering::Release);
            inner.detached = false;
            inner.polled = false;
            inner.queued = false;
            inner.running = false;
            inner.wake_requested = false;
            inner.published = false;
            inner.shared = None;
            inner.owner_worker = owner_worker;
            inner.last_worker = owner_worker;
            inner.mobility = mobility;
            inner.group_id = None;
            inner.is_spawned = is_spawned;
            inner.panic_info = None;
            inner.spawn_trace = spawn_trace;
            inner.wait_reason = None;
            inner.waited_on_io = false;
            inner.registered_sleep = false;
            (task_index, generation)
        } else {
            let spawn_trace = self.trace_for_spawn(metadata, Vec::new());
            let task_generation = TASK_INITIAL_GENERATION;
            let slot = Arc::new(TaskSlot::new(
                task_generation,
                handle,
                out_ptr,
                out_buf,
                owner_worker,
                mobility,
            ));
            {
                let mut inner = slot.inner.lock().unwrap();
                inner.is_spawned = is_spawned;
                inner
                    .cancelled
                    .store(self.draining.load(Ordering::Acquire), Ordering::Release);
                inner.spawn_trace = spawn_trace;
            }
            let task_index = self.push_task_slot(slot);
            {
                let mut timers = self.timers.lock().unwrap();
                timers.latest.push(None);
            }
            (task_index, task_generation)
        };

        let task_token = pack_task_token(task_index, task_generation);
        self.stats.add(&self.stats.tasks_created, 1);
        let live_tasks = self.incomplete_tasks.fetch_add(1, Ordering::AcqRel) + 1;
        if self.stats.enabled {
            self.stats
                .peak_live_tasks
                .fetch_max(live_tasks as u64, Ordering::Relaxed);
        }
        self.record_trace("task_spawn", || {
            let Some(slot) = self.lookup_task_slot(task_index) else {
                return format!("task={task_token}");
            };
            let inner = slot
                .inner
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let Some(site) = inner.spawn_trace.last() else {
                return format!("task={task_token}");
            };
            format!(
                "task={} name={} file={} line={} column={}",
                task_token,
                quote_field(&site.name),
                quote_field(&site.file),
                site.line,
                site.column
            )
        });
        task_token
    }

    fn run_task(&self, worker_id: usize, task_token: TaskToken) {
        debug_assert!(worker_id < self.worker_count);
        struct PollingGuard<'a>(&'a AtomicBool);
        impl Drop for PollingGuard<'_> {
            fn drop(&mut self) {
                self.0.store(false, Ordering::Release);
            }
        }
        self.worker_polling[worker_id].store(true, Ordering::Release);
        let _polling = PollingGuard(&self.worker_polling[worker_id]);
        // Only a queued turn services this worker's waiting queue. Counting
        // inline children would inflate service rate and hide queueing delay
        // from the load review, especially for short withTimeout operations.
        if !crate::task::in_inline_poll() {
            let polls = &self.yielded[worker_id].polls;
            polls.store(
                polls.load(Ordering::Relaxed).wrapping_add(1),
                Ordering::Relaxed,
            );
        }

        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        let (handle, out_ptr, cancelled_before_first_poll, output_owner, cancellation) = {
            let mut inner = slot
                .inner
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if !inner.occupied
                || inner.generation != task_generation
                || inner.completed
                || inner.running
                || !inner.queued
            {
                return;
            }
            inner.queued = false;
            inner.running = true;
            inner.wait_reason = None;
            let cancelled_before_first_poll =
                inner.cancelled.load(Ordering::Acquire) && !inner.polled;
            inner.polled = true;
            inner.last_worker = worker_id;
            debug_assert!(
                matches!(inner.mobility, TaskMobility::Movable) || inner.owner_worker == worker_id,
                "pinned task scheduled on non-owner worker"
            );
            (
                inner.handle,
                inner.out_ptr,
                cancelled_before_first_poll,
                inner.out_buf.take(),
                inner.cancelled.clone(),
            )
        };
        if cancelled_before_first_poll {
            self.complete_task_cancelled(task_token);
            return;
        }

        let cancellation_flag = Arc::as_ptr(&cancellation);
        WORKER_CONTEXT.with(|cell| {
            let mut borrow = cell.borrow_mut();
            let context = borrow.as_mut().expect("ICE: worker context missing");
            context.current_task = Some(task_token);
            context.current_cancellation = Some(cancellation);
            context.current_wait_reason = None;
        });
        crate::task::set_polled_cancellation(cancellation_flag);
        // Only the opt-in watchdog reads this, and it costs an atomic on every poll.
        if self.deadlock_timeout.is_some() {
            self.progress_epoch.fetch_add(1, Ordering::AcqRel);
        }
        self.stats.add(&self.stats.task_polls, 1);
        self.record_trace("task_poll_start", || {
            format!("worker={worker_id} task={task_token}")
        });

        let poll_started = self.blocking_warn_threshold.map(|_| Instant::now());
        let poll = || {
            let output = output_owner;
            let owner = unsafe { crate::task::OwnedAsyncHandle::from_raw(handle) };
            let mut unwind = TaskPollUnwind {
                slot: &slot,
                owner: Some(owner),
            };
            let tag = crate::task::poll_with_output_publication(
                unwind.owner.as_ref().unwrap().as_ptr(),
                out_ptr,
                output.as_ref().map(TaskOutput::publication),
            );
            let _ = unwind.owner.take().unwrap().into_raw();
            (tag, output)
        };
        // Preserve a root panic until its children have cancelled and drained.
        // Catching only spawned tasks would unwind out of the worker loop and
        // stop workers before the remaining native requests acknowledge stop.
        let poll_result = crate::panic_unwind::catch_executor_panic(poll);
        if let Some(held) = crate::task::end_poll_holds() {
            self.release_held_spawn(held);
        }
        for held in crate::task::take_extra_held_spawns() {
            self.release_held_spawn(held);
        }
        if let (Some(threshold), Some(started)) = (self.blocking_warn_threshold, poll_started) {
            let elapsed = started.elapsed();
            if elapsed >= threshold {
                self.write_slow_poll_warning(task_token, elapsed);
            }
        }

        let wait_reason = WORKER_CONTEXT.with(|cell| {
            let mut borrow = cell.borrow_mut();
            let context = borrow.as_mut().expect("ICE: worker context missing");
            context.current_task = None;
            context.current_cancellation = None;
            context.current_wait_reason.take()
        });
        crate::task::set_polled_cancellation(std::ptr::null());

        let poll_status = match &poll_result {
            Err(_) => "panicked",
            Ok((0, _)) => "pending",
            Ok((2, _)) => "cancelled",
            Ok(_) => "ready",
        };
        self.record_trace("task_poll_end", || {
            format!("worker={worker_id} task={task_token} status={poll_status}")
        });

        let (tag, pending) = match poll_result {
            Ok((tag, output)) => {
                let mut inner = slot.inner.lock().unwrap();
                debug_assert!(inner.out_buf.is_none());
                inner.out_buf = output;
                // Pending cancellation is a live task, not completion. Its backend
                // may still hold borrowed addresses; only a terminal poll may release
                // the handle or publish cancellation to observers.
                let pending = (tag == 0).then(|| {
                    inner.running = false;
                    // A finished poll can satisfy an expired timeout's grace turn,
                    // which only the first one has to do.
                    let timeout_waiter = inner
                        .shared
                        .as_ref()
                        .filter(|shared| !shared.has_finished_a_poll())
                        .cloned();
                    // Pending polls must either have registered a runtime wait
                    // (`blocked`) or be cooperatively requeued here.
                    let requeue_target = if !inner.occupied
                        || inner.generation != task_generation
                        || inner.completed
                    {
                        None
                    } else if inner.wake_requested {
                        inner.wake_requested = false;
                        inner.wait_reason = None;
                        Some(match inner.mobility {
                            TaskMobility::Pinned => Some(inner.owner_worker),
                            TaskMobility::Movable => Some(inner.last_worker),
                        })
                    } else if let Some(wait_reason) = wait_reason {
                        inner.wait_reason = Some(wait_reason);
                        None
                    } else {
                        inner.wait_reason = None;
                        Some(match inner.mobility {
                            TaskMobility::Pinned => Some(inner.owner_worker),
                            // Behind this worker's other work. Its peers aren't needed
                            // just because this task wants another turn.
                            TaskMobility::Movable => None,
                        })
                    };
                    (requeue_target, timeout_waiter)
                });
                (tag, pending)
            }
            Err(report) => {
                // TaskPollUnwind retired the handle before its original unwind
                // cleanup before finalizing the slot.
                self.complete_task_panicked(task_token, report);
                return;
            }
        };

        if let Some((requeue_target, timeout_waiter)) = pending {
            match requeue_target {
                Some(Some(preferred_worker)) => {
                    self.schedule_task(task_token, Some(preferred_worker));
                }
                Some(None) => self.schedule_tasks([WakeRequest {
                    task_token,
                    placement: Placement::Yielded(worker_id),
                }]),
                None => {}
            }
            if let Some(shared) = timeout_waiter {
                shared.finished_poll();
            }
        } else if tag == 2 {
            self.complete_task_cancelled(task_token);
        } else {
            self.complete_task(task_token);
        }
    }

    /// Give a task the current poll just spawned its first poll on this stack, as
    /// itself: its own identity, cancellation flag and panic boundary, restored
    /// afterwards. For a poll about to wait on that task and nothing else, so only
    /// the order relative to other queued tasks changes. Its queue entry stays
    /// behind and is ignored when popped; a peer that took it first just wins.
    ///
    /// False when it can't happen here: the current task is being cancelled, as
    /// its cleanup must not start new work, or this is already such a poll, which
    /// keeps the stack bounded.
    pub(super) fn poll_spawned_inline(&self, task: TaskToken) -> bool {
        struct Restore<'a> {
            scheduler: &'a Scheduler,
            worker_id: usize,
            task: Option<TaskToken>,
            cancellation: Option<Arc<AtomicBool>>,
            wait_reason: Option<WaitReason>,
        }
        impl Drop for Restore<'_> {
            fn drop(&mut self) {
                let cancellation = self.cancellation.take();
                crate::task::set_polled_cancellation(
                    cancellation.as_ref().map_or(std::ptr::null(), Arc::as_ptr),
                );
                WORKER_CONTEXT.with(|cell| {
                    let mut context = cell.borrow_mut();
                    let context = context
                        .as_mut()
                        .expect("inline poll lost its worker context");
                    context.current_task = self.task;
                    context.current_cancellation = cancellation;
                    context.current_wait_reason = self.wait_reason.take();
                });
                self.scheduler.worker_polling[self.worker_id].store(true, Ordering::Release);
                crate::task::set_inline_poll(false);
            }
        }
        if crate::task::polled_task_cancelled() != Some(false) || crate::task::in_inline_poll() {
            return false;
        }
        let saved = WORKER_CONTEXT.with(|cell| {
            let mut context = cell.borrow_mut();
            let context = context.as_mut()?;
            Some((
                context.worker_id,
                context.current_task.take(),
                context.current_cancellation.take(),
                context.current_wait_reason.take(),
            ))
        });
        let Some((worker_id, parent, cancellation, wait_reason)) = saved else {
            return false;
        };
        crate::task::set_inline_poll(true);
        let _restore = Restore {
            scheduler: self,
            worker_id,
            task: parent,
            cancellation,
            wait_reason,
        };
        self.run_task(worker_id, task);
        true
    }

    /// Queue a task spawned with `__rt__task_hold_next_spawn`, as spawn would have.
    pub(super) fn release_held_spawn(&self, task_token: TaskToken) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        {
            let mut inner = slot.inner.lock().unwrap();
            if !inner.occupied || inner.generation != task_generation || !inner.queued {
                return;
            }
            inner.queued = false;
        }
        self.schedule_task(task_token, current_worker_id());
    }

    fn complete_task(&self, task_token: TaskToken) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        let waited_on_io;
        let registered_sleep;
        let (handle, shared, group_id, group_output, detached) = {
            let mut inner = slot.inner.lock().unwrap();
            if !inner.occupied || inner.generation != task_generation {
                return;
            }
            if inner.completed {
                inner.running = false;
                return;
            }
            inner.completed = true;
            inner.cancelled.store(false, Ordering::Release);
            inner.running = false;
            inner.queued = false;
            inner.wait_reason = None;

            let handle = inner.handle;
            waited_on_io = inner.waited_on_io;
            registered_sleep = inner.registered_sleep;

            inner.handle = std::ptr::null_mut();
            // Completion transfers the one output allocation into the group.
            // A byte clone would duplicate owned payloads without Copy/retain
            // witnesses and leave a second apparent result in the task slot.
            let group_output = if inner.group_id.is_some() {
                inner.out_ptr = std::ptr::null_mut();
                inner.out_buf.take()
            } else {
                None
            };
            (
                handle,
                inner.shared.take(),
                inner.group_id,
                group_output,
                inner.detached,
            )
        };

        if waited_on_io {
            io_poller::cancel_task(self.task_identity(task_token));
        }
        crate::sync::task_finalized(self.task_identity(task_token));
        if registered_sleep {
            self.clear_task_timer(task_token);
        }
        if !handle.is_null() {
            __rt__async_destroy(handle);
        }

        self.finish_terminal(
            task_token,
            PendingTerminal {
                terminal: Terminal::Completed(group_output),
                shared,
                group_id,
                detached,
            },
        );
    }

    fn cancel_task(&self, task_token: TaskToken) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        let should_wake = {
            let mut inner = slot.inner.lock().unwrap();
            if !inner.occupied || inner.generation != task_generation {
                return;
            }
            if inner.completed || inner.cancelled.load(Ordering::Acquire) {
                return;
            }
            inner.cancelled.store(true, Ordering::Release);
            // A blocked task has no queue owner; wake it so `run_task` can take
            // the cancellation path and perform normal finalization cleanup.
            if inner.running {
                inner.wake_requested = true;
                false
            } else if !inner.queued {
                true
            } else {
                false
            }
        };
        if should_wake {
            self.wake_tasks(&[task_token], false);
        }
    }

    fn complete_task_cancelled(&self, task_token: TaskToken) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        // Cleanup is part of completion, not work performed after publication.
        // Keep the slot running/incomplete while destroying the captured frame:
        // an observer must not retrieve cancellation before cleanup can panic.
        // Steal the handle first so panic finalization cannot destroy it twice.
        let (cleanup_handle, isolate) = {
            let mut inner = slot.inner.lock().unwrap();
            if !inner.occupied || inner.generation != task_generation || inner.completed {
                return;
            }
            inner.running = true;
            inner.queued = false;
            (
                std::mem::replace(&mut inner.handle, std::ptr::null_mut()),
                inner.is_spawned || inner.group_id.is_some(),
            )
        };
        let cleanup = || {
            let _context = TaskCleanupContextGuard::new(self, task_token);
            if !cleanup_handle.is_null() {
                __rt__async_destroy(cleanup_handle);
            }
        };
        if (isolate || self.rooted) && !crate::panic_unwind::is_unwinding() {
            if let Err(report) = crate::panic_unwind::catch_executor_panic(cleanup) {
                self.complete_task_panicked(task_token, report);
                return;
            }
        } else {
            cleanup();
        }
        let waited_on_io;
        let (handle, shared, group_id, detached) = {
            let mut inner = slot.inner.lock().unwrap();
            if !inner.occupied || inner.generation != task_generation {
                return;
            }
            if inner.completed {
                inner.running = false;
                return;
            }
            debug_assert!(inner.cancelled.load(Ordering::Acquire) || !inner.queued);
            inner.completed = true;
            inner.cancelled.store(true, Ordering::Release);
            inner.running = false;
            inner.queued = false;
            inner.wait_reason = None;

            let handle = inner.handle;
            waited_on_io = inner.waited_on_io;

            inner.handle = std::ptr::null_mut();
            (handle, inner.shared.take(), inner.group_id, inner.detached)
        };

        if waited_on_io {
            io_poller::cancel_task(self.task_identity(task_token));
        }
        crate::sync::task_finalized(self.task_identity(task_token));
        self.clear_task_timer(task_token);
        if !handle.is_null() {
            __rt__async_destroy(handle);
        }

        self.finish_terminal(
            task_token,
            PendingTerminal {
                terminal: Terminal::Cancelled,
                shared,
                group_id,
                detached,
            },
        );
    }

    fn complete_task_panicked(
        &self,
        task_token: TaskToken,
        mut report: crate::panic_unwind::PanicReport,
    ) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        let waited_on_io;
        let (handle, shared, group_id, detached, root) = {
            let mut inner = slot.inner.lock().unwrap();
            if !inner.occupied || inner.generation != task_generation {
                return;
            }
            if inner.completed {
                inner.running = false;
                return;
            }
            let root = self.rooted && inner.group_id.is_none() && !inner.is_spawned;
            inner.completed = true;
            inner.running = false;
            inner.queued = false;
            inner.wait_reason = None;

            let handle = inner.handle;
            waited_on_io = inner.waited_on_io;

            inner.handle = std::ptr::null_mut();
            report.task_trace = inner
                .spawn_trace
                .iter()
                .map(|site| (**site).clone())
                .collect();
            if !root && inner.group_id.is_none() && !inner.detached {
                // Store the report so the awaiter can retrieve it.
                inner.panic_info = Some(report.clone());
            }
            (
                handle,
                inner.shared.take(),
                inner.group_id,
                inner.detached,
                root,
            )
        };

        if root {
            *self.root_panic.lock().unwrap() = Some(report.clone());
        }

        if waited_on_io {
            io_poller::cancel_task(self.task_identity(task_token));
        }
        crate::sync::task_finalized(self.task_identity(task_token));
        self.clear_task_timer(task_token);
        if !handle.is_null() {
            __rt__async_destroy(handle);
        }

        self.finish_terminal(
            task_token,
            PendingTerminal {
                terminal: Terminal::Panicked(report),
                shared,
                group_id,
                detached,
            },
        );
    }

    /// Scope `child` to `parent`: the parent's terminal outcome waits until
    /// the child has published its own. Finished children are ignored.
    fn adopt_scoped_child(&self, parent: TaskToken, child: TaskToken) {
        if parent == child {
            return;
        }
        let (child_index, child_generation) = unpack_task_token(child);
        let mut links = self.scope_links.lock().unwrap();
        let Some(slot) = self.lookup_task_slot(child_index) else {
            return;
        };
        // Counted before reading `published`, which `publish_terminal` sets before
        // reading the count: either this sees it published, or it sees this link
        // and comes through the lock to remove it.
        self.scope_link_count.fetch_add(1, Ordering::SeqCst);
        let live = {
            let inner = slot.inner.lock().unwrap();
            inner.occupied && inner.generation == child_generation && !inner.published
        };
        if !live || links.parent.contains_key(&child) {
            self.scope_link_count.fetch_sub(1, Ordering::SeqCst);
            return;
        }
        links.parent.insert(child, parent);
        links.children.entry(parent).or_default().push(child);
    }

    /// Publish a task's terminal outcome after its cleanup, or defer it until
    /// its scoped children have finished. Deferring cancels those children.
    fn finish_terminal(&self, task_token: TaskToken, pending: PendingTerminal) {
        // A task's children were adopted in its own polls, all ordered before this,
        // and stay counted until they publish.
        if self.scope_link_count.load(Ordering::SeqCst) == 0 {
            self.publish_terminal(task_token, pending);
            return;
        }
        let waiting_on = {
            let mut links = self.scope_links.lock().unwrap();
            match links.children.get(&task_token) {
                Some(children) if !children.is_empty() => {
                    let children = children.clone();
                    links.pending.insert(task_token, pending);
                    children
                }
                _ => {
                    links.children.remove(&task_token);
                    drop(links);
                    self.publish_terminal(task_token, pending);
                    return;
                }
            }
        };
        self.record_trace("task_drain_children", || {
            format!("task={task_token} children={}", waiting_on.len())
        });
        for child in waiting_on.iter() {
            self.cancel_task(child);
        }
    }

    fn publish_terminal(&self, task_token: TaskToken, pending: PendingTerminal) {
        let PendingTerminal {
            terminal,
            shared,
            group_id,
            detached,
        } = pending;
        // Unlink from a scoping parent; the last child releases its parent.
        let (task_index, task_generation) = unpack_task_token(task_token);
        if let Some(slot) = self.lookup_task_slot(task_index) {
            let mut inner = slot.inner.lock().unwrap();
            if inner.occupied && inner.generation == task_generation {
                inner.published = true;
            }
        }
        let ready_parent = if self.scope_link_count.load(Ordering::SeqCst) == 0 {
            None
        } else {
            let mut links = self.scope_links.lock().unwrap();
            let parent = links.parent.remove(&task_token);
            if parent.is_some() {
                self.scope_link_count.fetch_sub(1, Ordering::SeqCst);
            }
            parent.and_then(|parent| {
                let siblings = links.children.get_mut(&parent)?;
                siblings.remove(task_token);
                if !siblings.is_empty() {
                    return None;
                }
                links.children.remove(&parent);
                links
                    .pending
                    .remove(&parent)
                    .map(|pending| (parent, pending))
            })
        };

        match terminal {
            Terminal::Completed(group_output) => {
                if let Some(group_id) = group_id {
                    self.notify_group_task_completed(group_id, task_token, group_output);
                }
                if let Some(shared) = shared {
                    shared.publish_completed();
                }
                self.stats.add(&self.stats.task_completions, 1);
                self.record_trace("task_complete", || format!("task={task_token}"));
            }
            Terminal::Cancelled => {
                if let Some(group_id) = group_id {
                    self.notify_group_task_cancelled(group_id, task_token);
                }
                if let Some(shared) = shared {
                    shared.publish_cancelled();
                }
                self.stats.add(&self.stats.task_cancellations, 1);
                self.record_trace("task_cancel", || format!("task={task_token}"));
            }
            Terminal::Panicked(report) => {
                if let Some(group_id) = group_id {
                    self.notify_group_task_panicked(group_id, task_token, report.clone());
                }
                // A spawned task reports its panic once, when it escapes the
                // task body, independently of whether any handle observes it.
                if let Some(shared) = shared {
                    crate::panic_unwind::write_task_panic(&report);
                    shared.publish_panicked(report);
                } else if detached {
                    crate::panic_unwind::write_unobserved_task_panic(&report);
                }
                self.stats.add(&self.stats.task_panics, 1);
                self.record_trace("task_panic", || format!("task={task_token}"));
            }
        }
        if detached || group_id.is_some() {
            self.reclaim_unobserved_task_slot(task_token);
        }

        self.finish_root_if_needed(task_token);
        self.task_finished();

        if let Some((parent, pending)) = ready_parent {
            self.publish_terminal(parent, pending);
        }
    }

    fn reclaim_task_slot(
        &self,
        task_token: TaskToken,
        inner: &mut TaskSlotInner,
    ) -> Option<TaskOutput> {
        let (task_index, task_generation) = unpack_task_token(task_token);
        assert!(
            inner.occupied && inner.generation == task_generation,
            "ICE: attempted to reclaim stale task token {task_token}"
        );
        assert!(
            inner.completed,
            "ICE: attempted to reclaim task token {task_token} before completion"
        );
        inner.occupied = false;
        inner.cancelled.store(false, Ordering::Release);
        inner.detached = false;
        inner.polled = false;
        inner.shared = None;
        inner.queued = false;
        inner.running = false;
        inner.wake_requested = false;
        inner.published = false;
        inner.wait_reason = None;
        inner.handle = std::ptr::null_mut();

        inner.out_ptr = std::ptr::null_mut();
        let output = inner.out_buf.take();
        inner.group_id = None;
        inner.panic_info = None;
        self.free_slots.lock().unwrap().push(task_index);
        output
    }

    fn reclaim_unobserved_task_slot(&self, task_token: TaskToken) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        let output = {
            let mut inner = slot.inner.lock().unwrap();
            if inner.occupied
                && inner.generation == task_generation
                && inner.completed
                && (inner.detached || inner.group_id.is_some())
            {
                self.reclaim_task_slot(task_token, &mut inner)
            } else {
                None
            }
        };
        drop(output);
    }

    #[cfg(test)]
    fn add_group_task_with_metadata(
        &self,
        group_id: u64,
        handle: *mut u8,
        output_desc: &GcDesc,
        owner_worker: usize,
        metadata: SpawnMetadata,
    ) -> TaskToken {
        let token = self.prepare_group_task_with_metadata(
            group_id,
            handle,
            unsafe { TaskOutput::new(output_desc) },
            output_desc,
            owner_worker,
            metadata,
        );
        self.schedule_task(token, Some(owner_worker));
        token
    }

    fn prepare_group_task_with_metadata(
        &self,
        group_id: u64,
        handle: *mut u8,
        mut out_buf: TaskOutput,
        output_desc: &GcDesc,
        owner_worker: usize,
        metadata: SpawnMetadata,
    ) -> TaskToken {
        let out_ptr = out_buf.as_mut_ptr();
        // Closing/cancelling the group cannot interleave with registration.
        // Preparation invokes no user callbacks and publishes no runnable work.
        // The only nested scheduler lock order here is group -> task slot;
        // completion releases its slot lock before notifying the group.
        let mut groups = self.task_groups.lock().unwrap();
        let failure = match live_group_mut(&mut groups, group_id) {
            None => Some("task group used after its scope ended"),
            Some(group) if group.spawning_closed => {
                Some("task_group_spawn called after group was closed")
            }
            Some(group) if group.cancelled => {
                Some("task_group_spawn called after group was cancelled")
            }
            Some(group) if group.result_size != output_desc.size => {
                Some("task_group_spawn result size mismatch")
            }
            Some(_) => None,
        };
        if let Some(message) = failure {
            drop(groups);
            crate::panic_unwind::rethrow_panic_message(message.to_string());
        }
        let group = live_group_mut(&mut groups, group_id).unwrap();

        let task_token = self.prepare_task_with_metadata(
            handle,
            out_ptr,
            Some(out_buf),
            owner_worker,
            false,
            metadata,
        );
        let (task_index, task_generation) = unpack_task_token(task_token);
        let slot = self
            .lookup_task_slot(task_index)
            .expect("prepared task slot");
        {
            let mut inner = slot.inner.lock().unwrap();
            debug_assert!(inner.occupied && inner.generation == task_generation);
            debug_assert!(!inner.queued && !inner.running && !inner.completed);
            inner.group_id = Some(group_id);
        }
        group.tasks.insert(task_token);
        drop(groups);
        // The caller transfers its input-handle obligation before publishing
        // runnable work. Membership is already complete when a worker starts.
        task_token
    }

    fn notify_group_task_completed(
        &self,
        group_id: u64,
        task_token: TaskToken,
        out_buf: Option<TaskOutput>,
    ) {
        self.finish_group_task(group_id, task_token, out_buf, None);
    }

    fn notify_group_task_cancelled(&self, group_id: u64, task_token: TaskToken) {
        self.finish_group_task(group_id, task_token, None, None);
    }

    fn notify_group_task_panicked(
        &self,
        group_id: u64,
        task_token: TaskToken,
        report: crate::panic_unwind::PanicReport,
    ) {
        self.finish_group_task(group_id, task_token, None, Some(report));
    }

    /// Retire one child's group membership before running any cleanup callback.
    /// Unknown/duplicate notifications cannot publish into a reused group slot.
    fn finish_group_task(
        &self,
        group_id: u64,
        task_token: TaskToken,
        mut output: Option<TaskOutput>,
        mut report: Option<crate::panic_unwind::PanicReport>,
    ) {
        let actions = {
            let mut groups = self.task_groups.lock().unwrap();
            (|| {
                let slot = live_group_slot(&mut groups, group_id)?;
                let group = slot.as_mut()?;
                if !group.tasks.remove(&task_token) {
                    return None;
                }
                let mut cancel = Vec::new();
                if !group.destroy_pending {
                    if !group.discard_results
                        && let Some(buf) = output.take()
                    {
                        group.completed.push_back(CompletedGroupTask { buf });
                    }
                    if let Some(report) = report.take() {
                        if group.panic_report.is_none() {
                            group.panic_report = Some(report);
                        }
                        if group.cancel_on_panic {
                            group.cancelled = true;
                            group.spawning_closed = true;
                            cancel = group.tasks.iter().copied().collect();
                        }
                    }
                }
                // A discarding group's waiter only wants to hear of the last one.
                let waiter = if group.discard_results && !group.tasks.is_empty() {
                    None
                } else {
                    group.waiter.take()
                };
                let retired = if group.destroy_pending && group.tasks.is_empty() {
                    slot.take()
                } else {
                    None
                };
                Some((waiter, cancel, retired))
            })()
        };
        if let Some((waiter, cancel, retired)) = actions {
            if retired.is_some() {
                self.free_group_slots
                    .lock()
                    .unwrap()
                    .push(group_index(group_id));
            }
            // Retired groups contain no queued output; all lifecycle callbacks
            // nevertheless stay outside the group/free-list locks.
            drop(retired);
            for token in cancel {
                self.cancel_task(token);
            }
            if let Some(waiter) = waiter {
                self.wake_tasks(&[waiter], false);
            }
            if let Some(report) = report {
                crate::panic_unwind::write_unobserved_task_panic(&report);
            }
        }
        drop(output);
    }

    fn destroy_task_group(&self, group_id: u64) -> Option<crate::panic_unwind::PanicReport> {
        let (completed, report, remaining, waiter, retired) = {
            let mut groups = self.task_groups.lock().unwrap();
            let slot = live_group_slot(&mut groups, group_id)?;
            let group = slot.as_mut()?;
            if group.destroy_pending {
                return None;
            }
            group.destroy_pending = true;
            group.spawning_closed = true;
            group.cancelled = true;
            let completed = std::mem::take(&mut group.completed);
            let report = group.panic_report.take();
            let remaining: Vec<TaskToken> = group.tasks.iter().copied().collect();
            let waiter = group.waiter.take();
            let retired = if remaining.is_empty() {
                slot.take()
            } else {
                None
            };
            (completed, report, remaining, waiter, retired)
        };
        if retired.is_some() {
            self.free_group_slots
                .lock()
                .unwrap()
                .push(group_index(group_id));
        }
        drop(retired);
        // A scope that ends early (cancellation or panic) leaves live children:
        // the scope's task does not publish its outcome until they finish.
        let parent = current_task_token();
        for token in remaining {
            if let Some(parent) = parent {
                self.adopt_scoped_child(parent, token);
            }
            self.cancel_task(token);
        }
        if let Some(waiter) = waiter {
            self.wake_tasks(&[waiter], false);
        }
        // Cleanup may reenter the executor or unwind. The group has already
        // been closed and its live children retain a tombstone until finalized.
        drop(completed);
        report
    }

    fn register_sleep(&self, task_token: TaskToken, deadline: Instant) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        if let Some(slot) = self.lookup_task_slot(task_index) {
            let mut inner = slot.inner.lock().unwrap();
            if inner.occupied && inner.generation == task_generation {
                inner.registered_sleep = true;
            }
        }
        let should_notify = {
            let mut timers = self.timers.lock().unwrap();
            if task_index >= timers.latest.len() {
                timers.latest.resize(task_index + 1, None);
            }

            // Re-registering the same deadline for the same task is a no-op.
            if timers.latest[task_index].is_some_and(|entry| entry.deadline == deadline) {
                return;
            }

            let previous = timers.heap.peek().map(|entry| entry.0.deadline);
            let sequence = self.next_timer_sequence.fetch_add(1, Ordering::Relaxed);
            timers.heap.push(Reverse(TimerEntry {
                deadline,
                sequence,
                task_token,
            }));
            // Heap entries are append-only. `latest` is the cancellation and
            // re-registration guard that makes older heap entries stale.
            timers.latest[task_index] = Some(TimerRegistration { deadline, sequence });
            previous.is_none_or(|earliest| deadline < earliest)
        };

        self.stats.add(&self.stats.timer_registrations, 1);
        self.record_trace("timer_register", || format!("task={task_token}"));

        // A thread that isn't in the reactor reads the timers before it next is.
        if should_notify
            && self.started.load(Ordering::Acquire)
            && self.reactor_poller.load(Ordering::SeqCst) != POLLER_NONE
        {
            io_poller::notify();
        }
    }

    fn next_timer_timeout(&self) -> Option<StdDuration> {
        let deadline = {
            let mut timers = self.timers.lock().unwrap();
            loop {
                let entry = timers.heap.peek().copied()?.0;
                if Self::is_live_timer_entry(&timers, entry) {
                    break entry.deadline;
                }
                let _ = timers.heap.pop();
            }
        };
        let now = Instant::now();
        Some(if deadline <= now {
            StdDuration::ZERO
        } else {
            deadline.duration_since(now)
        })
    }

    fn wake_due_timers(&self) {
        let now = Instant::now();
        let mut due = Vec::new();
        {
            let mut timers = self.timers.lock().unwrap();
            while let Some(Reverse(entry)) = timers.heap.peek().copied() {
                if !Self::is_live_timer_entry(&timers, entry) {
                    let _ = timers.heap.pop();
                    continue;
                }
                if entry.deadline > now {
                    break;
                }
                let _ = timers.heap.pop();
                let (task_index, _) = unpack_task_token(entry.task_token);
                if let Some(slot) = timers.latest.get_mut(task_index) {
                    *slot = None;
                }
                due.push(entry.task_token);
            }
        }

        if !due.is_empty() {
            self.stats.add(&self.stats.timer_wakeups, due.len() as u64);
            for task_token in &due {
                self.record_trace("timer_wake", || format!("task={task_token}"));
            }
            self.wake_tasks(&due, false);
        }
    }

    fn is_live_timer_entry(timers: &TimerState, entry: TimerEntry) -> bool {
        let (task_index, _) = unpack_task_token(entry.task_token);
        timers
            .latest
            .get(task_index)
            .and_then(|slot| *slot)
            .is_some_and(|latest| {
                latest.sequence == entry.sequence && latest.deadline == entry.deadline
            })
    }

    fn clear_task_timer(&self, task_token: TaskToken) {
        let (task_index, _) = unpack_task_token(task_token);
        let mut timers = self.timers.lock().unwrap();
        if let Some(slot) = timers.latest.get_mut(task_index) {
            *slot = None;
        }
    }

    /// Noted before the reactor can know the task, which finishing relies on: most
    /// tasks never wait on I/O, and need never touch the reactor's global lock.
    fn note_task_waited_on_io(&self, task_token: TaskToken) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        if let Some(slot) = self.lookup_task_slot(task_index) {
            let mut inner = slot.inner.lock().unwrap();
            if inner.occupied && inner.generation == task_generation {
                inner.waited_on_io = true;
            }
        }
    }

    fn lookup_task_slot(&self, task_index: TaskIndex) -> Option<&TaskSlot> {
        // A slot outlives the scheduler's use of it: see `TaskSlotIndex`.
        self.task_index
            .get(task_index)
            .map(|slot| unsafe { &*slot })
    }

    fn push_task_slot(&self, slot: Arc<TaskSlot>) -> TaskIndex {
        let mut tasks = self.tasks.write().unwrap();
        let task_index = tasks.len();
        self.task_index.publish(task_index, Arc::as_ptr(&slot));
        tasks.push(slot);
        task_index
    }

    fn write_slow_poll_warning(&self, task_token: TaskToken, elapsed: StdDuration) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        let inner = slot.inner.lock().unwrap();
        if !inner.occupied || inner.generation != task_generation {
            return;
        }
        let (name, location) = inner.spawn_trace.last().map_or_else(
            || ("<unknown>".to_string(), String::new()),
            |frame| {
                let location = if frame.file.is_empty() {
                    String::new()
                } else {
                    format!(" at {}:{}:{}", frame.file, frame.line, frame.column)
                };
                (frame.name.clone(), location)
            },
        );
        drop(inner);

        let mut stderr = std::io::stderr().lock();
        let _ = writeln!(
            stderr,
            "warning: async task `{name}` blocked an executor worker for {} ms{location}; move synchronous blocking work into std.task.blocking",
            elapsed.as_millis()
        );
        let _ = stderr.flush();
    }

    fn diagnostic_snapshots(&self) -> Vec<TaskDiagnosticSnapshot> {
        let slots: Vec<_> = self.tasks.read().unwrap().iter().cloned().collect();
        let mut snapshots = Vec::new();
        for (task_index, slot) in slots.into_iter().enumerate() {
            let inner = slot
                .inner
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if !inner.occupied {
                continue;
            }
            let state = if inner.completed {
                if inner.panic_info.is_some() {
                    "panicked"
                } else if inner.cancelled.load(Ordering::Acquire) {
                    "cancelled"
                } else {
                    "completed"
                }
            } else if inner.running {
                "running"
            } else if inner.queued {
                "runnable"
            } else if inner.wait_reason.is_some() {
                "waiting"
            } else {
                "pending"
            };
            snapshots.push(TaskDiagnosticSnapshot {
                token: pack_task_token(task_index, inner.generation),
                state,
                spawn_trace: inner.spawn_trace.clone(),
                wait_reason: inner.wait_reason.clone(),
            });
        }
        snapshots.sort_by_key(|snapshot| snapshot.token);
        snapshots
    }

    fn wait_dependencies(&self, reason: &WaitReason) -> Vec<TaskToken> {
        let mut dependencies = match reason {
            WaitReason::Task(task) => vec![*task],
            WaitReason::Tasks(tasks) => tasks.to_vec(),
            WaitReason::TaskTimeout { task, .. } => vec![*task],
            WaitReason::TaskGroup(group_id) => self
                .task_groups
                .lock()
                .unwrap()
                .get(group_index(*group_id))
                .and_then(Option::as_ref)
                .filter(|group| group.id == *group_id)
                .map(|group| group.tasks.iter().copied().collect())
                .unwrap_or_default(),
            WaitReason::Sync { sync_id, kind } => {
                crate::sync::wait_dependencies(self.identity, *sync_id, *kind)
            }
            WaitReason::Sleep(_)
            | WaitReason::Io { .. }
            | WaitReason::BlockingCapacity
            | WaitReason::BlockingWork
            | WaitReason::NativeRequest
            | WaitReason::ForeignTask => Vec::new(),
        };
        dependencies.sort_unstable();
        dependencies.dedup();
        dependencies
    }

    fn format_wait_reason(
        &self,
        reason: &WaitReason,
        dependencies: &[TaskToken],
        now: Instant,
    ) -> String {
        let dependency_list = || {
            dependencies
                .iter()
                .map(|token| format_task_token(*token))
                .collect::<Vec<_>>()
                .join(", ")
        };
        match reason {
            WaitReason::Task(task) => format!("waiting for task {}", format_task_token(*task)),
            WaitReason::Tasks(tasks) => format!(
                "waiting for first completion among tasks {} and {}",
                format_task_token(tasks[0]),
                format_task_token(tasks[1])
            ),
            WaitReason::TaskTimeout { task, deadline } => format!(
                "waiting for task {} with {} ms remaining",
                format_task_token(*task),
                deadline.saturating_duration_since(now).as_millis()
            ),
            WaitReason::TaskGroup(group_id) => {
                if dependencies.is_empty() {
                    format!("waiting for task group {group_id}")
                } else {
                    format!(
                        "waiting for task group {group_id} (live tasks: {})",
                        dependency_list()
                    )
                }
            }
            WaitReason::Sleep(deadline) => format!(
                "sleeping for another {} ms",
                deadline.saturating_duration_since(now).as_millis()
            ),
            WaitReason::Io {
                source_id,
                interest,
            } => format!(
                "waiting for {} readiness on I/O source {source_id}",
                match interest {
                    Interest::Read => "read",
                    Interest::Write => "write",
                }
            ),
            WaitReason::Sync { sync_id, kind } => {
                let resource = match kind {
                    crate::sync::WaitKind::ChannelSend => "channel send",
                    crate::sync::WaitKind::ChannelRecv => "channel receive",
                    crate::sync::WaitKind::Mutex => "mutex",
                    crate::sync::WaitKind::RwRead => "rwlock read",
                    crate::sync::WaitKind::RwWrite => "rwlock write",
                };
                if dependencies.is_empty() {
                    format!("waiting on {resource} {sync_id} (external or unmatched wait)")
                } else {
                    format!(
                        "waiting on {resource} {sync_id} (depends on tasks: {})",
                        dependency_list()
                    )
                }
            }
            WaitReason::BlockingCapacity => {
                "waiting for capacity in the bounded blocking pool".into()
            }
            WaitReason::BlockingWork => "waiting for blocking work to finish".into(),
            WaitReason::NativeRequest => "waiting for native buffer acknowledgment".into(),
            WaitReason::ForeignTask => "waiting for a task from another executor session".into(),
        }
    }

    fn build_task_dump(&self, heading: &str) -> TaskDump {
        let snapshots = self.diagnostic_snapshots();
        let active: HashSet<_> = snapshots.iter().map(|snapshot| snapshot.token).collect();
        let mut graph = HashMap::new();
        let mut dependencies_by_task = HashMap::new();
        for snapshot in &snapshots {
            let dependencies = snapshot
                .wait_reason
                .as_ref()
                .map(|reason| self.wait_dependencies(reason))
                .unwrap_or_default();
            let live_dependencies: Vec<_> = dependencies
                .into_iter()
                .filter(|dependency| active.contains(dependency))
                .collect();
            // A task timeout names a child dependency for diagnostics, but its
            // timer can still resolve the wait. Do not treat that edge as a
            // definitive internal deadlock dependency.
            if snapshot
                .wait_reason
                .as_ref()
                .is_some_and(|reason| !matches!(reason, WaitReason::TaskTimeout { .. }))
            {
                graph.insert(snapshot.token, live_dependencies.clone());
            }
            dependencies_by_task.insert(snapshot.token, live_dependencies);
        }
        let cycle = find_wait_cycle(&graph);
        let now = Instant::now();
        let mut text = String::new();
        let _ = writeln!(text, "{heading}: {} live task(s)", snapshots.len());
        for snapshot in &snapshots {
            let name = snapshot
                .spawn_trace
                .last()
                .map(|frame| frame.name.as_str())
                .unwrap_or("<unknown>");
            let _ = writeln!(
                text,
                "task {} `{name}` [{}]",
                format_task_token(snapshot.token),
                snapshot.state
            );
            if let Some(site) = snapshot.spawn_trace.last() {
                let file = if site.file.is_empty() {
                    "<unknown>"
                } else {
                    &site.file
                };
                let _ = writeln!(text, "  spawned at {file}:{}:{}", site.line, site.column);
            }
            if snapshot.spawn_trace.len() > 1 {
                let _ = writeln!(text, "  causal parents:");
                for parent in snapshot.spawn_trace[..snapshot.spawn_trace.len() - 1]
                    .iter()
                    .rev()
                {
                    let file = if parent.file.is_empty() {
                        "<unknown>"
                    } else {
                        &parent.file
                    };
                    let _ = writeln!(
                        text,
                        "    `{}` at {file}:{}:{}",
                        parent.name, parent.line, parent.column
                    );
                }
            }
            if let Some(reason) = snapshot.wait_reason.as_ref() {
                let dependencies = dependencies_by_task
                    .get(&snapshot.token)
                    .map(Vec::as_slice)
                    .unwrap_or_default();
                let _ = writeln!(
                    text,
                    "  {}",
                    self.format_wait_reason(reason, dependencies, now)
                );
            }
        }
        if let Some(cycle) = cycle.as_ref() {
            let rendered = cycle
                .iter()
                .map(|token| format_task_token(*token))
                .collect::<Vec<_>>()
                .join(" -> ");
            let _ = writeln!(text, "definitive deadlock cycle: {rendered}");
        } else {
            let _ = writeln!(
                text,
                "no definitive internal cycle; unmatched waits may depend on timers, I/O, or external producers"
            );
        }
        TaskDump { text, cycle }
    }

    fn write_task_dump(&self, heading: &str) -> Option<Vec<TaskToken>> {
        let dump = self.build_task_dump(heading);
        let mut stderr = std::io::stderr().lock();
        let _ = stderr.write_all(dump.text.as_bytes());
        let _ = stderr.flush();
        dump.cycle
    }

    #[cfg(test)]
    fn assert_spawned_token_live_or_panic(&self, task_token: TaskToken) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let slot = self
            .lookup_task_slot(task_index)
            .unwrap_or_else(|| panic!("invalid spawned task token {task_token}"));
        let inner = slot.inner.lock().unwrap();
        if !inner.occupied || inner.generation != task_generation {
            panic!("stale spawned task token {task_token}");
        }
    }

    fn enqueue_task(&self, task_token: TaskToken, placement: Placement, batch: &mut WakeBatch) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        let target = {
            let mut inner = slot.inner.lock().unwrap();
            if !inner.occupied
                || inner.generation != task_generation
                || inner.completed
                || inner.queued
            {
                return;
            }
            if inner.running {
                // The worker owns the poll right now. Record that a wake
                // happened; the worker will reschedule after the poll returns.
                inner.wake_requested = true;
                return;
            }
            inner.queued = true;
            match inner.mobility {
                TaskMobility::Pinned => QueueTarget::PinnedWorker(inner.owner_worker),
                // A worker that is mid-poll cannot drain its private queue;
                // publish to the injector so an idle peer can take the task.
                TaskMobility::Movable => match placement {
                    Placement::Continuation(worker_id) => QueueTarget::Worker(worker_id),
                    Placement::Gather => QueueTarget::Yielded(GATHERING_WORKER),
                    Placement::Yielded(worker_id) => QueueTarget::Yielded(worker_id),
                    Placement::Prefer(worker_id)
                        if !self.worker_polling[worker_id].load(Ordering::Acquire) =>
                    {
                        QueueTarget::Worker(worker_id)
                    }
                    Placement::Prefer(_) | Placement::Anywhere => QueueTarget::Global,
                },
            }
        };

        self.stats.add(&self.stats.wakeups, 1);
        self.stats.add(&self.stats.queue_enqueues, 1);
        match target {
            QueueTarget::PinnedWorker(worker_id) => {
                self.stats.add(&self.stats.pinned_enqueues, 1);
                self.record_trace("task_enqueue", || {
                    format!("task={task_token} target=pinned worker={worker_id}")
                });
                self.pinned_queues[worker_id].push_back(task_token);
                batch.note_worker(worker_id);
            }
            QueueTarget::Worker(worker_id) => {
                self.stats.add(&self.stats.worker_enqueues, 1);
                self.record_trace("task_enqueue", || {
                    format!("task={task_token} target=worker worker={worker_id}")
                });
                self.remote_queues[worker_id].push_back(task_token);
                batch.note_worker(worker_id);
            }
            QueueTarget::Yielded(worker_id) => {
                self.record_trace("task_enqueue", || {
                    format!("task={task_token} target=yielded worker={worker_id}")
                });
                self.yielded[worker_id].tasks.push(task_token);
                // A gathered task arrives from elsewhere; a yielded one is on its worker.
                if placement == Placement::Gather {
                    batch.note_worker(worker_id);
                }
            }
            QueueTarget::Global => {
                self.stats.add(&self.stats.global_injects, 1);
                self.record_trace("task_enqueue", || {
                    format!("task={task_token} target=global")
                });
                self.injector.push(task_token);
                batch.note_global();
            }
        }
    }

    fn finish_wake_batch(&self, batch: WakeBatch) {
        if !self.started.load(Ordering::Acquire) {
            return;
        }

        let current_worker = current_worker_id_for(self);
        // Pair queue publication with the worker's idle store and final queue check.
        std::sync::atomic::fence(Ordering::SeqCst);
        for worker_id in batch.touched_workers() {
            if current_worker == Some(worker_id) {
                continue;
            }
            if self.worker_idle[worker_id]
                .compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst)
                .is_ok()
            {
                self.unpark_worker(worker_id);
                self.stats.add(&self.stats.worker_unparks, 1);
            } else if !self.remote_queues[worker_id].is_empty() {
                // It's busy or on its way to its final check. A peer can get here first.
                self.unpark_next_worker_except(Some(worker_id));
                self.stats.add(&self.stats.global_unparks, 1);
            }
        }

        let global_unparks = batch.global_count.min(self.worker_count);
        for _ in 0..global_unparks {
            self.unpark_next_worker();
            self.stats.add(&self.stats.global_unparks, 1);
        }
    }

    fn schedule_tasks<I>(&self, requests: I)
    where
        I: IntoIterator<Item = WakeRequest>,
    {
        let mut batch = WakeBatch::new(self.worker_count);
        for request in requests {
            self.enqueue_task(request.task_token, request.placement, &mut batch);
        }
        self.finish_wake_batch(batch);
    }

    fn schedule_task(&self, task_token: TaskToken, preferred_worker: Option<usize>) {
        self.schedule_tasks([WakeRequest {
            task_token,
            placement: preferred_worker.into(),
        }]);
    }

    fn wake_tasks(&self, task_tokens: &[TaskToken], for_io: bool) {
        // Wakes are advisory: stale/completed/already-queued tokens are filtered
        // by `enqueue_task`, so external subsystems can race safely with task
        // completion.
        let gather = for_io && self.worker_count > 1 && self.gathering.load(Ordering::Relaxed);
        self.schedule_tasks(task_tokens.iter().copied().map(|task_token| {
            let (task_index, task_generation) = unpack_task_token(task_token);
            let placement = {
                let Some(slot) = self.lookup_task_slot(task_index) else {
                    return WakeRequest {
                        task_token,
                        placement: Placement::Anywhere,
                    };
                };
                let inner = slot.inner.lock().unwrap();
                if !inner.occupied || inner.generation != task_generation {
                    return WakeRequest {
                        task_token,
                        placement: Placement::Anywhere,
                    };
                }
                match inner.mobility {
                    TaskMobility::Pinned => Placement::Prefer(inner.owner_worker),
                    TaskMobility::Movable if gather => Placement::Gather,
                    TaskMobility::Movable => Placement::Prefer(inner.last_worker),
                }
            };
            WakeRequest {
                task_token,
                placement,
            }
        }));
    }

    fn force_shutdown(&self) {
        if self.shutdown.swap(true, Ordering::AcqRel) {
            return;
        }
        self.signal_root_exit();
        if let Some(pool) = self.blocking_pool.get() {
            pool.state.shutdown();
        }
        io_poller::notify();
        self.io_unparker.unpark();
        for worker_id in 0..self.worker_count {
            self.worker_unparkers[worker_id].unpark();
        }
    }

    fn unpark_worker(&self, worker_id: usize) {
        self.record_trace("worker_unpark", || format!("worker={worker_id}"));
        if worker_id == GATHERING_WORKER
            && self.reactor_poller.load(Ordering::SeqCst) == POLLER_WORKER
        {
            io_poller::notify();
        } else {
            self.worker_unparkers[worker_id].unpark();
        }
    }

    fn unpark_next_worker(&self) {
        self.unpark_next_worker_except(None);
    }

    fn unpark_next_worker_except(&self, excluded: Option<usize>) {
        if self.worker_count == 0 {
            return;
        }

        let current_worker = current_worker_id_for(self);
        // A lone worker in a poll checks its queues as soon as the poll returns.
        if self.worker_count == 1 && current_worker == Some(0) {
            return;
        }
        let start = self.wake_cursor.fetch_add(1, Ordering::Relaxed);
        // Pair queue publication with the worker's idle store and final queue
        // check. Either it sees this work there, or this sees it idle or searching.
        std::sync::atomic::fence(Ordering::SeqCst);
        if self.searching_workers.load(Ordering::SeqCst) != 0 {
            return;
        }
        for offset in 0..self.worker_count {
            let worker_id = (start + offset) % self.worker_count;
            if current_worker != Some(worker_id)
                && excluded != Some(worker_id)
                && self.worker_registered[worker_id].load(Ordering::Acquire)
                && self.worker_idle[worker_id]
                    .compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst)
                    .is_ok()
            {
                self.unpark_worker(worker_id);
                return;
            }
        }
    }

    fn join_background_threads(&self) {
        if let Some(join) = self.watchdog_join.lock().unwrap().take() {
            join.thread().unpark();
            let _ = join.join();
        }
        if let Some(join) = self.io_join.lock().unwrap().take() {
            let _ = join.join();
        }
        let mut joins = self.worker_joins.lock().unwrap();
        for join in joins.drain(..) {
            let _ = join.join();
        }
    }

    #[inline]
    fn record_trace(&self, event: &'static str, fields: impl FnOnce() -> String) {
        self.diagnostics.record(event, fields);
    }

    fn live_task_counts(&self) -> (usize, usize, usize, usize, usize) {
        let tasks = self.tasks.read().unwrap();
        let mut live = 0;
        let mut queued = 0;
        let mut running = 0;
        let mut waiting = 0;
        let mut completed = 0;
        for slot in tasks.iter() {
            let inner = slot
                .inner
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if !inner.occupied {
                continue;
            }
            if inner.completed {
                // The async root occupies a slot until session teardown but
                // has no user-owned result handle. Only spawned/group results
                // can represent retained application work.
                if inner.is_spawned || inner.group_id.is_some() {
                    completed += 1;
                }
                continue;
            }
            live += 1;
            if inner.running {
                running += 1;
            } else if inner.queued {
                queued += 1;
            } else if inner.wait_reason.is_some() {
                waiting += 1;
            }
        }
        (live, queued, running, waiting, completed)
    }

    fn write_diagnostics_report(&self) {
        if !self.diagnostics.is_enabled() || self.diagnostics_reported.swap(true, Ordering::AcqRel)
        {
            return;
        }

        let output = format_diagnostics_report(
            self.worker_count,
            &self.diagnostics,
            &self.stats.snapshot(),
            &stats_snapshot(),
            &self.gc_stats_baseline,
            self.live_task_counts(),
        );
        write_diagnostics_report(&output);
        diagnostics_report_pending().store(true, Ordering::Release);
    }

    fn record_worker_panic(&self) {
        let message = crate::panic_unwind::take_thread_panic_report()
            .filter(|message| !message.is_empty())
            .unwrap_or_else(|| "task panicked on a worker thread".to_string());
        let mut panic_slot = self.worker_panic.lock().unwrap();
        if panic_slot.is_none() {
            *panic_slot = Some(message);
        }
        drop(panic_slot);
        self.force_shutdown();
    }

    fn take_worker_panic(&self) -> Option<String> {
        self.worker_panic.lock().unwrap().take()
    }

    fn record_fatal_runtime_error(&self, message: String) {
        let mut fatal = self.fatal_runtime_error.lock().unwrap();
        if fatal.is_none() {
            *fatal = Some(message);
        }
        drop(fatal);
        self.force_shutdown();
    }

    fn take_fatal_runtime_error(&self) -> Option<String> {
        self.fatal_runtime_error.lock().unwrap().take()
    }

    fn teardown_remaining_tasks(&self) {
        self.force_shutdown();
        let tasks: Vec<_> = {
            let _admission = self.lock_admission();
            self.tasks.read().unwrap().iter().cloned().collect()
        };
        // Admission is closed, and any earlier registration has finished. Drop
        // the lock before callbacks, including callbacks that attempt to spawn.

        for (task_index, slot) in tasks.iter().enumerate() {
            let (task_token, handle, unobserved_panic, output) = {
                let mut inner = slot
                    .inner
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                if !inner.occupied {
                    inner.occupied = false;
                    (None, std::ptr::null_mut(), None, inner.out_buf.take())
                } else if inner.completed {
                    inner.occupied = false;
                    (
                        None,
                        std::ptr::null_mut(),
                        inner.panic_info.take(),
                        inner.out_buf.take(),
                    )
                } else {
                    let generation = inner.generation;
                    let task_token = pack_task_token(task_index, generation);
                    inner.completed = true;
                    inner.occupied = false;
                    inner.running = false;
                    inner.queued = false;

                    let handle = inner.handle;

                    inner.handle = std::ptr::null_mut();
                    (Some(task_token), handle, None, inner.out_buf.take())
                }
            };
            if let Some(report) = unobserved_panic {
                crate::panic_unwind::write_unobserved_task_panic(&report);
            }
            // Output cleanup can call back into the executor. No slot lock is
            // held, and SessionGuard has not cleared the current scheduler yet.
            drop(output);
            let Some(task_token) = task_token else {
                continue;
            };
            io_poller::cancel_task(self.task_identity(task_token));
            crate::sync::task_finalized(self.task_identity(task_token));
            self.clear_task_timer(task_token);
            if !handle.is_null() {
                __rt__async_destroy(handle);
            }
        }
        // A group may still own completed results after its tasks' slots have
        // been reclaimed. Drain those owners before destroying the scheduler,
        // while callbacks can still resolve task handles through the session.
        let groups = {
            let mut groups = self.task_groups.lock().unwrap();
            std::mem::take(&mut *groups)
        };
        for group in groups.into_iter().flatten() {
            if crate::panic_unwind::is_unwinding() {
                drop(group);
            } else if let Err(report) = crate::panic_unwind::catch_executor_panic(|| drop(group)) {
                crate::panic_unwind::write_unobserved_task_panic(&report);
            }
        }
    }
}

trait StealSource {
    fn steal_batch_and_pop(&self, local: &Worker<TaskToken>) -> Steal<TaskToken>;
}

impl StealSource for Injector<TaskToken> {
    fn steal_batch_and_pop(&self, local: &Worker<TaskToken>) -> Steal<TaskToken> {
        self.steal_batch_and_pop(local)
    }
}

impl StealSource for Stealer<TaskToken> {
    fn steal_batch_and_pop(&self, local: &Worker<TaskToken>) -> Steal<TaskToken> {
        self.steal_batch_and_pop(local)
    }
}

/// A queue that its worker checks before every poll and usually finds empty.
struct WorkerQueue {
    tasks: HotMutex<VecDeque<TaskToken>>,
    // Sequentially consistent, like the mutex it stands in for when empty: a
    // worker publishes itself idle and then checks here, while a notifier
    // publishes here and then looks for an idle worker. One must see the other.
    len: AtomicUsize,
}

impl WorkerQueue {
    fn new() -> Self {
        Self {
            tasks: HotMutex::new(VecDeque::new()),
            len: AtomicUsize::new(0),
        }
    }

    fn push_back(&self, task: TaskToken) {
        let mut tasks = self.tasks.lock().unwrap();
        tasks.push_back(task);
        self.len.store(tasks.len(), Ordering::SeqCst);
    }

    fn pop_front(&self) -> Option<TaskToken> {
        if self.is_empty() {
            return None;
        }
        let mut tasks = self.tasks.lock().unwrap();
        let task = tasks.pop_front();
        self.len.store(tasks.len(), Ordering::SeqCst);
        task
    }

    fn drain(&self) -> Vec<TaskToken> {
        if self.is_empty() {
            return Vec::new();
        }
        let mut tasks = self.tasks.lock().unwrap();
        self.len.store(0, Ordering::SeqCst);
        tasks.drain(..).collect()
    }

    fn is_empty(&self) -> bool {
        self.len.load(Ordering::SeqCst) == 0
    }
}

enum QueueTarget {
    Yielded(usize),
    PinnedWorker(usize),
    Worker(usize),
    Global,
}

fn session_cell() -> &'static Mutex<Option<Arc<Scheduler>>> {
    static SESSION: OnceLock<Mutex<Option<Arc<Scheduler>>>> = OnceLock::new();
    SESSION.get_or_init(|| Mutex::new(None))
}

fn clear_scheduler_if_current(scheduler: &Arc<Scheduler>) {
    let mut session = session_cell().lock().unwrap();
    if session
        .as_ref()
        .is_some_and(|current| Arc::ptr_eq(current, scheduler))
    {
        *session = None;
    }
}

fn configured_worker_count() -> Result<usize, String> {
    if let Some(raw) = std::env::var_os("TARO_WORKERS") {
        let raw = raw
            .into_string()
            .map_err(|_| "TARO_WORKERS must contain valid Unicode".to_string())?;
        return raw
            .parse::<usize>()
            .ok()
            .filter(|count| *count > 0)
            .ok_or_else(|| format!("TARO_WORKERS must be a positive integer; got `{raw}`"));
    }
    Ok(thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1)
        .max(1))
}

fn configured_blocking_thread_count() -> usize {
    if let Ok(raw) = std::env::var("TARO_BLOCKING_THREADS")
        && let Ok(count) = raw.parse::<usize>()
        && count > 0
    {
        return count;
    }
    thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1)
        .clamp(1, 32)
}

fn configured_blocking_queue_capacity(worker_count: usize) -> usize {
    if let Ok(raw) = std::env::var("TARO_BLOCKING_QUEUE")
        && let Ok(capacity) = raw.parse::<usize>()
        && capacity > 0
    {
        return capacity;
    }
    worker_count.saturating_mul(4).max(1)
}

fn configured_deadlock_timeout() -> Option<StdDuration> {
    let raw = std::env::var("TARO_DEADLOCK_TIMEOUT_MS").ok()?;
    let millis = raw.parse::<u64>().ok()?;
    (millis > 0).then(|| StdDuration::from_millis(millis))
}

fn configured_blocking_warn_threshold() -> Option<StdDuration> {
    let raw = std::env::var("TARO_BLOCKING_WARN_MS").ok()?;
    let millis = raw.parse::<u64>().ok()?;
    (millis > 0).then(|| StdDuration::from_millis(millis))
}

fn runtime_configuration_error(message: String) -> ! {
    eprintln!("runtime configuration error: {message}");
    std::process::exit(2);
}

fn create_scheduler(rooted: bool) -> Arc<Scheduler> {
    let worker_count = match configured_worker_count() {
        Ok(worker_count) => worker_count,
        Err(error) => runtime_configuration_error(error),
    };
    let diagnostics = match RuntimeDiagnosticsConfig::from_env() {
        Ok(config) => RuntimeDiagnostics::new(config),
        Err(error) => runtime_configuration_error(error),
    };
    Scheduler::new_with_diagnostics(rooted, worker_count, diagnostics)
}

fn percentile(sorted_samples: &[u64], percentile: usize) -> u64 {
    if sorted_samples.is_empty() {
        return 0;
    }
    let rank = sorted_samples
        .len()
        .saturating_mul(percentile)
        .saturating_add(99)
        / 100;
    sorted_samples[rank.saturating_sub(1).min(sorted_samples.len() - 1)]
}

fn format_diagnostics_report(
    worker_count: usize,
    diagnostics: &RuntimeDiagnostics,
    stats: &RuntimeStatsSnapshot,
    gc: &GcStatsSnapshot,
    gc_baseline: &GcStatsSnapshot,
    task_counts: (usize, usize, usize, usize, usize),
) -> String {
    let mut output = String::new();
    if diagnostics.stats_enabled {
        let (live, queued, running, waiting, completed) = task_counts;
        let mut pauses = gc.pause_nanos_since(gc_baseline.collections);
        pauses.sort_unstable();
        let _ = writeln!(output, "runtime stats:");
        let _ = writeln!(output, "  config workers={worker_count}");
        let (leases, closing, close_errors) = crate::fd_lease::stats();
        let _ = writeln!(
            output,
            "  descriptors live_leases={leases} pending_close={closing} deferred_close_errors={close_errors}"
        );
        let _ = writeln!(
            output,
            "  tasks created={} polls={} completed={} cancelled={} panicked={} live={} peak_live={} queued={} running={} waiting={} retained_completed={}",
            stats.tasks_created,
            stats.task_polls,
            stats.task_completions,
            stats.task_cancellations,
            stats.task_panics,
            live,
            stats.peak_live_tasks,
            queued,
            running,
            waiting,
            completed,
        );
        let _ = writeln!(
            output,
            "  queues enqueues={} global={} worker={} pinned={} wakeups={} steals={} parks={} worker_unparks={} global_unparks={}",
            stats.queue_enqueues,
            stats.global_injects,
            stats.worker_enqueues,
            stats.pinned_enqueues,
            stats.wakeups,
            stats.steals,
            stats.parks,
            stats.worker_unparks,
            stats.global_unparks,
        );
        let _ = writeln!(
            output,
            "  timers registrations={} wakes={} io_wakes={}",
            stats.timer_registrations, stats.timer_wakeups, stats.io_wakeups,
        );
        let _ = writeln!(
            output,
            "  gc collections={} allocations={} frees={} allocated_bytes={} freed_bytes={} live_objects={} heap_live_bytes={} heap_goal={} memory_limit={} heap_reserved_bytes={} heap_free_page_bytes={} cached_span_refills={} released_bytes={} scavenged_bytes={} soft_limit_exceedances={}",
            gc.collections.saturating_sub(gc_baseline.collections),
            gc.total_allocations
                .saturating_sub(gc_baseline.total_allocations),
            gc.total_frees.saturating_sub(gc_baseline.total_frees),
            gc.total_allocated_bytes
                .saturating_sub(gc_baseline.total_allocated_bytes),
            gc.total_freed_bytes
                .saturating_sub(gc_baseline.total_freed_bytes),
            gc.live_objects,
            gc.live_bytes,
            gc.heap_goal,
            gc.configured_memory_limit
                .map_or_else(|| "off".to_string(), |value| value.to_string()),
            gc.segment_bytes,
            gc.free_bytes,
            gc.cached_span_refills
                .saturating_sub(gc_baseline.cached_span_refills),
            gc.released_bytes.saturating_sub(gc_baseline.released_bytes),
            gc.scavenged_bytes
                .saturating_sub(gc_baseline.scavenged_bytes),
            gc.soft_limit_exceedances
                .saturating_sub(gc_baseline.soft_limit_exceedances),
        );
        let _ = writeln!(
            output,
            "  gc_pause_ns count={} p50={} p95={} p99={} max={}",
            pauses.len(),
            percentile(&pauses, 50),
            percentile(&pauses, 95),
            percentile(&pauses, 99),
            pauses.last().copied().unwrap_or(0),
        );
        let _ = writeln!(
            output,
            "  gc_phase_ns rendezvous={} mark={} weak={} sweep={} scavenge={} pause_total={}",
            gc.phases
                .rendezvous_ns
                .saturating_sub(gc_baseline.phases.rendezvous_ns),
            gc.phases.mark_ns.saturating_sub(gc_baseline.phases.mark_ns),
            gc.phases.weak_ns.saturating_sub(gc_baseline.phases.weak_ns),
            gc.phases
                .sweep_ns
                .saturating_sub(gc_baseline.phases.sweep_ns),
            gc.phases
                .scavenge_ns
                .saturating_sub(gc_baseline.phases.scavenge_ns),
            gc.total_pause_ns.saturating_sub(gc_baseline.total_pause_ns),
        );
    }
    if let Some(trace) = diagnostics.trace_report(worker_count) {
        output.push_str(&trace);
    }
    output
}

fn write_diagnostics_report(output: &str) {
    let mut stderr = std::io::stderr().lock();
    let _ = stderr.write_all(output.as_bytes());
    let _ = stderr.flush();
}

fn write_idle_diagnostics_report() {
    let diagnostics = match RuntimeDiagnosticsConfig::from_env() {
        Ok(config) => RuntimeDiagnostics::new(config),
        Err(error) => runtime_configuration_error(error),
    };
    if !diagnostics.is_enabled() {
        return;
    }
    let worker_count = match configured_worker_count() {
        Ok(worker_count) => worker_count,
        Err(error) => runtime_configuration_error(error),
    };
    let output = format_diagnostics_report(
        worker_count,
        &diagnostics,
        &RuntimeStatsSnapshot::default(),
        &stats_snapshot(),
        &GcStatsSnapshot::default(),
        (0, 0, 0, 0, 0),
    );
    write_diagnostics_report(&output);
}

fn diagnostics_report_pending() -> &'static AtomicBool {
    static PENDING: AtomicBool = AtomicBool::new(false);
    &PENDING
}

fn install_scheduler(rooted: bool) -> Arc<Scheduler> {
    let scheduler = create_scheduler(rooted);
    let mut session = session_cell().lock().unwrap();
    if session.is_some() {
        panic!("ICE: executor session already active");
    }
    *session = Some(Arc::clone(&scheduler));
    scheduler
}

fn ensure_rootless_scheduler() -> Arc<Scheduler> {
    let mut session = session_cell().lock().unwrap();
    if let Some(scheduler) = session.as_ref() {
        assert!(
            !scheduler.rooted,
            "ICE: spawn called while rooted executor is active"
        );
        return Arc::clone(scheduler);
    }

    let scheduler = create_scheduler(false);
    *session = Some(Arc::clone(&scheduler));
    scheduler
}

/// Resolve identity before consulting the process's currently active session.
/// No TLS RefCell borrow survives into the caller or any generated cleanup.
fn current_scheduler() -> Option<Arc<Scheduler>> {
    let native = NATIVE_SCHEDULER.with(|cell| cell.borrow().as_ref().map(Weak::upgrade));
    native.unwrap_or_else(|| {
        current_worker_scheduler().or_else(|| session_cell().lock().unwrap().clone())
    })
}

fn has_native_scheduler_binding() -> bool {
    NATIVE_SCHEDULER.with(|cell| cell.borrow().is_some())
}

/// Whether a connection on this worker should busy-wait for its next request.
/// Peers of the gathering worker only do when it needs their help.
pub(crate) fn may_spin() -> bool {
    WORKER_CONTEXT.with(|cell| {
        cell.borrow().as_ref().is_none_or(|context| {
            context.worker_id == GATHERING_WORKER
                || !context.scheduler.gathering.load(Ordering::Relaxed)
        })
    })
}
pub(crate) fn other_work_runnable() -> bool {
    WORKER_CONTEXT.with(|cell| {
        cell.borrow()
            .as_ref()
            .is_none_or(|context| context.scheduler.has_runnable(context.worker_id))
    })
}

fn current_worker_scheduler() -> Option<Arc<Scheduler>> {
    WORKER_CONTEXT.with(|cell| {
        cell.borrow()
            .as_ref()
            .map(|context| Arc::clone(&context.scheduler))
    })
}

/// This thread's worker, if it can tell. Registering a wait holds the context while
/// it may wake others, and a wake only uses this to avoid waking its own thread:
/// that worker is running, so it isn't idle and won't be chosen.
fn current_worker_id() -> Option<usize> {
    WORKER_CONTEXT.with(|cell| {
        cell.try_borrow()
            .ok()
            .and_then(|context| context.as_ref().map(|context| context.worker_id))
    })
}

/// Worker numbers belong to one executor. A callback from another executor
/// must not suppress a wake just because its worker has the same number.
fn current_worker_id_for(scheduler: &Scheduler) -> Option<usize> {
    WORKER_CONTEXT.with(|cell| {
        let context = cell.try_borrow().ok()?;
        let context = context.as_ref()?;
        std::ptr::eq(Arc::as_ptr(&context.scheduler), scheduler).then_some(context.worker_id)
    })
}

/// A completion token has registered a generation-bound wake before this
/// marker is installed. Completion racing the pending return sets wake_requested
/// on the running slot; it cannot be lost when the worker stops polling.
pub(crate) fn wait_for_native_request() {
    WORKER_CONTEXT.with(|cell| {
        if let Some(context) = cell.borrow_mut().as_mut()
            && context.current_task.is_some()
        {
            context.current_wait_reason = Some(WaitReason::NativeRequest);
        }
    });
}

pub(crate) fn current_task_wake() -> Option<TaskWake> {
    WORKER_CONTEXT.with(|cell| {
        let borrow = cell.borrow();
        let context = borrow.as_ref()?;
        Some(TaskWake::new(&context.scheduler, context.current_task?))
    })
}

pub(crate) fn current_task_token() -> Option<TaskToken> {
    WORKER_CONTEXT.with(|cell| {
        cell.borrow()
            .as_ref()
            .and_then(|context| context.current_task)
    })
}

pub(crate) fn current_task_identity() -> Option<TaskIdentity> {
    WORKER_CONTEXT.with(|cell| {
        let borrow = cell.borrow();
        let context = borrow.as_ref()?;
        Some(context.scheduler.task_identity(context.current_task?))
    })
}

/// Record why the current task's pending poll is blocked, for task dumps and
/// deadlock detection.
fn set_current_wait_reason(reason: WaitReason) {
    WORKER_CONTEXT.with(|cell| {
        if let Some(context) = cell.borrow_mut().as_mut() {
            context.current_wait_reason = Some(reason);
        }
    });
}

/// Entry point: run an async handle to completion using the multithreaded
/// executor.
pub fn run_root(handle: *mut u8, out: *mut u8) {
    // Rooted execution owns the scheduler session for this async root. The
    // guard ensures background workers and remaining tasks are torn down on all
    // exit paths.
    let scheduler = install_scheduler(true);
    let _guard = SessionGuard {
        scheduler: Arc::clone(&scheduler),
    };

    scheduler.add_task_with_metadata(handle, out, None, 0, Some(0), false, SpawnMetadata::root());
    let local = scheduler.start();
    Arc::clone(&scheduler).worker_loop(0, local);
    crate::panic_unwind::set_test_harness_active(scheduler.test_mode);
    if let Some(message) = scheduler.take_fatal_runtime_error() {
        crate::panic_unwind::rethrow_panic_message(message);
    }
    let root_panic = scheduler.root_panic.lock().unwrap().take();
    if let Some(report) = root_panic {
        crate::panic_unwind::restore_panic_report(report);
        crate::panic_unwind::rethrow_restored_panic();
    }
    if let Some(message) = scheduler.take_worker_panic() {
        crate::panic_unwind::resume_test_panic(message);
    }
}

/// Run a standalone program's async `main`. Unlike `run_root`, completion
/// does not cancel or drain background tasks: the calling thread waits for the
/// root on its own and returns while other workers may still be running, and
/// the entry shim then exits the process.
pub fn run_main(handle: *mut u8, out: *mut u8) {
    let scheduler = install_scheduler(true);
    scheduler.exit_on_root.store(true, Ordering::Release);
    scheduler.add_task_with_metadata(handle, out, None, 0, Some(0), false, SpawnMetadata::root());
    let local = scheduler.start();
    // Worker 0 gets its own thread so a background task that never yields
    // cannot hold the main thread past the root's completion.
    let worker = Arc::clone(&scheduler);
    let join = thread::Builder::new()
        .name("taro-worker-0".into())
        .spawn(move || worker.worker_thread_entry(0, local))
        .expect("failed to spawn worker thread");
    scheduler.worker_joins.lock().unwrap().push(join);
    crate::garbage_collector::idle_wait(|| {
        let mut exited = scheduler.root_exited.lock().unwrap();
        while !*exited {
            exited = scheduler.root_exit_signal.wait(exited).unwrap();
        }
    });
    if let Some(message) = scheduler.take_fatal_runtime_error() {
        crate::panic_unwind::rethrow_panic_message(message);
    }
    let root_panic = scheduler.root_panic.lock().unwrap().take();
    if let Some(report) = root_panic {
        crate::panic_unwind::restore_panic_report(report);
        crate::panic_unwind::rethrow_restored_panic();
    }
    if let Some(message) = scheduler.take_worker_panic() {
        crate::panic_unwind::resume_test_panic(message);
    }
    scheduler.write_diagnostics_report();
}

/// Finish a standalone program after `main` and its defers returned. Tasks
/// still running are abandoned to process exit rather than cancelled.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__executor_finish_main() {
    let scheduler = session_cell().lock().unwrap().clone();
    match scheduler {
        Some(scheduler) => scheduler.write_diagnostics_report(),
        None => {
            if !diagnostics_report_pending().swap(false, Ordering::AcqRel) {
                write_idle_diagnostics_report();
            }
        }
    }
}

/// Check if the currently running task is cancelled.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__executor_is_current_task_cancelled() -> bool {
    if let Some(cancelled) = crate::task::polled_task_cancelled() {
        return cancelled;
    }
    WORKER_CONTEXT.with(|cell| {
        let borrow = match cell.try_borrow() {
            Ok(value) => value,
            Err(_) => return false,
        };
        if crate::task::forced_cancellation_for(borrow.as_ref().and_then(|context| {
            context
                .current_task
                .map(|token| context.scheduler.task_identity(token))
        })) {
            return true;
        }
        let context = match borrow.as_ref() {
            Some(c) => c,
            None => return false,
        };
        let current = match context.current_task {
            Some(token) => token,
            None => return false,
        };
        if let Some(cancelled) = &context.current_cancellation {
            return cancelled.load(Ordering::Acquire);
        }
        // Runtime-authored contexts outside a worker poll can still identify a
        // task without installing a cached cancellation flag.
        let (task_index, _) = unpack_task_token(current);
        if let Some(slot) = context.scheduler.lookup_task_slot(task_index) {
            let inner = slot
                .inner
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            inner.cancelled.load(Ordering::Acquire)
        } else {
            false
        }
    })
}

/// Spawn a task whose terminal outcome is published to a shared record for
/// its handles. `make` receives the scheduler, task token, result storage and
/// result size before any worker can poll the task.
fn spawn_shared_task(
    handle: *mut u8,
    output_desc: *const u8,
    metadata: SpawnMetadata,
    make: impl FnOnce(&Arc<Scheduler>, TaskToken, *mut u8, usize) -> Arc<TaskShared>,
) -> Arc<TaskShared> {
    let owner = unsafe { crate::task::OwnedAsyncHandle::from_raw(handle) };
    let output_desc =
        unsafe { output_desc.cast::<GcDesc>().as_ref() }.expect("task output descriptor");
    let scheduler = current_scheduler().unwrap_or_else(|| {
        assert!(
            !has_native_scheduler_binding(),
            "spawn called after native executor teardown"
        );
        ensure_rootless_scheduler()
    });
    // The slot roots the result storage until completion; afterwards only the
    // handle object traces it. This allocation may collect, so it precedes
    // admission: a spawner blocked on that lock cannot reach a safepoint.
    let mut out_buf = unsafe { TaskOutput::new(output_desc) };
    let out_ptr = out_buf.as_mut_ptr();
    let _admission = scheduler.open_admission();
    let owner_worker = current_worker_id().unwrap_or(0);
    let task_token = scheduler.prepare_task_with_metadata(
        owner.as_ptr(),
        out_ptr,
        Some(out_buf),
        owner_worker,
        true,
        metadata,
    );
    let _ = owner.into_raw(); // the installed slot now owns the adapter
    let shared = make(&scheduler, task_token, out_ptr, output_desc.size);
    let held = crate::task::take_hold_next_spawn();
    {
        let (task_index, _) = unpack_task_token(task_token);
        let slot = scheduler
            .lookup_task_slot(task_index)
            .expect("prepared task slot");
        let mut inner = slot.inner.lock().unwrap();
        inner.shared = Some(Arc::clone(&shared));
        // No handle owns the slot: it retires as soon as the task completes.
        inner.detached = true;
        if held {
            // Reads as already queued, so a wake can't queue it before its release.
            inner.queued = true;
        }
    }
    if held {
        crate::task::set_held_spawn(task_token);
        return shared;
    }
    // Work-first policy: start newly spawned tasks on the current worker to
    // preserve cache locality; movable tasks can still migrate after the first
    // pending poll via injector requeue.
    scheduler.schedule_task(task_token, Some(owner_worker));
    shared
}

/// Borrow message bytes inside a live immutable serialized panic payload.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__panic_payload_message(
    payload: crate::panic_unwind::RtString,
) -> crate::panic_unwind::RtString {
    const INVALID_PAYLOAD: &[u8] = b"invalid captured task panic payload";
    if payload.ptr.is_null() || payload.len == 0 {
        return crate::panic_unwind::RtString {
            ptr: INVALID_PAYLOAD.as_ptr(),
            len: INVALID_PAYLOAD.len(),
        };
    }
    let bytes = unsafe { std::slice::from_raw_parts(payload.ptr, payload.len) };
    let Some(message) = crate::panic_unwind::serialized_panic_message(bytes) else {
        return crate::panic_unwind::RtString {
            ptr: INVALID_PAYLOAD.as_ptr(),
            len: INVALID_PAYLOAD.len(),
        };
    };
    crate::panic_unwind::RtString {
        ptr: message.as_ptr(),
        len: message.len(),
    }
}

/// Re-raise the original panic captured in an owned native payload.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__panic_payload_rethrow(payload: crate::panic_unwind::RtString) -> ! {
    let report = if payload.ptr.is_null() || payload.len == 0 {
        None
    } else {
        let bytes = unsafe { std::slice::from_raw_parts(payload.ptr, payload.len) };
        crate::panic_unwind::deserialize_panic_report(bytes)
    }
    .unwrap_or_else(|| crate::panic_unwind::PanicReport {
        message: "invalid captured task panic payload".into(),
        backtrace: String::new(),
        location: None,
        logical_stack: Vec::new(),
        task_trace: Vec::new(),
    });
    // Restore the original report so the unwind shows the original backtrace.
    crate::panic_unwind::restore_panic_report(report);
    // Choose the appropriate unwind mechanism for the current context.
    crate::panic_unwind::rethrow_restored_panic()
}

/// Spawn through the public entry and keep the handle object rooted for the
/// rest of the test process.
#[cfg(test)]
fn spawn_test_task(handle: *mut u8, out_size: u64) -> u64 {
    let output = test_gc_layout(out_size as usize, 1);
    let empty = || crate::panic_unwind::RtString {
        ptr: std::ptr::null(),
        len: 0,
    };
    let object = __rt__task_spawn_with_metadata(
        handle,
        (output as *const GcDesc).cast(),
        empty(),
        empty(),
        0,
        0,
    );
    crate::garbage_collector::with_gc(|gc| gc.add_persistent_root(object.cast_const()));
    object as u64
}

#[cfg(test)]
fn poll_test_task(task: u64, out: *mut u8) -> u8 {
    outcome::poll_test_task(task as *mut u8, out)
}

#[cfg(test)]
fn task_completion_status_raw(task: u64) -> u8 {
    __rt__task_status(task as *mut u8)
}

#[cfg(test)]
fn cancel_task_raw(task: u64) {
    __rt__task_cancel(task as *mut u8);
}

/// Print a stable snapshot of live tasks, their spawn chains, and wait graph.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__executor_dump_tasks() {
    let scheduler = current_scheduler();
    if let Some(scheduler) = scheduler {
        let _ = scheduler.write_task_dump("task dump");
    } else {
        let mut stderr = std::io::stderr().lock();
        let _ = writeln!(stderr, "task dump: no active executor");
        let _ = stderr.flush();
    }
}

/// Create a new task group. Returns a group ID.
/// `cancel_on_panic`: 1 = cancel siblings on panic, 0 = independent.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_group_create(result_size: u64, cancel_on_panic: u8) -> u64 {
    let scheduler = current_scheduler().expect("task_group_create called outside executor");
    let _admission = scheduler.open_admission();
    let serial = NEXT_GROUP_SERIAL.fetch_add(1, Ordering::Relaxed) & GROUP_INDEX_MASK;
    let mut state = TaskGroupState {
        id: 0,
        tasks: Default::default(),
        completed: VecDeque::new(),
        discard_results: false,
        result_size: result_size as usize,
        waiter: None,
        spawning_closed: false,
        destroy_pending: false,
        cancelled: false,
        cancel_on_panic: cancel_on_panic != 0,
        ready_status: 0,
        panic_report: None,
    };
    let mut free = scheduler.free_group_slots.lock().unwrap();
    let mut groups = scheduler.task_groups.lock().unwrap();
    let idx = free.pop().unwrap_or_else(|| {
        groups.push(None);
        groups.len() - 1
    });
    let id = (serial << 32) | idx as u64;
    state.id = id;
    groups[idx] = Some(state);
    id
}

/// Spawn a task into a group. Returns the task token.
#[cfg(test)]
fn spawn_test_group_task(group_id: u64, handle: *mut u8, out_size: u64) -> u64 {
    let output = test_gc_layout(out_size as usize, 1);
    __rt__task_group_spawn_with_metadata(
        group_id,
        handle,
        (output as *const GcDesc).cast(),
        crate::panic_unwind::RtString {
            ptr: std::ptr::null(),
            len: 0,
        },
        crate::panic_unwind::RtString {
            ptr: std::ptr::null(),
            len: 0,
        },
        0,
        0,
    )
}

/// Spawn a task into a group with static source metadata.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_group_spawn_with_metadata(
    group_id: u64,
    handle: *mut u8,
    output_desc: *const u8,
    name: crate::panic_unwind::RtString,
    file: crate::panic_unwind::RtString,
    line: usize,
    column: usize,
) -> u64 {
    let owner = unsafe { crate::task::OwnedAsyncHandle::from_raw(handle) };
    let output_desc =
        unsafe { output_desc.cast::<GcDesc>().as_ref() }.expect("task output descriptor");
    let scheduler = current_scheduler().expect("task_group_spawn called outside executor");
    // This allocation may collect, so it precedes admission; see spawn_shared_task.
    let output = unsafe { TaskOutput::new(output_desc) };
    let _admission = scheduler.open_admission();
    let owner_worker = current_worker_id().unwrap_or(0);

    let token = scheduler.prepare_group_task_with_metadata(
        group_id,
        owner.as_ptr(),
        output,
        output_desc,
        owner_worker,
        SpawnMetadata::from_runtime(name, file, line, column),
    );
    let _ = owner.into_raw();
    scheduler.schedule_task(token, Some(owner_worker));
    token
}

/// Signal that no more tasks will be spawned into the group.
/// Drop the group's children's results as they finish. See TaskGroup.discardResults.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_group_discard_results(group_id: u64) {
    let scheduler = current_scheduler().expect("task_group_discard_results called outside executor");
    let mut groups = scheduler.task_groups.lock().unwrap();
    if let Some(group) = live_group_mut(&mut groups, group_id) {
        group.discard_results = true;
    }
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_group_close(group_id: u64) {
    let scheduler = current_scheduler().expect("task_group_close called outside executor");
    let mut groups = scheduler.task_groups.lock().unwrap();
    if let Some(group) = live_group_mut(&mut groups, group_id) {
        group.spawning_closed = true;
        // If already drained, wake waiter
        if group.tasks.is_empty() && group.completed.is_empty() {
            if let Some(waiter) = group.waiter.take() {
                drop(groups);
                scheduler.wake_tasks(&[waiter], false);
            }
        }
    }
}

/// Cancel all remaining tasks in the group.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_group_cancel_all(group_id: u64) {
    let scheduler = current_scheduler().expect("task_group_cancel_all called outside executor");
    let tokens: Vec<TaskToken> = {
        let mut groups = scheduler.task_groups.lock().unwrap();
        if let Some(group) = live_group_mut(&mut groups, group_id) {
            group.cancelled = true;
            group.tasks.iter().copied().collect()
        } else {
            return;
        }
    };
    for t in tokens {
        scheduler.cancel_task(t);
    }
}

/// Release the group owner, cancelling any remaining children. The runtime
/// retains a tombstone until their final notifications prevent premature reuse.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_group_destroy(group_id: u64) {
    let scheduler = current_scheduler().expect("task_group_destroy called outside executor");
    let _ = scheduler.destroy_task_group(group_id);
}

/// Destroy the group state and rethrow the first captured child panic, if any.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_group_destroy_and_rethrow_panic(group_id: u64) {
    let scheduler =
        current_scheduler().expect("task_group_destroy_and_rethrow_panic called outside executor");
    if let Some(report) = scheduler.destroy_task_group(group_id) {
        crate::panic_unwind::restore_panic_report(report);
        crate::panic_unwind::rethrow_restored_panic();
    }
}

pub(crate) const GROUP_POLL_RETIRED: u8 = 4;

/// Poll for the next completed result from a task group.
/// Returns 0 = pending, 1 = got result (written to `out`), 2 = group exhausted,
/// GROUP_POLL_RETIRED = the group's scope already ended.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_group_poll_next(group_id: u64, out: *mut u8) -> u8 {
    let (status, output) = WORKER_CONTEXT.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let context = borrow
            .as_mut()
            .expect("task_group_poll_next called outside executor worker");
        let current = context
            .current_task
            .expect("task_group_poll_next called with no current task");
        let mut groups = context.scheduler.task_groups.lock().unwrap();
        let group = match live_group_mut(&mut groups, group_id) {
            Some(g) => g,
            // Only an alias that escaped its scope can name a retired group.
            None => return (GROUP_POLL_RETIRED, None),
        };

        if group.destroy_pending {
            return (2, None);
        }

        // Check for completed results
        if let Some(completed) = group.completed.pop_front() {
            group.ready_status = 1;
            return (1, Some(completed.buf));
        }

        // If no tasks remain (and no completed values are queued), treat as exhausted.
        // This matches `TaskGroup.next()` / `for await` semantics where callers can
        // finish draining without requiring an explicit close first.
        if group.tasks.is_empty() {
            group.ready_status = 2;
            return (2, None);
        }

        // Otherwise, register as waiter
        match group.waiter {
            Some(waiter) if waiter != current => {
                panic!("task group already has an active waiter");
            }
            Some(_) => {}
            None => group.waiter = Some(current),
        }
        group.ready_status = 0;
        context.current_wait_reason = Some(WaitReason::TaskGroup(group_id));
        (0, None)
    });
    if let Some(output) = output {
        unsafe { output.copy_into(out) };
    }
    status
}

/// Return the most recent ready status observed by `__rt__task_group_poll_next`.
/// Returns 1 = yielded value, 2 = exhausted.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_group_next_status(group_id: u64) -> u8 {
    let scheduler = current_scheduler().expect("task_group_next_status called outside executor");
    let mut groups = scheduler.task_groups.lock().unwrap();
    let group = live_group_mut(&mut groups, group_id)
        .unwrap_or_else(|| panic!("invalid task group id {group_id}"));
    assert!(
        group.ready_status != 0,
        "task_group_next_status called before a ready group event"
    );
    group.ready_status
}

pub(crate) fn register_sleep(deadline: Instant) {
    WORKER_CONTEXT.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let context = borrow.as_mut().expect("sleep polled outside executor");
        let task_token = context
            .current_task
            .expect("sleep polled with no current task");
        context.scheduler.register_sleep(task_token, deadline);
        context.current_wait_reason = Some(WaitReason::Sleep(deadline));
    });
}

/// Also wake the current task after this duration, on its one timer. The wait
/// that follows returns on whichever wake comes first, so the caller has to
/// recheck both its operation and its deadline. A task suspends at one leaf
/// wait at a time, so nothing else can need the timer until that wait returns.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_wake_after(secs: u64, nanos: u32) {
    let deadline = Instant::now()
        .checked_add(StdDuration::new(secs, nanos))
        .unwrap_or_else(|| panic!("task wake duration overflow"));
    register_sleep(deadline);
}

/// Stop the wake armed by `__rt__task_wake_after`. Cancellation may skip this:
/// it ends the task, and a later wake for a finished task's token is ignored.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_clear_wake() {
    WORKER_CONTEXT.with(|cell| {
        let borrow = cell.borrow();
        let context = borrow.as_ref().expect("task wake cleared outside executor");
        let task_token = context
            .current_task
            .expect("task wake cleared with no current task");
        context.scheduler.clear_task_timer(task_token);
    });
}

pub(crate) fn register_io_wait(source_id: usize, interest: Interest) -> Result<(), i32> {
    WORKER_CONTEXT.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let context = borrow.as_mut().expect("async io polled outside executor");
        let current = context
            .current_task
            .expect("async io polled with no current task");
        context.scheduler.note_task_waited_on_io(current);

        io_poller::register_wait(
            source_id,
            TaskWake::new(&context.scheduler, current),
            interest,
        )?;
        context.scheduler.record_trace("io_wait", || {
            format!(
                "task={current} source={source_id} interest={}",
                match interest {
                    Interest::Read => "read",
                    Interest::Write => "write",
                }
            )
        });
        context.current_wait_reason = Some(WaitReason::Io {
            source_id,
            interest,
        });
        Ok(())
    })
}

pub(crate) fn register_sync_wait(sync_id: usize, kind: crate::sync::WaitKind) -> Result<(), i32> {
    WORKER_CONTEXT.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let context = borrow.as_mut().expect("sync wait polled outside executor");
        let current = context
            .current_task
            .expect("sync wait polled with no current task");

        crate::sync::register_wait(TaskWake::new(&context.scheduler, current), sync_id, kind)?;
        context.scheduler.record_trace("sync_wait", || {
            format!("task={current} resource={sync_id} kind={kind:?}")
        });
        context.current_wait_reason = Some(WaitReason::Sync { sync_id, kind });
        Ok(())
    })
}

/// Finish any lazily-created rootless executor work after a synchronous root
/// returns. When diagnostics were requested without async work, emit a
/// zero-task report so `taro run --runtime-stats` is never silently ignored.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__executor_finish_rootless() {
    let scheduler = {
        let session = session_cell().lock().unwrap();
        let Some(scheduler) = session.as_ref() else {
            drop(session);
            if diagnostics_report_pending().swap(false, Ordering::AcqRel) {
                return;
            }
            write_idle_diagnostics_report();
            return;
        };
        assert!(
            !scheduler.rooted,
            "ICE: finish_rootless called while rooted executor is active"
        );
        Arc::clone(scheduler)
    };

    let _guard = SessionGuard {
        scheduler: Arc::clone(&scheduler),
    };
    scheduler.begin_shutdown_drain();
    scheduler.finish_quiescent_drain();
    if scheduler.shutdown.load(Ordering::Acquire) {
        return;
    }
    // Workers drive cancellation (including native acknowledgment) to quiescence.
    let local = if scheduler.started.load(Ordering::Acquire) {
        panic!("ICE: rootless scheduler already started");
    } else {
        scheduler.start()
    };
    Arc::clone(&scheduler).worker_loop(0, local);
    crate::panic_unwind::set_test_harness_active(scheduler.test_mode);
    if let Some(message) = scheduler.take_fatal_runtime_error() {
        crate::panic_unwind::rethrow_panic_message(message);
    }
    if let Some(message) = scheduler.take_worker_panic() {
        crate::panic_unwind::resume_test_panic(message);
    }
}

/// Abort any lazily-created rootless executor state without polling queued
/// tasks. Used by the test harness after a panicking sync test.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__executor_abort_rootless() {
    let scheduler = {
        let session = session_cell().lock().unwrap();
        let Some(scheduler) = session.as_ref() else {
            return;
        };
        assert!(
            !scheduler.rooted,
            "ICE: abort_rootless called while rooted executor is active"
        );
        Arc::clone(scheduler)
    };

    // Abort is intentionally non-polling: queued async frames are dropped so a
    // panicking sync test cannot leave rootless work alive for the next test.
    scheduler.force_shutdown();
    scheduler.join_background_threads();
    scheduler.write_diagnostics_report();
    scheduler.teardown_remaining_tasks();
    clear_scheduler_if_current(&scheduler);
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::task::{__rt__async_create, __rt__async_run_root, TaskMobility};
    use std::collections::{HashMap, HashSet};
    use std::panic::{self, AssertUnwindSafe};
    use std::ptr;
    use std::sync::{Arc, Condvar, Mutex, mpsc};

    /// Serializes tests across modules that start the process-wide executor session.
    pub(crate) static TEST_ENV_LOCK: Mutex<()> = Mutex::new(());

    fn published_unit_output() -> TaskOutput {
        let output = TaskOutput::empty();
        output.publication().store(true, Ordering::Release);
        output
    }

    #[test]
    fn blocking_pool_applies_queue_backpressure_and_releases_capacity() {
        let scheduler = Scheduler::new(false, 1);
        let state = Arc::new(BlockingPoolState {
            scheduler: Arc::downgrade(&scheduler),
            queue_capacity: 1,
            queue: Mutex::new(BlockingQueueState {
                jobs: VecDeque::new(),
                capacity_waiters: VecDeque::new(),
            }),
            available: Condvar::new(),
            shutdown: AtomicBool::new(false),
            test_mode: true,
        });
        let first = BlockingJob::new(std::ptr::null_mut(), TaskOutput::empty());
        let second = BlockingJob::new(std::ptr::null_mut(), TaskOutput::empty());

        assert!(matches!(
            state.try_enqueue(&first, 11),
            BlockingEnqueue::Accepted
        ));
        assert!(matches!(
            state.try_enqueue(&second, 12),
            BlockingEnqueue::Full
        ));
        assert_eq!(state.queue.lock().unwrap().capacity_waiters.len(), 1);

        assert!(Arc::ptr_eq(&state.pop_job().unwrap(), &first));
        assert!(matches!(
            state.try_enqueue(&second, 12),
            BlockingEnqueue::Accepted
        ));
        state.shutdown();
    }

    #[test]
    fn worker_count_prefers_env_override() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let previous = std::env::var_os("TARO_WORKERS");
        unsafe { std::env::set_var("TARO_WORKERS", "2") };
        assert_eq!(configured_worker_count(), Ok(2));
        if let Some(previous) = previous {
            unsafe { std::env::set_var("TARO_WORKERS", previous) };
        } else {
            unsafe { std::env::remove_var("TARO_WORKERS") };
        }
    }

    #[test]
    fn worker_count_defaults_to_logical_cpu_count() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let previous = std::env::var_os("TARO_WORKERS");
        unsafe { std::env::remove_var("TARO_WORKERS") };
        let expected = thread::available_parallelism()
            .map(|count| count.get())
            .unwrap_or(1)
            .max(1);
        assert_eq!(configured_worker_count(), Ok(expected));
        if let Some(previous) = previous {
            unsafe { std::env::set_var("TARO_WORKERS", previous) };
        }
    }

    #[test]
    fn worker_count_rejects_invalid_values() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let previous = std::env::var_os("TARO_WORKERS");

        for invalid in ["", "0", "-1", "many"] {
            unsafe { std::env::set_var("TARO_WORKERS", invalid) };
            let error = configured_worker_count().unwrap_err();
            assert!(error.contains("positive integer"));
            assert!(error.contains(invalid));
        }

        if let Some(previous) = previous {
            unsafe { std::env::set_var("TARO_WORKERS", previous) };
        } else {
            unsafe { std::env::remove_var("TARO_WORKERS") };
        }
    }

    #[test]
    fn runtime_report_is_stable_and_grep_friendly() {
        let diagnostics = RuntimeDiagnostics::new(RuntimeDiagnosticsConfig {
            stats: true,
            trace: true,
            trace_capacity: 4,
        });
        diagnostics.record("task_complete", || "task=7".into());
        let stats = RuntimeStatsSnapshot {
            tasks_created: 1,
            task_polls: 2,
            task_completions: 1,
            peak_live_tasks: 1,
            queue_enqueues: 2,
            worker_enqueues: 2,
            ..RuntimeStatsSnapshot::default()
        };

        let gc = GcStatsSnapshot::default();
        let report = format_diagnostics_report(3, &diagnostics, &stats, &gc, &gc, (0, 0, 0, 0, 1));

        assert!(report.starts_with("runtime stats:\n  config workers=3\n"));
        assert!(report.contains("tasks created=1 polls=2 completed=1"));
        assert!(report.contains("queues enqueues=2 global=0 worker=2"));
        assert!(report.contains("gc collections=0 allocations=0 frees=0 allocated_bytes=0"));
        assert!(report.contains("gc_pause_ns count=0 p50=0 p95=0 p99=0 max=0"));
        assert!(!report.contains("cleanups queued="));
        assert!(report.contains("runtime trace: workers=3 events=1 capacity=4 dropped=0"));
        assert!(report.contains("event=task_complete task=7"));
    }

    #[test]
    fn runtime_report_percentiles_use_nearest_rank() {
        assert_eq!(percentile(&[], 50), 0);
        assert_eq!(percentile(&[10], 99), 10);
        assert_eq!(percentile(&[10, 20, 30, 40], 50), 20);
        assert_eq!(percentile(&[10, 20, 30, 40], 95), 40);
    }

    #[test]
    fn global_wake_batches_need_no_worker_flag_allocation() {
        for workers in [1, 4, 65] {
            let mut batch = WakeBatch::new(workers);
            batch.note_global();
            batch.note_global();
            batch.note_worker(workers); // Ignore an invalid worker as before.
            assert_eq!(batch.global_count, 2);
            assert_eq!(batch.worker_touched.capacity(), 0);
            assert_eq!(batch.touched_workers().count(), 0);

            batch.note_worker(workers - 1);
            batch.note_worker(0);
            batch.note_worker(workers - 1); // Notifications remain deduplicated.
            let expected = if workers == 1 {
                vec![0]
            } else {
                vec![0, workers - 1]
            };
            assert_eq!(batch.touched_workers().collect::<Vec<_>>(), expected);
        }
    }

    #[test]
    fn batched_wakeups_limit_unparks() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 4);
        scheduler.started.store(true, Ordering::Release);

        for worker_id in 0..scheduler.worker_count {
            scheduler.register_worker_thread(worker_id);
        }

        for _ in 0..8 {
            scheduler.push_task_slot(Arc::new(TaskSlot::new(
                TASK_INITIAL_GENERATION,
                ptr::null_mut(),
                ptr::null_mut(),
                None,
                0,
                TaskMobility::Movable,
            )));
        }
        for _ in 0..5 {
            scheduler.push_task_slot(Arc::new(TaskSlot::new(
                TASK_INITIAL_GENERATION,
                ptr::null_mut(),
                ptr::null_mut(),
                None,
                1,
                TaskMobility::Pinned,
            )));
        }
        for _ in 0..3 {
            scheduler.push_task_slot(Arc::new(TaskSlot::new(
                TASK_INITIAL_GENERATION,
                ptr::null_mut(),
                ptr::null_mut(),
                None,
                2,
                TaskMobility::Pinned,
            )));
        }

        let requests = (0..8)
            .map(|task_index| WakeRequest {
                task_token: pack_task_token(task_index, TASK_INITIAL_GENERATION),
                placement: Placement::Anywhere,
            })
            .chain((8..16).map(|task_index| WakeRequest {
                task_token: pack_task_token(task_index, TASK_INITIAL_GENERATION),
                placement: Placement::Prefer(0),
            }));

        // Waking a worker that isn't asleep would only leave it a spurious token.
        scheduler.worker_idle[1].store(true, Ordering::SeqCst);
        scheduler.worker_idle[2].store(true, Ordering::SeqCst);
        scheduler.schedule_tasks(requests);

        assert_eq!(scheduler.stats.wakeups.load(Ordering::Relaxed), 16);
        assert_eq!(scheduler.stats.global_injects.load(Ordering::Relaxed), 8);
        assert_eq!(scheduler.stats.global_unparks.load(Ordering::Relaxed), 4);
        assert_eq!(scheduler.stats.worker_unparks.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn global_wake_prefers_a_parked_peer_over_a_busy_worker() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new_with_diagnostics(
            false,
            2,
            RuntimeDiagnostics::new(crate::observability::RuntimeDiagnosticsConfig {
                trace: true,
                ..Default::default()
            }),
        );
        // Worker zero represents a non-yielding poll. Worker one runs the real
        // idle registration/parking path; selection is asserted from the trace.
        scheduler.worker_registered[0].store(true, Ordering::Release);
        scheduler.worker_polling[0].store(true, Ordering::Release);
        let local = scheduler.take_local_worker(1);
        let worker = {
            let scheduler = Arc::clone(&scheduler);
            thread::spawn(move || scheduler.worker_loop(1, local))
        };
        let deadline = Instant::now() + StdDuration::from_secs(2);
        while scheduler.idle_workers.load(Ordering::Acquire) == 0 && Instant::now() < deadline {
            thread::yield_now();
        }
        let parked = scheduler.idle_workers.load(Ordering::Acquire) != 0;
        scheduler.unpark_next_worker();
        let trace = scheduler.diagnostics.trace_report(2).unwrap();
        scheduler.force_shutdown();
        worker.join().unwrap();
        assert!(parked, "worker did not park");
        assert!(trace.contains("event=worker_unpark worker=1"), "{trace}");
        assert!(!trace.contains("event=worker_unpark worker=0"), "{trace}");
    }

    #[test]
    fn final_queue_check_forwards_a_reserved_wake_to_an_idle_peer() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new_with_diagnostics(
            false,
            3,
            RuntimeDiagnostics::new(crate::observability::RuntimeDiagnosticsConfig {
                trace: true,
                ..Default::default()
            }),
        );
        for id in 0..3 {
            scheduler.worker_registered[id].store(true, Ordering::Release);
        }
        scheduler.worker_polling[0].store(true, Ordering::Release);
        scheduler.worker_idle[1].store(true, Ordering::SeqCst);
        scheduler.worker_idle[2].store(true, Ordering::SeqCst);
        scheduler.wake_cursor.store(1, Ordering::Relaxed);
        // A notifier reserves worker one while its final check finds another
        // task. That task may never yield, so the reservation must reach two.
        scheduler.unpark_next_worker();
        assert!(!scheduler.worker_idle[1].load(Ordering::SeqCst));
        scheduler.leave_idle_for_task(1);
        let trace = scheduler.diagnostics.trace_report(3).unwrap();
        assert!(trace.contains("event=worker_unpark worker=1"), "{trace}");
        assert!(trace.contains("event=worker_unpark worker=2"), "{trace}");
        assert!(!trace.contains("event=worker_unpark worker=0"), "{trace}");
    }

    #[test]
    fn movable_remote_work_can_be_stolen_while_its_owner_is_busy() {
        let scheduler = Scheduler::new(false, 2);
        let local = scheduler.take_local_worker(1);
        scheduler.worker_polling[0].store(true, Ordering::Release);
        scheduler.remote_queues[0].push_back(42);
        assert_eq!(scheduler.next_task(1, &local), Some(42));
        assert!(scheduler.pinned_queues[0].is_empty());
    }

    #[test]
    fn global_wake_after_the_final_queue_check_retains_a_park_token() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 1);
        let ready = Arc::new(std::sync::Barrier::new(2));
        let resume = Arc::new(std::sync::Barrier::new(2));
        let (sent, received) = std::sync::mpsc::channel();
        let worker = {
            let scheduler = Arc::clone(&scheduler);
            let ready = Arc::clone(&ready);
            let resume = Arc::clone(&resume);
            thread::spawn(move || {
                let parker = scheduler.take_worker_parker(0);
                scheduler.register_worker_thread(0);
                // Idle is published before the final queue check, as `worker_loop` does.
                scheduler.worker_idle[0].store(true, Ordering::SeqCst);
                ready.wait();
                resume.wait();
                parker.park();
                sent.send(()).unwrap();
            })
        };
        ready.wait();
        assert_eq!(scheduler.idle_workers.load(Ordering::Acquire), 0);
        // Model work arriving after the last queue check but before the worker
        // sleeps. The notification must survive until it parks.
        scheduler.unpark_next_worker();
        resume.wait();
        let woke = received.recv_timeout(StdDuration::from_secs(2)).is_ok();
        scheduler.unpark_worker(0);
        worker.join().unwrap();
        assert!(woke, "a global wake was lost before the worker slept");
    }

    #[test]
    fn worker_wake_survives_unrelated_thread_parking() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 1);
        let notified = Arc::new(AtomicBool::new(false));
        let ready = Arc::new(AtomicBool::new(false));
        let (sent, received) = std::sync::mpsc::channel();
        let worker = {
            let scheduler = Arc::clone(&scheduler);
            let notified = Arc::clone(&notified);
            let ready = Arc::clone(&ready);
            thread::spawn(move || {
                let parker = scheduler.take_worker_parker(0);
                scheduler.register_worker_thread(0);
                ready.store(true, Ordering::Release);
                while !notified.load(Ordering::Acquire) {
                    std::hint::spin_loop();
                }
                // Standard-library synchronization and native cleanup can use
                // this thread's park token before the scheduler's idle wait.
                thread::park_timeout(StdDuration::ZERO);
                parker.park();
                sent.send(()).unwrap();
            })
        };
        while !ready.load(Ordering::Acquire) {
            std::hint::spin_loop();
        }
        scheduler.unpark_worker(0);
        notified.store(true, Ordering::Release);
        let woke = received.recv_timeout(StdDuration::from_secs(2)).is_ok();
        scheduler.unpark_worker(0);
        worker.join().unwrap();
        assert!(woke, "unrelated thread parking consumed the scheduler wake");
    }

    #[test]
    fn idle_workers_shutdown_without_a_collector_handshake() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 3);
        let local = scheduler.start();
        drop(local);

        let deadline = Instant::now() + StdDuration::from_secs(1);
        while Instant::now() < deadline {
            let all_registered = (1..scheduler.worker_count)
                .all(|worker_id| scheduler.worker_registered[worker_id].load(Ordering::Acquire));
            if all_registered {
                break;
            }
            thread::yield_now();
        }

        thread::sleep(StdDuration::from_millis(20));

        scheduler.force_shutdown();
        scheduler.join_background_threads();
    }

    #[test]
    fn workers_that_ran_managed_code_do_not_stall_collection() {
        static POLLED: AtomicUsize = AtomicUsize::new(0);
        unsafe extern "C-unwind" fn poll(_: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
            // Managed code registers its worker thread with the collector.
            crate::garbage_collector::ensure_thread_registered();
            POLLED.fetch_add(1, Ordering::AcqRel);
            1
        }
        unsafe extern "C-unwind" fn destroy(frame: *mut u8) {
            drop(unsafe { Box::from_raw(frame) });
        }
        let _guard = TEST_ENV_LOCK
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        POLLED.store(0, Ordering::Release);
        let scheduler = Scheduler::new(false, 3);
        // An outstanding task keeps the session open after these complete, so
        // the workers that ran them go idle instead of shutting down.
        scheduler.incomplete_tasks.fetch_add(1, Ordering::AcqRel);
        let local = scheduler.start();
        drop(local);
        const TASKS: usize = 16;
        for _ in 0..TASKS {
            let handle = crate::task::__rt__async_create(
                Box::into_raw(Box::new(0_u8)),
                poll as *const () as *const u8,
                destroy as *const () as *const u8,
                crate::task::TaskMobility::Movable as u8,
            );
            scheduler.add_task_with_metadata(
                handle,
                ptr::null_mut(),
                None,
                0,
                None,
                true,
                SpawnMetadata::new("managedWorker".into(), "src/work.tr".into(), 1, 1),
            );
        }
        let deadline = Instant::now() + StdDuration::from_secs(5);
        while POLLED.load(Ordering::Acquire) < TASKS && Instant::now() < deadline {
            thread::yield_now();
        }
        assert_eq!(POLLED.load(Ordering::Acquire), TASKS);
        // Let the workers that ran tasks go idle.
        thread::sleep(StdDuration::from_millis(50));

        let (done, collected) = std::sync::mpsc::channel();
        thread::spawn(move || {
            crate::garbage_collector::__gc__thread_attach();
            crate::garbage_collector::__gc__collect();
            crate::garbage_collector::__gc__thread_detach();
            let _ = done.send(());
        });
        if collected.recv_timeout(StdDuration::from_secs(5)).is_err() {
            // The stalled collector also blocks teardown; fail the process.
            eprintln!("an idle worker that ran managed code stalled the collection");
            std::process::exit(101);
        }

        scheduler.incomplete_tasks.fetch_sub(1, Ordering::AcqRel);
        scheduler.force_shutdown();
        scheduler.join_background_threads();
    }

    #[test]
    fn task_token_pack_unpack_roundtrip() {
        let token = pack_task_token(17, 42);
        let (index, generation) = unpack_task_token(token);
        assert_eq!(index, 17);
        assert_eq!(generation, 42);
    }

    #[test]
    fn wait_cycle_detection_returns_a_closed_deterministic_path() {
        let first = pack_task_token(1, 1);
        let second = pack_task_token(2, 1);
        let mut graph = HashMap::new();
        graph.insert(first, vec![second]);
        graph.insert(second, vec![first]);

        assert_eq!(find_wait_cycle(&graph), Some(vec![first, second, first]));
    }

    #[test]
    fn spawn_trace_retains_bounded_ancestry_after_parent_storage_is_retired() {
        let scheduler = Scheduler::new(false, 1);
        let parent = scheduler.add_task(ptr::null_mut(), ptr::null_mut(), None, 0, None, false);
        let (index, _) = unpack_task_token(parent);
        let slot = scheduler.lookup_task_slot(index).unwrap();
        slot.inner.lock().unwrap().spawn_trace = (0..MAX_TASK_TRACE_FRAMES)
            .map(|line| {
                SpawnMetadata::new(format!("parent{line}"), "parent.tr".into(), line, 1).frame
            })
            .collect();
        WORKER_CONTEXT.with(|cell| {
            cell.replace(Some(WorkerContext {
                scheduler: scheduler.clone(),
                worker_id: 0,
                current_task: Some(parent),
                current_cancellation: None,
                current_wait_reason: None,
            }));
        });
        let _context = WorkerContextGuard;
        let trace = scheduler.trace_for_spawn(
            SpawnMetadata::new("child".into(), "child.tr".into(), 17, 3),
            Vec::new(),
        );
        slot.inner.lock().unwrap().spawn_trace.clear();
        assert_eq!(trace.len(), MAX_TASK_TRACE_FRAMES);
        assert_eq!(trace[0].name, "parent1");
        assert_eq!(trace[0].file, "parent.tr");
        assert_eq!(
            trace[MAX_TASK_TRACE_FRAMES - 2].line,
            MAX_TASK_TRACE_FRAMES - 1
        );
        let child = trace.last().unwrap();
        assert_eq!(child.name, "child");
        assert_eq!(child.file, "child.tr");
        assert_eq!((child.line, child.column), (17, 3));
    }

    #[test]
    fn task_dump_includes_spawn_sites_wait_reasons_and_deadlock_cycle() {
        let scheduler = Scheduler::new(false, 1);
        let first = scheduler.add_task_with_metadata(
            ptr::null_mut(),
            ptr::null_mut(),
            None,
            0,
            None,
            true,
            SpawnMetadata::new("firstWorker".into(), "src/work.tr".into(), 10, 5),
        );
        let second = scheduler.add_task_with_metadata(
            ptr::null_mut(),
            ptr::null_mut(),
            None,
            0,
            None,
            true,
            SpawnMetadata::new("secondWorker".into(), "src/work.tr".into(), 20, 7),
        );

        for (token, dependency) in [(first, second), (second, first)] {
            let (index, generation) = unpack_task_token(token);
            let slot = scheduler.lookup_task_slot(index).unwrap();
            let mut inner = slot.inner.lock().unwrap();
            assert_eq!(inner.generation, generation);
            inner.queued = false;
            inner.wait_reason = Some(WaitReason::Task(dependency));
        }

        let dump = scheduler.build_task_dump("task dump");
        assert_eq!(dump.cycle, Some(vec![first, second, first]));
        assert!(dump.text.contains("`firstWorker` [waiting]"));
        assert!(dump.text.contains("spawned at src/work.tr:10:5"));
        assert!(
            dump.text
                .contains(&format!("waiting for task {}", format_task_token(second)))
        );
        assert!(dump.text.contains("definitive deadlock cycle:"));
    }

    #[test]
    fn timeout_dependency_is_not_a_definitive_deadlock_edge() {
        let scheduler = Scheduler::new(false, 1);
        let parent = scheduler.add_task(ptr::null_mut(), ptr::null_mut(), None, 0, None, true);
        let child = scheduler.add_task(ptr::null_mut(), ptr::null_mut(), None, 0, None, true);
        for (token, reason) in [
            (
                parent,
                WaitReason::TaskTimeout {
                    task: child,
                    deadline: Instant::now() + StdDuration::from_secs(1),
                },
            ),
            (child, WaitReason::Task(parent)),
        ] {
            let (index, _) = unpack_task_token(token);
            let slot = scheduler.lookup_task_slot(index).unwrap();
            let mut inner = slot.inner.lock().unwrap();
            inner.queued = false;
            inner.wait_reason = Some(reason);
        }

        let dump = scheduler.build_task_dump("task dump");
        assert_eq!(dump.cycle, None);
        assert!(dump.text.contains(" ms remaining"));
        assert!(dump.text.contains("no definitive internal cycle"));
    }

    #[test]
    fn deadlock_timeout_is_opt_in_and_requires_positive_milliseconds() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let previous = std::env::var_os("TARO_DEADLOCK_TIMEOUT_MS");

        unsafe { std::env::remove_var("TARO_DEADLOCK_TIMEOUT_MS") };
        assert_eq!(configured_deadlock_timeout(), None);
        unsafe { std::env::set_var("TARO_DEADLOCK_TIMEOUT_MS", "0") };
        assert_eq!(configured_deadlock_timeout(), None);
        unsafe { std::env::set_var("TARO_DEADLOCK_TIMEOUT_MS", "25") };
        assert_eq!(
            configured_deadlock_timeout(),
            Some(StdDuration::from_millis(25))
        );

        if let Some(previous) = previous {
            unsafe { std::env::set_var("TARO_DEADLOCK_TIMEOUT_MS", previous) };
        } else {
            unsafe { std::env::remove_var("TARO_DEADLOCK_TIMEOUT_MS") };
        }
    }

    #[test]
    fn blocking_warning_is_opt_in_and_requires_positive_milliseconds() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let previous = std::env::var_os("TARO_BLOCKING_WARN_MS");

        unsafe { std::env::remove_var("TARO_BLOCKING_WARN_MS") };
        assert_eq!(configured_blocking_warn_threshold(), None);
        unsafe { std::env::set_var("TARO_BLOCKING_WARN_MS", "0") };
        assert_eq!(configured_blocking_warn_threshold(), None);
        unsafe { std::env::set_var("TARO_BLOCKING_WARN_MS", "15") };
        assert_eq!(
            configured_blocking_warn_threshold(),
            Some(StdDuration::from_millis(15))
        );

        if let Some(previous) = previous {
            unsafe { std::env::set_var("TARO_BLOCKING_WARN_MS", previous) };
        } else {
            unsafe { std::env::remove_var("TARO_BLOCKING_WARN_MS") };
        }
    }

    #[test]
    fn consumed_completed_task_slot_is_reused() {
        let scheduler = Scheduler::new(false, 1);
        let slot = Arc::new(TaskSlot::new(
            TASK_INITIAL_GENERATION,
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            TaskMobility::Movable,
        ));
        {
            let mut inner = slot.inner.lock().unwrap();
            inner.completed = true;
        }
        scheduler.push_task_slot(Arc::clone(&slot));
        scheduler.timers.lock().unwrap().latest.push(None);

        let old_token = pack_task_token(0, TASK_INITIAL_GENERATION);
        {
            let mut inner = slot.inner.lock().unwrap();
            scheduler.reclaim_task_slot(old_token, &mut inner);
        }

        let new_token = scheduler.add_task(
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            None,
            false,
        );
        let (new_index, new_generation) = unpack_task_token(new_token);
        assert_eq!(new_index, 0);
        assert_ne!(new_generation, TASK_INITIAL_GENERATION);
    }

    #[test]
    fn stale_token_rejected_after_slot_reuse() {
        let scheduler = Scheduler::new(false, 1);
        let slot = Arc::new(TaskSlot::new(
            TASK_INITIAL_GENERATION,
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            TaskMobility::Movable,
        ));
        {
            let mut inner = slot.inner.lock().unwrap();
            inner.completed = true;
        }
        scheduler.push_task_slot(Arc::clone(&slot));
        scheduler.timers.lock().unwrap().latest.push(None);

        let stale_token = pack_task_token(0, TASK_INITIAL_GENERATION);
        {
            let mut inner = slot.inner.lock().unwrap();
            scheduler.reclaim_task_slot(stale_token, &mut inner);
        }
        let _current_token = scheduler.add_task(
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            None,
            false,
        );

        let panicked = panic::catch_unwind(AssertUnwindSafe(|| {
            scheduler.assert_spawned_token_live_or_panic(stale_token)
        }));
        assert!(panicked.is_err());
    }

    struct AbandonedPanicFrame {
        job: Weak<BlockingJob>,
        pool: Weak<BlockingPoolState>,
    }

    unsafe extern "C-unwind" fn abandoned_panic_poll(frame: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
        let frame = unsafe { &*frame.cast::<AbandonedPanicFrame>() };
        // Simulate the parent abandoning this already-running native call.
        frame.job.upgrade().unwrap().inner.lock().unwrap().abandoned = true;
        frame.pool.upgrade().unwrap().shutdown();
        let message = b"native abandoned panic";
        crate::panic_unwind::__rt__panic_unwind(crate::panic_unwind::RtString {
            ptr: message.as_ptr(),
            len: message.len(),
        });
    }

    unsafe extern "C-unwind" fn abandoned_panic_drop(frame: *mut u8) {
        drop(unsafe { Box::from_raw(frame.cast::<AbandonedPanicFrame>()) });
    }

    #[test]
    fn abandoned_running_native_panic_is_reported_once() {
        const PROBE: &str = "TARO_TEST_ABANDONED_NATIVE_PANIC";
        if std::env::var_os(PROBE).is_none() {
            let result = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "executor::tests::abandoned_running_native_panic_is_reported_once",
                    "--nocapture",
                ])
                .env(PROBE, "1")
                .output()
                .unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            assert_eq!(
                String::from_utf8_lossy(&result.stderr)
                    .matches("unobserved task panic: native abandoned panic")
                    .count(),
                1,
                "a panic after native abandonment must be reported exactly once"
            );
            return;
        }
        let scheduler = Scheduler::new(false, 1);
        let state = Arc::new(BlockingPoolState {
            scheduler: Arc::downgrade(&scheduler),
            queue_capacity: 1,
            queue: Mutex::new(BlockingQueueState {
                jobs: VecDeque::new(),
                capacity_waiters: VecDeque::new(),
            }),
            available: Condvar::new(),
            shutdown: AtomicBool::new(false),
            test_mode: true,
        });
        let job = BlockingJob::new(ptr::null_mut(), TaskOutput::empty());
        let handle = __rt__async_create(
            Box::into_raw(Box::new(AbandonedPanicFrame {
                job: Arc::downgrade(&job),
                pool: Arc::downgrade(&state),
            }))
            .cast(),
            abandoned_panic_poll as *const () as *const u8,
            abandoned_panic_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );
        job.inner.lock().unwrap().adapter = handle;
        assert!(matches!(
            state.try_enqueue(&job, 0),
            BlockingEnqueue::Accepted
        ));
        let worker = thread::spawn(move || blocking_worker_loop(state));
        worker.join().unwrap();
    }

    #[test]
    fn native_channel_close_wakes_waiter_in_a_later_session() {
        let _env = TEST_ENV_LOCK.lock().unwrap();
        assert!(session_cell().lock().unwrap().is_none());
        let old = Scheduler::new(false, 1);
        let old_identity = Arc::downgrade(&old);
        drop(old);
        let channel = unsafe {
            crate::sync::__gc__sync_channel_create(1, 1, crate::test_layout::value::<u8>())
        };
        assert!(!channel.is_null());
        struct Root(*mut u8);
        impl Drop for Root {
            fn drop(&mut self) {
                unsafe { crate::sync::__rt__sync_handle_release(self.0) };
            }
        }
        let _root = Root(channel);
        let next = Scheduler::new(false, 1);
        let token = next.add_task(ptr::null_mut(), ptr::null_mut(), None, 0, None, false);
        let (index, _) = unpack_task_token(token);
        let slot = next.lookup_task_slot(index).unwrap();
        slot.inner.lock().unwrap().queued = false;
        *session_cell().lock().unwrap() = Some(Arc::clone(&next));
        WORKER_CONTEXT.with(|cell| {
            cell.replace(Some(WorkerContext {
                scheduler: Arc::clone(&next),
                worker_id: 0,
                current_task: Some(token),
                current_wait_reason: None,
                current_cancellation: None,
            }))
        });
        let _context = WorkerContextGuard;
        let channel_id =
            crate::sync::wait_handle_id(channel, crate::sync::WaitKind::ChannelRecv).unwrap();
        register_sync_wait(channel_id, crate::sync::WaitKind::ChannelRecv).unwrap();
        let reason = WORKER_CONTEXT.with(|cell| {
            cell.borrow_mut()
                .as_mut()
                .unwrap()
                .current_wait_reason
                .take()
        });
        slot.inner.lock().unwrap().wait_reason = reason;
        // The native caller retains its channel independently of its expired
        // executor. This raw native fixture keeps that GC handle rooted above.
        let address = channel as usize;
        let worker = thread::spawn(move || {
            let _identity = NativeSchedulerGuard::new(old_identity);
            crate::sync::__rt__sync_channel_close(address as *mut u8)
        });
        let status = worker.join().unwrap();
        let awakened = slot.inner.lock().unwrap().queued;
        next.teardown_remaining_tasks();
        clear_scheduler_if_current(&next);
        assert_eq!(crate::sync::__rt__sync_channel_destroy(channel), 0);
        assert_eq!(status, 0);
        assert!(
            awakened,
            "a late native operation lost the new session's registered wake"
        );
    }

    #[cfg(unix)]
    #[test]
    fn native_source_close_wakes_waiter_in_a_later_session() {
        let _env = TEST_ENV_LOCK.lock().unwrap();
        assert!(session_cell().lock().unwrap().is_none());
        let old = Scheduler::new(false, 1);
        let old_identity = Arc::downgrade(&old);
        drop(old);
        let mut fds = [-1_i32; 2];
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
        let source = io_poller::adopt_fd(fds[0]);
        assert_ne!(source, 0);
        let next = Scheduler::new(false, 1);
        let token = next.add_task(ptr::null_mut(), ptr::null_mut(), None, 0, None, false);
        let (index, _) = unpack_task_token(token);
        let slot = next.lookup_task_slot(index).unwrap();
        slot.inner.lock().unwrap().queued = false;
        *session_cell().lock().unwrap() = Some(Arc::clone(&next));
        WORKER_CONTEXT.with(|cell| {
            cell.replace(Some(WorkerContext {
                scheduler: Arc::clone(&next),
                worker_id: 0,
                current_task: Some(token),
                current_wait_reason: None,
                current_cancellation: None,
            }))
        });
        let _context = WorkerContextGuard;
        register_io_wait(source, Interest::Read).unwrap();
        let reason = WORKER_CONTEXT.with(|cell| {
            cell.borrow_mut()
                .as_mut()
                .unwrap()
                .current_wait_reason
                .take()
        });
        slot.inner.lock().unwrap().wait_reason = reason;
        let worker = thread::spawn(move || {
            let _identity = NativeSchedulerGuard::new(old_identity);
            io_poller::__rt__async_io_close_source(source)
        });
        let status = worker.join().unwrap();
        let awakened = slot.inner.lock().unwrap().queued;
        next.teardown_remaining_tasks();
        clear_scheduler_if_current(&next);
        assert_eq!(unsafe { libc::close(fds[1]) }, 0);
        assert_eq!(status, 0);
        assert!(
            awakened,
            "a late native source close lost the new session's registered wake"
        );
    }

    fn check_finalization_namespace(io: bool) {
        let _env = TEST_ENV_LOCK.lock().unwrap();
        let old = Scheduler::new(false, 1);
        let old_token = old.add_task(ptr::null_mut(), ptr::null_mut(), None, 0, None, false);
        let next = Scheduler::new(false, 1);
        let token = next.add_task(ptr::null_mut(), ptr::null_mut(), None, 0, None, false);
        assert_eq!(
            old_token, token,
            "independent schedulers can use the same local token"
        );
        let (index, _) = unpack_task_token(token);
        let slot = next.lookup_task_slot(index).unwrap();
        slot.inner.lock().unwrap().queued = false;
        WORKER_CONTEXT.with(|cell| {
            cell.replace(Some(WorkerContext {
                scheduler: Arc::clone(&next),
                worker_id: 0,
                current_task: Some(token),
                current_wait_reason: None,
                current_cancellation: None,
            }))
        });
        let _context = WorkerContextGuard;
        if io {
            #[cfg(unix)]
            {
                let mut fds = [-1_i32; 2];
                assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
                let source = io_poller::adopt_fd(fds[0]);
                assert_ne!(source, 0);
                register_io_wait(source, Interest::Read).unwrap();
                old.complete_task(old_token);
                assert_eq!(io_poller::__rt__async_io_close_source(source), 0);
                let awakened = slot.inner.lock().unwrap().queued;
                next.teardown_remaining_tasks();
                assert_eq!(unsafe { libc::close(fds[1]) }, 0);
                assert!(awakened, "another scheduler finalized this I/O waiter");
            }
        } else {
            let mutex = crate::sync::__rt__sync_mutex_create();
            struct Root(*mut u8);
            impl Drop for Root {
                fn drop(&mut self) {
                    unsafe { crate::sync::__rt__sync_handle_release(self.0) };
                }
            }
            let _root = Root(mutex);
            assert_eq!(crate::sync::__rt__sync_mutex_try_lock(mutex), 0);
            old.complete_task(old_token);
            let status = crate::sync::__rt__sync_mutex_unlock(mutex);
            next.teardown_remaining_tasks();
            assert_eq!(crate::sync::__rt__sync_mutex_destroy(mutex), 0);
            assert_eq!(status, 0, "another scheduler finalized this mutex owner");
        }
    }

    #[test]
    fn finalization_does_not_release_another_schedulers_mutex() {
        check_finalization_namespace(false);
    }

    #[cfg(unix)]
    #[test]
    fn finalization_does_not_cancel_another_schedulers_io() {
        check_finalization_namespace(true);
    }

    fn check_rejected_native_spawn(expired: bool) {
        let mut original = Some(Scheduler::new(false, 1));
        let binding = Arc::downgrade(original.as_ref().unwrap());
        original.as_ref().unwrap().force_shutdown();
        if expired {
            drop(original.take());
        }
        let _identity = NativeSchedulerGuard::new(binding);
        let polls = Arc::new(AtomicUsize::new(0));
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = make_pending_handle(Arc::clone(&polls), Arc::clone(&drops));
        let result = crate::panic_unwind::catch_executor_panic(|| spawn_test_task(handle, 0));
        if let Some(scheduler) = original {
            scheduler.teardown_remaining_tasks();
        }
        let reclaimed = drops.load(Ordering::Acquire);
        // Keep the pre-fix regression itself leak-free on rejected calls that
        // forgot to consume their raw adapter. No scheduler received that handle.
        if result.is_err() && reclaimed == 0 {
            __rt__async_destroy(handle);
        }
        assert!(
            result.is_err(),
            "native work registered after executor shutdown"
        );
        assert_eq!(polls.load(Ordering::Acquire), 0);
        assert_eq!(
            reclaimed, 1,
            "rejected native spawn leaked its captured environment"
        );
    }

    #[test]
    fn native_spawn_rejects_a_shutting_down_executor() {
        check_rejected_native_spawn(false);
    }

    #[test]
    fn rejected_native_spawn_reclaims_its_captured_environment() {
        check_rejected_native_spawn(true);
    }

    #[test]
    fn native_spawn_racing_teardown_reclaims_the_adapter_once() {
        for _ in 0..24 {
            let scheduler = Scheduler::new(false, 1);
            let polls = Arc::new(AtomicUsize::new(0));
            let drops = Arc::new(AtomicUsize::new(0));
            let barrier = Arc::new(std::sync::Barrier::new(2));
            let binding = Arc::downgrade(&scheduler);
            let ready = Arc::clone(&barrier);
            let child_polls = Arc::clone(&polls);
            let child_drops = Arc::clone(&drops);
            let spawn = thread::spawn(move || {
                let _identity = NativeSchedulerGuard::new(binding);
                let handle = make_pending_handle(child_polls, child_drops);
                {
                    ready.wait();
                }
                let _outcome =
                    crate::panic_unwind::catch_executor_panic(|| spawn_test_task(handle, 0));
            });
            let closing = Arc::clone(&scheduler);
            let teardown = thread::spawn(move || {
                {
                    barrier.wait();
                }
                closing.teardown_remaining_tasks();
            });
            {
                spawn.join().unwrap();
                teardown.join().unwrap();
            }
            assert_eq!(polls.load(Ordering::Acquire), 0);
            assert_eq!(drops.load(Ordering::Acquire), 1);
            assert!(
                scheduler.tasks.read().unwrap().iter().all(|slot| !slot
                    .inner
                    .lock()
                    .unwrap()
                    .occupied)
            );
        }
    }

    #[test]
    fn rejected_group_spawn_reclaims_input_without_poisoning_group_state() {
        let scheduler = Scheduler::new(false, 1);
        let _identity = NativeSchedulerGuard::new(Arc::downgrade(&scheduler));
        let group = __rt__task_group_create(0, 0);
        __rt__task_group_close(group);
        let polls = Arc::new(AtomicUsize::new(0));
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = make_pending_handle(Arc::clone(&polls), Arc::clone(&drops));
        let result =
            crate::panic_unwind::catch_executor_panic(|| spawn_test_group_task(group, handle, 0));
        let poisoned = scheduler.task_groups.is_poisoned();
        let reclaimed = drops.load(Ordering::Acquire);
        // Repair only the old fixture state so its expected failure does not
        // cause another panic or leave the untransferred adapter rooted.
        if poisoned {
            scheduler.task_groups.clear_poison();
        }
        if reclaimed == 0 {
            __rt__async_destroy(handle);
        }
        scheduler.destroy_task_group(group);
        // Expected validation failures must not disable later admission or
        // teardown through a poisoned coordination-only mutex.
        scheduler.teardown_remaining_tasks();
        assert!(result.is_err());
        assert!(
            !poisoned,
            "a rejected group registration poisoned cleanup state"
        );
        assert_eq!(reclaimed, 1, "group rejection leaked its input environment");
        assert_eq!(polls.load(Ordering::Acquire), 0);
    }

    #[test]
    fn destroyed_group_reserves_its_id_until_live_children_finalize() {
        let scheduler = Scheduler::new(false, 1);
        scheduler
            .task_groups
            .lock()
            .unwrap()
            .push(Some(TaskGroupState {
                id: 0,
                tasks: Default::default(),
                discard_results: false,
                completed: VecDeque::new(),
                result_size: 0,
                waiter: None,
                spawning_closed: false,
                destroy_pending: false,
                cancelled: false,
                cancel_on_panic: false,
                ready_status: 0,
                panic_report: None,
            }));
        let descriptor = test_gc_layout(0, 1);
        let token = scheduler.add_group_task_with_metadata(
            0,
            ptr::null_mut(),
            descriptor,
            0,
            SpawnMetadata::anonymous(),
        );
        scheduler.destroy_task_group(0);
        assert!(
            scheduler.task_groups.lock().unwrap()[0].is_some(),
            "a running child still owns the group identity"
        );
        assert!(scheduler.free_group_slots.lock().unwrap().is_empty());
        let (index, _) = unpack_task_token(token);
        let slot = scheduler.lookup_task_slot(index).unwrap();
        assert!(slot.inner.lock().unwrap().cancelled.load(Ordering::Acquire));
        // A poll already in flight can return Ready after cancellation was
        // requested. Its output must be discarded, never sent to a new group.
        scheduler.complete_task(token);
        assert!(scheduler.task_groups.lock().unwrap()[0].is_none());
        assert_eq!(*scheduler.free_group_slots.lock().unwrap(), [0]);
        assert!(!slot.inner.lock().unwrap().occupied);
    }

    #[test]
    fn destroyed_group_retires_after_cancelled_or_panicked_children() {
        for panicked in [false, true] {
            let scheduler = Scheduler::new(false, 1);
            scheduler
                .task_groups
                .lock()
                .unwrap()
                .push(Some(TaskGroupState {
                    id: 0,
                    tasks: Default::default(),
                    discard_results: false,
                    completed: VecDeque::new(),
                    result_size: 0,
                    waiter: None,
                    spawning_closed: false,
                    destroy_pending: false,
                    cancelled: false,
                    cancel_on_panic: false,
                    ready_status: 0,
                    panic_report: None,
                }));
            let descriptor = test_gc_layout(0, 1);
            let token = scheduler.add_group_task_with_metadata(
                0,
                ptr::null_mut(),
                descriptor,
                0,
                SpawnMetadata::anonymous(),
            );
            scheduler.destroy_task_group(0);
            if panicked {
                scheduler.complete_task_panicked(
                    token,
                    crate::panic_unwind::PanicReport {
                        message: "late group panic".into(),
                        backtrace: String::new(),
                        location: None,
                        logical_stack: Vec::new(),
                        task_trace: Vec::new(),
                    },
                );
            } else {
                scheduler.complete_task_cancelled(token);
            }
            assert!(scheduler.task_groups.lock().unwrap()[0].is_none());
            assert_eq!(*scheduler.free_group_slots.lock().unwrap(), [0]);
            let (index, _) = unpack_task_token(token);
            assert!(
                !scheduler
                    .lookup_task_slot(index)
                    .unwrap()
                    .inner
                    .lock()
                    .unwrap()
                    .occupied
            );
            // A duplicate late notification must not recycle the slot twice.
            scheduler.notify_group_task_cancelled(0, token);
            assert_eq!(*scheduler.free_group_slots.lock().unwrap(), [0]);
        }
    }

    #[test]
    fn destroyed_group_discards_late_results_and_retires_its_identity() {
        let scheduler = Scheduler::new(false, 1);
        let token = pack_task_token(0, TASK_INITIAL_GENERATION);
        scheduler
            .task_groups
            .lock()
            .unwrap()
            .push(Some(TaskGroupState {
                id: 0,
                tasks: [token].into_iter().collect(),
                discard_results: false,
                completed: VecDeque::new(),
                result_size: 0,
                waiter: None,
                spawning_closed: false,
                destroy_pending: false,
                cancelled: false,
                cancel_on_panic: false,
                ready_status: 0,
                panic_report: None,
            }));
        scheduler.destroy_task_group(0);
        scheduler.notify_group_task_completed(0, token, Some(published_unit_output()));
        assert!(scheduler.task_groups.lock().unwrap()[0].is_none());
    }

    #[test]
    fn group_notifications_reject_nonmembers() {
        let scheduler = Scheduler::new(false, 1);
        scheduler
            .task_groups
            .lock()
            .unwrap()
            .push(Some(TaskGroupState {
                id: 0,
                tasks: [pack_task_token(1, TASK_INITIAL_GENERATION)].into_iter().collect(),
                discard_results: false,
                completed: VecDeque::new(),
                result_size: 0,
                waiter: None,
                spawning_closed: false,
                destroy_pending: false,
                cancelled: false,
                cancel_on_panic: false,
                ready_status: 0,
                panic_report: None,
            }));
        scheduler.notify_group_task_completed(
            0,
            pack_task_token(0, TASK_INITIAL_GENERATION),
            Some(published_unit_output()),
        );
        let (completed, live) = {
            let groups = scheduler.task_groups.lock().unwrap();
            let group = groups[0].as_ref().unwrap();
            (group.completed.len(), group.tasks.len())
        };
        assert_eq!(completed, 0);
        assert_eq!(live, 1);
    }

    #[test]
    fn completed_group_task_slots_are_reclaimed_without_waiting_for_session_exit() {
        let scheduler = Scheduler::new(false, 1);
        scheduler
            .task_groups
            .lock()
            .unwrap()
            .push(Some(TaskGroupState {
                id: 0,
                tasks: Default::default(),
                discard_results: false,
                completed: VecDeque::new(),
                result_size: 0,
                waiter: None,
                spawning_closed: false,
                destroy_pending: false,
                cancelled: false,
                cancel_on_panic: false,
                ready_status: 0,
                panic_report: None,
            }));
        let descriptor = test_gc_layout(0, 1);
        let token = scheduler.add_group_task_with_metadata(
            0,
            ptr::null_mut(),
            descriptor,
            0,
            SpawnMetadata::anonymous(),
        );
        scheduler.complete_task(token);
        let (index, _) = unpack_task_token(token);
        assert!(
            !scheduler
                .lookup_task_slot(index)
                .unwrap()
                .inner
                .lock()
                .unwrap()
                .occupied
        );
        assert_eq!(
            scheduler.task_groups.lock().unwrap()[0]
                .as_ref()
                .unwrap()
                .completed
                .len(),
            1
        );
    }

    #[test]
    fn completed_group_result_transfers_its_allocation_without_a_byte_clone() {
        let scheduler = Scheduler::new(false, 1);
        scheduler
            .task_groups
            .lock()
            .unwrap()
            .push(Some(TaskGroupState {
                id: 0,
                tasks: Default::default(),
                discard_results: false,
                completed: VecDeque::new(),
                result_size: 4,
                waiter: None,
                spawning_closed: false,
                destroy_pending: false,
                cancelled: false,
                cancel_on_panic: false,
                ready_status: 0,
                panic_report: None,
            }));
        let descriptor = test_gc_layout(4, 1);
        let mut bytes = unsafe { TaskOutput::new(&descriptor) };
        unsafe { ptr::copy_nonoverlapping([1_u8, 2, 3, 4].as_ptr(), bytes.as_mut_ptr(), 4) };
        bytes.publication().store(true, Ordering::Release);
        let allocation = bytes.as_mut_ptr();
        let token = scheduler.add_task(ptr::null_mut(), allocation, Some(bytes), 0, None, false);
        let (index, _) = unpack_task_token(token);
        let slot = scheduler.lookup_task_slot(index).unwrap();
        slot.inner.lock().unwrap().group_id = Some(0);
        scheduler.task_groups.lock().unwrap()[0]
            .as_mut()
            .unwrap()
            .tasks
            .insert(token);
        scheduler.complete_task(token);

        let groups = scheduler.task_groups.lock().unwrap();
        let group = groups[0].as_ref().unwrap();
        assert_eq!(group.completed.len(), 1);
        assert_eq!(group.completed[0].buf.as_ptr(), allocation);
        assert_eq!(
            unsafe { std::slice::from_raw_parts(group.completed[0].buf.as_ptr(), 4) },
            [1, 2, 3, 4]
        );
        assert!(group.tasks.is_empty());
        assert!(slot.inner.lock().unwrap().out_buf.is_none());
    }

    #[test]
    fn group_tasks_publish_complete_membership_and_transfer_zero_sized_results() {
        let scheduler = Scheduler::new(false, 2);
        scheduler
            .task_groups
            .lock()
            .unwrap()
            .push(Some(TaskGroupState {
                id: 0,
                tasks: Default::default(),
                discard_results: false,
                completed: VecDeque::new(),
                result_size: 0,
                waiter: None,
                spawning_closed: false,
                destroy_pending: false,
                cancelled: false,
                cancel_on_panic: false,
                ready_status: 0,
                panic_report: None,
            }));
        let prepared = scheduler.prepare_task_with_metadata(
            ptr::null_mut(),
            ptr::null_mut(),
            None,
            0,
            false,
            SpawnMetadata::anonymous(),
        );
        let (index, _) = unpack_task_token(prepared);
        let slot = scheduler.lookup_task_slot(index).unwrap();
        assert!(
            !slot.inner.lock().unwrap().queued,
            "preparation must not publish work"
        );
        scheduler.complete_task(prepared);

        let task = scheduler.add_group_task_with_metadata(
            0,
            ptr::null_mut(),
            &crate::test_layout::UNIT,
            0,
            SpawnMetadata::anonymous(),
        );
        let (index, generation) = unpack_task_token(task);
        let slot = scheduler.lookup_task_slot(index).unwrap();
        {
            let inner = slot.inner.lock().unwrap();
            assert!(inner.queued);
            assert_eq!(inner.generation, generation);
            assert_eq!(inner.group_id, Some(0));
            assert!(inner.out_buf.is_some());
        }
        assert_eq!(
            scheduler.task_groups.lock().unwrap()[0]
                .as_ref()
                .unwrap()
                .tasks
                .iter()
                .copied()
                .collect::<Vec<_>>(),
            [task]
        );
        scheduler.complete_task(task);
        let groups = scheduler.task_groups.lock().unwrap();
        let group = groups[0].as_ref().unwrap();
        assert!(group.tasks.is_empty());
        assert_eq!(
            group.completed.len(),
            1,
            "unit is still one completed value"
        );
        assert!(group.completed[0].buf.is_empty());
        assert!(slot.inner.lock().unwrap().out_buf.is_none());
    }

    #[test]
    fn blocking_adapter_catch_includes_cleanup_and_consumes_the_handle_once() {
        struct Probe {
            drops: Arc<AtomicUsize>,
            panic_in_poll: bool,
            panic_in_drop: bool,
        }
        unsafe extern "C-unwind" fn poll(frame: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
            if unsafe { (*frame.cast::<Probe>()).panic_in_poll } {
                crate::panic_unwind::rethrow_panic_message("blocking poll panic".into());
            }
            0 // Invalid suspension still has to destroy its adapter.
        }
        unsafe extern "C-unwind" fn destroy(frame: *mut u8) {
            let frame = unsafe { Box::from_raw(frame.cast::<Probe>()) };
            frame.drops.fetch_add(1, Ordering::SeqCst);
            let panics = frame.panic_in_drop;
            drop(frame);
            if panics {
                crate::panic_unwind::rethrow_panic_message("blocking drop panic".into());
            }
        }
        for (panic_in_poll, panic_in_drop, expected) in [
            (true, false, "blocking poll panic"),
            (false, true, "blocking drop panic"),
        ] {
            let drops = Arc::new(AtomicUsize::new(0));
            let handle = __rt__async_create(
                Box::into_raw(Box::new(Probe {
                    drops: Arc::clone(&drops),
                    panic_in_poll,
                    panic_in_drop,
                }))
                .cast(),
                poll as *const () as *const u8,
                destroy as *const () as *const u8,
                TaskMobility::Movable as u8,
            );
            let Err(error) = poll_blocking_adapter(handle, TaskOutput::empty()) else {
                panic!("blocking adapter should panic");
            };
            assert!(error.message.contains(expected), "{error:?}");
            assert_eq!(drops.load(Ordering::SeqCst), 1);
            assert!(crate::panic_unwind::take_full_panic_report().is_none());
        }
    }

    #[test]
    fn completed_unconsumed_task_remains_until_teardown() {
        let scheduler = Scheduler::new(false, 1);
        let token = scheduler.add_task(
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            None,
            false,
        );
        scheduler.complete_task(token);

        assert!(scheduler.free_slots.lock().unwrap().is_empty());

        let (task_index, task_generation) = unpack_task_token(token);
        let slot = scheduler
            .lookup_task_slot(task_index)
            .expect("completed task slot must still exist");
        let inner = slot.inner.lock().unwrap();
        assert!(inner.occupied);
        assert!(inner.completed);
        assert_eq!(inner.generation, task_generation);
        assert!(inner.out_buf.is_some());
    }

    #[test]
    fn detached_task_slot_is_reclaimed_on_completion() {
        let scheduler = Scheduler::new(false, 1);
        let token = scheduler.add_task(
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            None,
            true,
        );

        // A spawned task without a waiting handle retires its slot itself.
        scheduler
            .lookup_task_slot(unpack_task_token(token).0)
            .unwrap()
            .inner
            .lock()
            .unwrap()
            .detached = true;
        scheduler.complete_task(token);

        let (task_index, _) = unpack_task_token(token);
        let slot = scheduler.lookup_task_slot(task_index).unwrap();
        assert!(!slot.inner.lock().unwrap().occupied);
        assert_eq!(
            scheduler.free_slots.lock().unwrap().as_slice(),
            &[task_index]
        );
    }

    #[test]
    fn timer_latest_table_ignores_stale_deadlines() {
        let scheduler = Scheduler::new(false, 1);
        let token = scheduler.add_task(
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            None,
            false,
        );

        let old_deadline = Instant::now() + StdDuration::from_millis(10);
        let new_deadline = old_deadline + StdDuration::from_secs(5);
        scheduler.register_sleep(token, old_deadline);
        scheduler.register_sleep(token, new_deadline);

        let timers = scheduler.timers.lock().unwrap();
        let stale_entry = timers
            .heap
            .iter()
            .map(|entry| entry.0)
            .find(|entry| entry.deadline == old_deadline)
            .expect("old timer entry should still be in the heap");
        let latest_entry = timers
            .heap
            .iter()
            .map(|entry| entry.0)
            .find(|entry| entry.deadline == new_deadline)
            .expect("new timer entry should be in the heap");

        assert!(!Scheduler::is_live_timer_entry(&timers, stale_entry));
        assert!(Scheduler::is_live_timer_entry(&timers, latest_entry));
    }

    #[test]
    fn clear_task_timer_makes_due_timer_entry_stale() {
        let scheduler = Scheduler::new(false, 1);
        let token = scheduler.add_task(
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            None,
            false,
        );
        let (task_index, _) = unpack_task_token(token);
        let slot = scheduler.lookup_task_slot(task_index).unwrap();
        slot.inner.lock().unwrap().queued = false;

        let due = Instant::now()
            .checked_sub(StdDuration::from_millis(1))
            .unwrap_or_else(Instant::now);
        scheduler.register_sleep(token, due);
        scheduler.clear_task_timer(token);
        scheduler.wake_due_timers();

        let inner = slot.inner.lock().unwrap();
        assert!(!inner.queued, "cleared timer must not wake the task");
        drop(inner);
        let timers = scheduler.timers.lock().unwrap();
        assert!(timers.latest[task_index].is_none());
    }

    #[derive(Default)]
    struct OverlapState {
        in_flight: usize,
        max_in_flight: usize,
        threads: HashSet<thread::ThreadId>,
        open: bool,
    }

    #[derive(Default)]
    struct OverlapRecorder {
        state: Mutex<OverlapState>,
        ready: Condvar,
    }

    unsafe extern "C-unwind" fn overlap_poll(frame: *mut u8, _ctx: *mut u8, _out: *mut u8) -> u8 {
        let recorder = unsafe { &*(frame as *const Arc<OverlapRecorder>) };
        // A native wait must publish roots so a concurrent collection cannot
        // prevent the other worker from entering its poll callback.
        let mut state = recorder.state.lock().unwrap();
        state.threads.insert(thread::current().id());
        state.in_flight += 1;
        state.max_in_flight = state.max_in_flight.max(state.in_flight);
        if state.in_flight > 1 {
            state.open = true;
            recorder.ready.notify_all();
        }
        let (mut state, timeout) = recorder
            .ready
            .wait_timeout_while(state, StdDuration::from_secs(5), |state| !state.open)
            .unwrap();
        if timeout.timed_out() {
            // Let every task finish and the scheduler join before the test
            // reports missing overlap, rather than deadlocking on a regression.
            state.open = true;
            recorder.ready.notify_all();
        }
        state.in_flight -= 1;
        drop(state);
        1
    }

    unsafe extern "C-unwind" fn overlap_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut Arc<OverlapRecorder>) };
    }

    #[test]
    fn movable_work_overlaps_and_steals_from_victim_queue() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 4);
        let recorder = Arc::new(OverlapRecorder::default());

        for _ in 0..4 {
            let handle = __rt__async_create(
                Box::into_raw(Box::new(Arc::clone(&recorder))) as *mut u8,
                overlap_poll as *const () as *const u8,
                overlap_drop as *const () as *const u8,
                TaskMobility::Movable as u8,
            );
            let _ = scheduler.add_task(handle, ptr::null_mut(), None, 0, Some(0), false);
        }

        let local = scheduler.start();
        // Peers may steal directly from worker zero's remote queue during
        // startup; they need not wait for zero to drain it into its deque.
        Arc::clone(&scheduler).worker_loop(0, local);
        scheduler.join_background_threads();

        let state = recorder.state.lock().unwrap();
        let max_in_flight = state.max_in_flight;
        let thread_count = state.threads.len();
        let steals = scheduler.stats.steals.load(Ordering::Relaxed);
        assert!(
            max_in_flight > 1,
            "expected concurrent overlap across workers, observed max in-flight {max_in_flight}"
        );
        assert!(
            thread_count > 1,
            "expected work to run on multiple workers, observed {thread_count} worker thread(s)"
        );
        assert!(
            steals > 0,
            "expected at least one victim-queue steal, observed {steals}"
        );
    }

    #[derive(Clone)]
    struct ThreadRecorder {
        visits: Arc<Mutex<HashMap<usize, HashSet<String>>>>,
    }

    impl ThreadRecorder {
        fn record(&self, task_id: usize) {
            let thread_name = thread::current()
                .name()
                .map(str::to_string)
                .unwrap_or_else(|| format!("{:?}", thread::current().id()));
            self.visits
                .lock()
                .unwrap()
                .entry(task_id)
                .or_default()
                .insert(thread_name);
        }
    }

    struct ChildFrame {
        task_id: usize,
        remaining: usize,
        recorder: ThreadRecorder,
    }

    unsafe extern "C-unwind" fn child_poll(frame: *mut u8, _ctx: *mut u8, _out: *mut u8) -> u8 {
        let frame = unsafe { &mut *(frame as *mut ChildFrame) };
        frame.recorder.record(frame.task_id);
        if frame.remaining == 0 {
            1
        } else {
            frame.remaining -= 1;
            0
        }
    }

    unsafe extern "C-unwind" fn child_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut ChildFrame) };
    }

    struct RootFrame {
        mobility: TaskMobility,
        recorder: ThreadRecorder,
        child_ids: Vec<u64>,
        child_done: Vec<bool>,
        spawned: bool,
        child_count: usize,
        polls_per_child: usize,
    }

    unsafe extern "C-unwind" fn root_poll(frame: *mut u8, _ctx: *mut u8, _out: *mut u8) -> u8 {
        let frame = unsafe { &mut *(frame as *mut RootFrame) };
        if !frame.spawned {
            for task_id in 0..frame.child_count {
                let child = Box::new(ChildFrame {
                    task_id,
                    remaining: frame.polls_per_child,
                    recorder: frame.recorder.clone(),
                });
                let handle = __rt__async_create(
                    Box::into_raw(child) as *mut u8,
                    child_poll as *const () as *const u8,
                    child_drop as *const () as *const u8,
                    frame.mobility as u8,
                );
                frame.child_ids.push(spawn_test_task(handle, 0));
                frame.child_done.push(false);
            }
            frame.spawned = true;
            return 0;
        }

        let mut all_done = true;
        for (index, &task_id) in frame.child_ids.iter().enumerate() {
            if frame.child_done[index] {
                continue;
            }
            let status = poll_test_task(task_id, std::ptr::null_mut());
            if status == 0 {
                all_done = false;
            } else {
                frame.child_done[index] = true;
            }
        }
        u8::from(all_done)
    }

    unsafe extern "C-unwind" fn root_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut RootFrame) };
    }

    fn run_recording_root(mobility: TaskMobility) -> HashMap<usize, HashSet<String>> {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        unsafe { std::env::set_var("TARO_WORKERS", "4") };

        let visits = Arc::new(Mutex::new(HashMap::new()));
        let root = Box::new(RootFrame {
            mobility,
            recorder: ThreadRecorder {
                visits: Arc::clone(&visits),
            },
            child_ids: Vec::new(),
            child_done: Vec::new(),
            spawned: false,
            child_count: 128,
            polls_per_child: 8,
        });
        let handle = __rt__async_create(
            Box::into_raw(root) as *mut u8,
            root_poll as *const () as *const u8,
            root_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );

        __rt__async_run_root(handle, std::ptr::null_mut());
        unsafe { std::env::remove_var("TARO_WORKERS") };
        Arc::try_unwrap(visits).unwrap().into_inner().unwrap()
    }

    #[test]
    fn movable_tasks_can_migrate() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 2);
        let visits = Arc::new(Mutex::new(HashMap::new()));
        let handle = __rt__async_create(
            Box::into_raw(Box::new(ChildFrame {
                task_id: 0,
                remaining: 1,
                recorder: ThreadRecorder {
                    visits: Arc::clone(&visits),
                },
            })) as *mut u8,
            child_poll as *const () as *const u8,
            child_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );
        let token = scheduler.add_task(
            handle,
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            Some(0),
            false,
        );
        // Pending work may legally finish on its original worker. A fast
        // workload cannot require incidental migration. Drive its first poll
        // on worker 0, have the load review share its continuation as it would
        // from a stuck worker, then let worker 1 consume it.
        for worker_id in 0..2 {
            let local = scheduler.local_workers.lock().unwrap()[worker_id]
                .take()
                .unwrap();
            let worker_scheduler = Arc::clone(&scheduler);
            thread::Builder::new()
                .name(format!("migration-worker-{worker_id}"))
                .spawn(move || {
                    WORKER_CONTEXT.with(|cell| {
                        *cell.borrow_mut() = Some(WorkerContext {
                            scheduler: Arc::clone(&worker_scheduler),
                            worker_id,
                            current_task: None,
                            current_wait_reason: None,
                            current_cancellation: None,
                        });
                    });
                    let _context = WorkerContextGuard;
                    let next = worker_scheduler
                        .next_task(worker_id, &local)
                        .expect("queued movable continuation");
                    assert_eq!(next, token);
                    worker_scheduler.run_task(worker_id, next);
                })
                .unwrap()
                .join()
                .unwrap();
            if worker_id == 0 {
                review_with_no_polls_finished(&scheduler);
            }
        }
        assert_eq!(scheduler.incomplete_tasks.load(Ordering::Acquire), 0);
        assert_eq!(visits.lock().unwrap().get(&0).unwrap().len(), 2);
        scheduler.teardown_remaining_tasks();
    }

    fn review_with_no_polls_finished(scheduler: &Scheduler) {
        let mut polls: Vec<u64> = scheduler
            .yielded
            .iter()
            .map(|yielded| yielded.polls.load(Ordering::Relaxed))
            .collect();
        scheduler.review_load(&mut polls, LOAD_REVIEW_INTERVAL);
    }

    fn scheduler_with_placeholder_tasks(workers: usize, tasks: usize) -> Arc<Scheduler> {
        let scheduler = Scheduler::new(false, workers);
        for _ in 0..tasks {
            scheduler.push_task_slot(Arc::new(TaskSlot::new(
                TASK_INITIAL_GENERATION,
                ptr::null_mut(),
                ptr::null_mut(),
                None,
                0,
                TaskMobility::Movable,
            )));
        }
        scheduler.started.store(true, Ordering::Release);
        scheduler
    }

    fn yield_tasks(scheduler: &Scheduler, worker_id: usize, tasks: std::ops::Range<u32>) {
        scheduler.schedule_tasks(tasks.map(|task_index| WakeRequest {
            task_token: pack_task_token(task_index as _, TASK_INITIAL_GENERATION),
            placement: Placement::Yielded(worker_id),
        }));
    }

    #[test]
    fn foreign_worker_does_not_suppress_another_executors_wake() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = scheduler_with_placeholder_tasks(1, 1);
        let foreign = Scheduler::new(false, 1);
        WORKER_CONTEXT.with(|cell| {
            cell.replace(Some(WorkerContext {
                scheduler: foreign,
                worker_id: 0,
                current_task: None,
                current_cancellation: None,
                current_wait_reason: None,
            }));
        });
        let _context = WorkerContextGuard;
        let task = pack_task_token(0, TASK_INITIAL_GENERATION);
        scheduler.worker_idle[0].store(true, Ordering::SeqCst);
        scheduler.schedule_task(task, Some(0));
        assert!(
            !scheduler.worker_idle[0].load(Ordering::SeqCst),
            "worker IDs are local to their executor, so this worker must wake"
        );
        assert_eq!(scheduler.remote_queues[0].pop_front(), Some(task));

        scheduler
            .lookup_task_slot(0)
            .unwrap()
            .inner
            .lock()
            .unwrap()
            .queued = false;
        scheduler.worker_registered[0].store(true, Ordering::Release);
        scheduler.worker_idle[0].store(true, Ordering::SeqCst);
        scheduler.schedule_task(task, None);
        assert!(
            !scheduler.worker_idle[0].load(Ordering::SeqCst),
            "a foreign worker zero is not this executor's only worker"
        );
    }

    #[test]
    fn a_yielded_task_stays_with_its_worker_and_wakes_nobody() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = scheduler_with_placeholder_tasks(2, 1);
        for worker in &scheduler.worker_idle {
            worker.store(true, Ordering::SeqCst);
        }
        yield_tasks(&scheduler, 0, 0..1);
        assert!(
            scheduler
                .worker_idle
                .iter()
                .all(|idle| idle.load(Ordering::SeqCst))
        );
        let peer = scheduler.take_local_worker(1);
        assert_eq!(scheduler.next_task(1, &peer), None);
        let owner = scheduler.take_local_worker(0);
        assert!(scheduler.next_task(0, &owner).is_some());
    }

    #[test]
    fn a_worker_stuck_in_one_poll_gives_up_its_yielded_tasks() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = scheduler_with_placeholder_tasks(2, 3);
        yield_tasks(&scheduler, 0, 0..3);
        review_with_no_polls_finished(&scheduler);
        assert!(scheduler.yielded[0].tasks.is_empty());
        assert!(!scheduler.gathering.load(Ordering::Relaxed));
        let peer = scheduler.take_local_worker(1);
        assert!(scheduler.next_task(1, &peer).is_some());
    }

    #[test]
    fn a_stuck_worker_stops_gathering_even_with_nothing_yielded() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = scheduler_with_placeholder_tasks(2, 0);
        review_with_no_polls_finished(&scheduler);
        assert!(!scheduler.gathering.load(Ordering::Relaxed));
    }

    #[test]
    fn a_sleeping_worker_is_not_stuck() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = scheduler_with_placeholder_tasks(2, 0);
        scheduler.gathering.store(false, Ordering::Relaxed);
        scheduler.worker_idle[0].store(true, Ordering::SeqCst);
        review_with_no_polls_finished(&scheduler);
        assert!(scheduler.gathering.load(Ordering::Relaxed));
    }

    #[test]
    fn an_overloaded_worker_shares_half_of_its_yielded_tasks() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = scheduler_with_placeholder_tasks(2, 8);
        yield_tasks(&scheduler, 0, 0..8);
        // Four polls in a review interval leaves the last of eight waiting for two.
        scheduler.yielded[0].polls.store(4, Ordering::Relaxed);
        let mut polls = vec![0, 0];
        scheduler.review_load(&mut polls, StdDuration::from_millis(1));
        assert_eq!(scheduler.yielded[0].tasks.len(), 4);
        assert!(!scheduler.gathering.load(Ordering::Relaxed));
        assert_eq!(polls[0], 4);
    }

    #[test]
    fn a_worker_keeping_up_keeps_its_yielded_tasks() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = scheduler_with_placeholder_tasks(2, 8);
        yield_tasks(&scheduler, 0, 0..8);
        scheduler.yielded[0].polls.store(100, Ordering::Relaxed);
        let mut polls = vec![0, 0];
        scheduler.review_load(&mut polls, StdDuration::from_millis(1));
        assert_eq!(scheduler.yielded[0].tasks.len(), 8);
        assert!(scheduler.gathering.load(Ordering::Relaxed));
    }

    #[test]
    fn yielded_tasks_are_not_overtaken_forever_by_other_work() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let tasks = YIELD_FAIRNESS_INTERVAL + 1;
        let scheduler = scheduler_with_placeholder_tasks(2, tasks);
        yield_tasks(&scheduler, 0, 0..1);
        scheduler.schedule_tasks((1..tasks).map(|task_index| WakeRequest {
            task_token: pack_task_token(task_index as _, TASK_INITIAL_GENERATION),
            placement: Placement::Anywhere,
        }));
        let yielded_token = pack_task_token(0, TASK_INITIAL_GENERATION);
        let local = scheduler.take_local_worker(0);
        let taken: Vec<_> = (0..YIELD_FAIRNESS_INTERVAL)
            .map(|_| scheduler.next_task(0, &local).unwrap())
            .collect();
        assert_eq!(taken.last(), Some(&yielded_token));
    }

    #[test]
    fn at_most_half_of_the_workers_search_and_they_absorb_wakes() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = scheduler_with_placeholder_tasks(4, 0);
        assert!(scheduler.enter_search());
        assert!(scheduler.enter_search());
        assert!(!scheduler.enter_search());
        scheduler.worker_registered[3].store(true, Ordering::Release);
        scheduler.worker_idle[3].store(true, Ordering::SeqCst);
        scheduler.unpark_next_worker();
        assert!(scheduler.worker_idle[3].load(Ordering::SeqCst));
        scheduler.leave_search(false);
        scheduler.unpark_next_worker();
        assert!(scheduler.worker_idle[3].load(Ordering::SeqCst));
        // The last searcher to find work hands the search on.
        scheduler.leave_search(true);
        assert!(!scheduler.worker_idle[3].load(Ordering::SeqCst));
    }

    #[test]
    fn a_lone_worker_still_gets_a_turn_for_its_only_searcher() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = scheduler_with_placeholder_tasks(1, 0);
        assert!(scheduler.enter_search());
        assert!(!scheduler.enter_search());
        scheduler.leave_search(false);
    }

    #[test]
    fn a_wake_while_registering_a_wait_does_not_need_the_worker_context() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = scheduler_with_placeholder_tasks(2, 1);
        scheduler.worker_registered[1].store(true, Ordering::Release);
        scheduler.worker_idle[1].store(true, Ordering::SeqCst);
        WORKER_CONTEXT.with(|cell| {
            *cell.borrow_mut() = Some(WorkerContext {
                scheduler: Arc::clone(&scheduler),
                worker_id: 0,
                current_task: None,
                current_wait_reason: None,
                current_cancellation: None,
            });
        });
        let context = WorkerContextGuard;
        WORKER_CONTEXT.with(|cell| {
            // As `register_sync_wait` does while the sync layer wakes a waiter.
            let _registering = cell.borrow_mut();
            scheduler.schedule_task(pack_task_token(0, TASK_INITIAL_GENERATION), Some(1));
        });
        drop(context);
        assert!(!scheduler.worker_idle[1].load(Ordering::SeqCst));
    }

    struct RescueFrame {
        rescued: Arc<AtomicBool>,
        polls: usize,
    }

    unsafe extern "C-unwind" fn rescue_poll(frame: *mut u8, _ctx: *mut u8, _out: *mut u8) -> u8 {
        let frame = unsafe { &mut *(frame as *mut RescueFrame) };
        frame.polls += 1;
        if frame.polls == 1 {
            return 0;
        }
        frame.rescued.store(true, Ordering::Release);
        1
    }

    unsafe extern "C-unwind" fn rescue_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut RescueFrame) };
    }

    #[test]
    fn a_yielded_task_is_rescued_from_a_stuck_worker_by_the_running_review() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 2);
        let rescued = Arc::new(AtomicBool::new(false));
        let handle = __rt__async_create(
            Box::into_raw(Box::new(RescueFrame {
                rescued: Arc::clone(&rescued),
                polls: 0,
            })) as *mut u8,
            rescue_poll as *const () as *const u8,
            rescue_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );
        scheduler.add_task(
            handle,
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            Some(0),
            false,
        );
        // This thread is worker 0. Its first poll leaves the task on its yield queue
        // before anyone else is running; then it never returns to that queue.
        let local = scheduler.take_local_worker(0);
        WORKER_CONTEXT.with(|cell| {
            *cell.borrow_mut() = Some(WorkerContext {
                scheduler: Arc::clone(&scheduler),
                worker_id: 0,
                current_task: None,
                current_wait_reason: None,
                current_cancellation: None,
            });
        });
        let context = WorkerContextGuard;
        let task = scheduler.next_task(0, &local).expect("the task just added");
        scheduler.run_task(0, task);
        drop(context);
        assert_eq!(scheduler.yielded[0].tasks.len(), 1);
        scheduler.local_workers.lock().unwrap()[0] = Some(local);
        let _worker_zero = scheduler.start();
        let deadline = Instant::now() + StdDuration::from_secs(10);
        while !rescued.load(Ordering::Acquire) && Instant::now() < deadline {
            thread::sleep(StdDuration::from_millis(1));
        }
        let was_rescued = rescued.load(Ordering::Acquire);
        scheduler.force_shutdown();
        scheduler.join_background_threads();
        scheduler.teardown_remaining_tasks();
        assert!(was_rescued, "a yielded task stayed behind a stuck worker");
    }

    #[test]
    fn pinned_tasks_stay_on_one_worker() {
        let visits = run_recording_root(TaskMobility::Pinned);
        assert!(visits.values().all(|threads| threads.len() == 1));
    }

    struct PendingFrame {
        polls: Arc<AtomicUsize>,
        drops: Arc<AtomicUsize>,
    }

    unsafe extern "C-unwind" fn pending_poll(frame: *mut u8, _ctx: *mut u8, _out: *mut u8) -> u8 {
        let frame = unsafe { &mut *(frame as *mut PendingFrame) };
        frame.polls.fetch_add(1, Ordering::AcqRel);
        if __rt__executor_is_current_task_cancelled() {
            2
        } else {
            0
        }
    }

    unsafe extern "C-unwind" fn pending_drop(frame: *mut u8) {
        let frame = unsafe { Box::from_raw(frame as *mut PendingFrame) };
        frame.drops.fetch_add(1, Ordering::AcqRel);
    }

    struct ReadyValueFrame {
        value: u32,
    }

    unsafe extern "C-unwind" fn ready_value_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &*(frame as *mut ReadyValueFrame) };
        if !out.is_null() {
            unsafe { (out as *mut u32).write(frame.value) };
        }
        1
    }

    unsafe extern "C-unwind" fn ready_value_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut ReadyValueFrame) };
    }

    struct DelayedValueFrame {
        value: u32,
        remaining: usize,
        drops: Arc<AtomicUsize>,
    }

    unsafe extern "C-unwind" fn delayed_value_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *(frame as *mut DelayedValueFrame) };
        if frame.remaining > 0 {
            frame.remaining -= 1;
            return 0;
        }
        if !out.is_null() {
            unsafe { (out as *mut u32).write(frame.value) };
        }
        1
    }

    unsafe extern "C-unwind" fn delayed_value_drop(frame: *mut u8) {
        let frame = unsafe { Box::from_raw(frame as *mut DelayedValueFrame) };
        frame.drops.fetch_add(1, Ordering::AcqRel);
    }

    struct PanicFrame {
        message: String,
    }

    unsafe extern "C-unwind" fn panic_task_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        _out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &*(frame as *mut PanicFrame) };
        crate::panic_unwind::rethrow_panic_message(frame.message.clone())
    }

    unsafe extern "C-unwind" fn panic_task_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut PanicFrame) };
    }

    fn make_pending_handle(polls: Arc<AtomicUsize>, drops: Arc<AtomicUsize>) -> *mut u8 {
        __rt__async_create(
            Box::into_raw(Box::new(PendingFrame { polls, drops })) as *mut u8,
            pending_poll as *const () as *const u8,
            pending_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        )
    }

    fn make_ready_value_handle(value: u32) -> *mut u8 {
        __rt__async_create(
            Box::into_raw(Box::new(ReadyValueFrame { value })) as *mut u8,
            ready_value_poll as *const () as *const u8,
            ready_value_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        )
    }

    fn make_delayed_value_handle(value: u32, remaining: usize, drops: Arc<AtomicUsize>) -> *mut u8 {
        __rt__async_create(
            Box::into_raw(Box::new(DelayedValueFrame {
                value,
                remaining,
                drops,
            })) as *mut u8,
            delayed_value_poll as *const () as *const u8,
            delayed_value_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        )
    }

    fn make_panic_handle(message: &str) -> *mut u8 {
        __rt__async_create(
            Box::into_raw(Box::new(PanicFrame {
                message: message.to_string(),
            })) as *mut u8,
            panic_task_poll as *const () as *const u8,
            panic_task_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        )
    }

    #[test]
    fn rootless_abort_drops_pending_spawned_handles() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        assert!(session_cell().lock().unwrap().is_none());

        let polls = Arc::new(AtomicUsize::new(0));
        let drops = Arc::new(AtomicUsize::new(0));
        let _token = spawn_test_task(
            make_pending_handle(Arc::clone(&polls), Arc::clone(&drops)),
            0,
        );

        assert_eq!(polls.load(Ordering::Acquire), 0);
        assert_eq!(drops.load(Ordering::Acquire), 0);

        __rt__executor_abort_rootless();

        assert_eq!(polls.load(Ordering::Acquire), 0);
        assert_eq!(drops.load(Ordering::Acquire), 1);
        assert!(session_cell().lock().unwrap().is_none());
    }

    #[test]
    fn cancel_marks_blocked_task_and_wakes_it() {
        let scheduler = Scheduler::new(false, 1);
        let token = scheduler.add_task(
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            None,
            false,
        );
        let (task_index, _) = unpack_task_token(token);
        let slot = scheduler.lookup_task_slot(task_index).unwrap();
        {
            let mut inner = slot.inner.lock().unwrap();
            inner.queued = false;
        }

        scheduler.cancel_task(token);

        let inner = slot.inner.lock().unwrap();
        assert!(inner.cancelled.load(Ordering::Acquire));
        assert!(inner.queued);
    }

    #[test]
    fn current_cancellation_cache_avoids_task_table_and_observes_cancel() {
        let scheduler = Scheduler::new(false, 1);
        let token = scheduler.add_task(
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            None,
            false,
        );
        let (index, _) = unpack_task_token(token);
        let slot = scheduler.lookup_task_slot(index).unwrap();
        let flag = slot.inner.lock().unwrap().cancelled.clone();
        for expected in [false, true] {
            if expected {
                scheduler.cancel_task(token);
            }
            let (send, receive) = std::sync::mpsc::channel();
            let home = scheduler.clone();
            let cancellation = flag.clone();
            // A nested poll must not reacquire either scheduler lock. Bound
            // failure so a regression reports an error rather than hanging.
            let table = scheduler.tasks.write().unwrap();
            let state = slot.inner.lock().unwrap();
            let query = thread::spawn(move || {
                WORKER_CONTEXT.with(|cell| {
                    cell.replace(Some(WorkerContext {
                        scheduler: home,
                        worker_id: 0,
                        current_task: Some(token),
                        current_cancellation: Some(cancellation),
                        current_wait_reason: None,
                    }));
                });
                let _guard = WorkerContextGuard;
                send.send(__rt__executor_is_current_task_cancelled())
                    .unwrap();
            });
            let observed = receive.recv_timeout(StdDuration::from_secs(1));
            drop(state);
            drop(table);
            query.join().unwrap();
            assert_eq!(observed.unwrap(), expected);
        }
    }

    #[test]
    fn child_list_keeps_each_child_in_arrival_order() {
        let mut children = ChildList::default();
        assert!(children.is_empty());
        for child in [7, 8, 9] {
            children.push(child);
        }
        assert_eq!(children.len(), 3);
        children.remove(7);
        assert_eq!(children.iter().collect::<Vec<_>>(), vec![8, 9]);
        children.remove(9);
        assert_eq!(children.iter().collect::<Vec<_>>(), vec![8]);
        children.remove(42);
        assert_eq!(children.len(), 1);
        children.remove(8);
        assert!(children.is_empty());
    }

    #[test]
    fn task_slot_index_finds_every_published_slot_across_chunk_boundaries() {
        let index = TaskSlotIndex::new();
        let slots: Vec<Arc<TaskSlot>> = (0..1_000)
            .map(|_| {
                Arc::new(TaskSlot::new(
                    TASK_INITIAL_GENERATION,
                    ptr::null_mut(),
                    ptr::null_mut(),
                    None,
                    0,
                    TaskMobility::Movable,
                ))
            })
            .collect();
        for (position, slot) in slots.iter().enumerate() {
            assert_eq!(index.get(position), None);
            index.publish(position, Arc::as_ptr(slot));
            assert_eq!(index.get(position), Some(Arc::as_ptr(slot)));
        }
        for (position, slot) in slots.iter().enumerate() {
            assert_eq!(index.get(position), Some(Arc::as_ptr(slot)));
        }
        assert_eq!(
            index.get(usize::MAX - (1 << TaskSlotIndex::FIRST_CHUNK_BITS)),
            None
        );
    }

    #[test]
    fn cancel_completed_task_is_noop() {
        let scheduler = Scheduler::new(false, 1);
        let token = scheduler.add_task(
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            None,
            false,
        );
        scheduler.complete_task(token);

        scheduler.cancel_task(token);

        let (task_index, _) = unpack_task_token(token);
        let slot = scheduler.lookup_task_slot(task_index).unwrap();
        let inner = slot.inner.lock().unwrap();
        assert!(inner.completed);
        assert!(!inner.cancelled.load(Ordering::Acquire));
    }

    #[test]
    fn cancelled_task_skips_poll_and_runs_drop() {
        let scheduler = Scheduler::new(false, 1);
        let polls = Arc::new(AtomicUsize::new(0));
        let drops = Arc::new(AtomicUsize::new(0));
        let token = scheduler.add_task(
            make_pending_handle(Arc::clone(&polls), Arc::clone(&drops)),
            ptr::null_mut(),
            None,
            0,
            Some(0),
            false,
        );

        scheduler.cancel_task(token);
        scheduler.run_task(0, token);

        assert_eq!(polls.load(Ordering::Acquire), 0);
        assert_eq!(drops.load(Ordering::Acquire), 1);
    }

    #[test]
    fn cancelled_pending_native_request_is_not_published_or_freed() {
        let scheduler = Scheduler::new(false, 1);
        let polls = Arc::new(AtomicUsize::new(0));
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = make_pending_handle(polls.clone(), drops.clone());
        let completion = unsafe { crate::task::register_native_request(handle) };
        let token = scheduler.add_task(handle, ptr::null_mut(), None, 0, Some(0), false);
        WORKER_CONTEXT.with(|cell| {
            cell.replace(Some(WorkerContext {
                scheduler: Arc::clone(&scheduler),
                worker_id: 0,
                current_task: None,
                current_wait_reason: None,
                current_cancellation: None,
            }))
        });
        let _context = WorkerContextGuard;
        scheduler.run_task(0, token);
        scheduler.cancel_task(token);
        scheduler.run_task(0, token);
        let (index, _) = unpack_task_token(token);
        let slot = scheduler.lookup_task_slot(index).unwrap();
        {
            let inner = slot.inner.lock().unwrap();
            assert!(!inner.completed);
            assert!(!inner.queued, "native wait must not busy-requeue");
            assert_eq!(inner.wait_reason, Some(WaitReason::NativeRequest));
        }
        assert_eq!(drops.load(Ordering::Acquire), 0);
        assert_eq!(polls.load(Ordering::Acquire), 0, "cold body must not run");
        assert!(completion.is_cancelled());
        completion.finish();
        scheduler.run_task(0, token);
        assert!(slot.inner.lock().unwrap().completed);
        assert_eq!(drops.load(Ordering::Acquire), 1);
        assert_eq!(polls.load(Ordering::Acquire), 0);
    }

    struct CancelPanicFrame {
        drops: Arc<AtomicUsize>,
    }

    unsafe extern "C-unwind" fn cancel_panic_poll(_: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
        if __rt__executor_is_current_task_cancelled() {
            2
        } else {
            0
        }
    }

    unsafe extern "C-unwind" fn cancel_panic_drop(frame: *mut u8) {
        let frame = unsafe { Box::from_raw(frame.cast::<CancelPanicFrame>()) };
        frame.drops.fetch_add(1, Ordering::SeqCst);
        drop(frame);
        let message = b"cancellation capture cleanup panic";
        crate::panic_unwind::__rt__panic_unwind(crate::panic_unwind::RtString {
            ptr: message.as_ptr(),
            len: message.len(),
        });
    }

    #[test]
    fn cancellation_capture_cleanup_panic_becomes_task_failure() {
        for before_first_poll in [true, false] {
            let scheduler = Scheduler::new(false, 1);
            let drops = Arc::new(AtomicUsize::new(0));
            let handle = __rt__async_create(
                Box::into_raw(Box::new(CancelPanicFrame {
                    drops: Arc::clone(&drops),
                }))
                .cast(),
                cancel_panic_poll as *const () as *const u8,
                cancel_panic_drop as *const () as *const u8,
                TaskMobility::Movable as u8,
            );
            let token = scheduler.add_task(
                handle,
                ptr::null_mut(),
                Some(TaskOutput::empty()),
                0,
                Some(0),
                true,
            );
            WORKER_CONTEXT.with(|cell| {
                cell.replace(Some(WorkerContext {
                    scheduler: Arc::clone(&scheduler),
                    worker_id: 0,
                    current_task: None,
                    current_wait_reason: None,
                    current_cancellation: None,
                }))
            });
            let _context = WorkerContextGuard;
            if !before_first_poll {
                scheduler.run_task(0, token);
            }
            scheduler.cancel_task(token);
            let outcome =
                crate::panic_unwind::catch_executor_panic(|| scheduler.run_task(0, token));
            let (index, _) = unpack_task_token(token);
            let (completed, report) = {
                let slot = scheduler.lookup_task_slot(index).unwrap();
                let inner = slot.inner.lock().unwrap();
                (
                    inner.completed,
                    inner.panic_info.as_ref().map(|r| r.message.clone()),
                )
            };
            assert!(
                outcome.is_ok(),
                "a first cleanup panic escaped task isolation"
            );
            assert!(completed);
            assert_eq!(
                report.as_deref(),
                Some("cancellation capture cleanup panic")
            );
            assert_eq!(drops.load(Ordering::SeqCst), 1);
            assert!(
                current_task_token().is_none(),
                "panic cleanup leaked task identity"
            );
        }
    }

    struct CleanupIdentityFrame {
        mutex: *mut u8,
        locked: bool,
        observed_task: Arc<AtomicU64>,
        observed_cancelled: Arc<AtomicBool>,
        unlock_status: Arc<std::sync::atomic::AtomicI32>,
    }

    unsafe extern "C-unwind" fn cleanup_identity_poll(
        frame: *mut u8,
        _: *mut u8,
        _: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *frame.cast::<CleanupIdentityFrame>() };
        if !frame.locked {
            assert_eq!(crate::sync::__rt__sync_mutex_try_lock(frame.mutex), 0);
            frame.locked = true;
        }
        if __rt__executor_is_current_task_cancelled() {
            2
        } else {
            0
        }
    }

    unsafe extern "C-unwind" fn cleanup_identity_drop(frame: *mut u8) {
        let frame = unsafe { Box::from_raw(frame.cast::<CleanupIdentityFrame>()) };
        frame
            .observed_task
            .store(current_task_token().unwrap_or(0), Ordering::Release);
        frame.observed_cancelled.store(
            __rt__executor_is_current_task_cancelled(),
            Ordering::Release,
        );
        if !frame.locked {
            // Before-first-poll cancellation must also provide task identity.
            let status = crate::sync::__rt__sync_mutex_try_lock(frame.mutex);
            if status != 0 {
                frame.unlock_status.store(status, Ordering::Release);
                return;
            }
        }
        frame.unlock_status.store(
            crate::sync::__rt__sync_mutex_unlock(frame.mutex),
            Ordering::Release,
        );
    }

    #[test]
    fn cancellation_cleanup_preserves_task_identity_until_frame_destruction() {
        for before_first_poll in [true, false] {
            let scheduler = Scheduler::new(false, 1);
            let mutex = crate::sync::__rt__sync_mutex_create();
            let observed_task = Arc::new(AtomicU64::new(0));
            let observed_cancelled = Arc::new(AtomicBool::new(false));
            let unlock_status = Arc::new(std::sync::atomic::AtomicI32::new(-1));
            let handle = __rt__async_create(
                Box::into_raw(Box::new(CleanupIdentityFrame {
                    mutex,
                    locked: false,
                    observed_task: Arc::clone(&observed_task),
                    observed_cancelled: Arc::clone(&observed_cancelled),
                    unlock_status: Arc::clone(&unlock_status),
                }))
                .cast(),
                cleanup_identity_poll as *const () as *const u8,
                cleanup_identity_drop as *const () as *const u8,
                TaskMobility::Movable as u8,
            );
            let token = scheduler.add_task(
                handle,
                ptr::null_mut(),
                Some(TaskOutput::empty()),
                0,
                Some(0),
                true,
            );
            WORKER_CONTEXT.with(|cell| {
                cell.replace(Some(WorkerContext {
                    scheduler: Arc::clone(&scheduler),
                    worker_id: 0,
                    current_task: None,
                    current_wait_reason: None,
                    current_cancellation: None,
                }))
            });
            let _context = WorkerContextGuard;
            if !before_first_poll {
                scheduler.run_task(0, token);
            }
            scheduler.cancel_task(token);
            scheduler.run_task(0, token);
            let seen_task = observed_task.load(Ordering::Acquire);
            let seen_cancelled = observed_cancelled.load(Ordering::Acquire);
            let status = unlock_status.load(Ordering::Acquire);
            // Finish fixture ownership before asserting the recorded behavior.
            assert_eq!(crate::sync::__rt__sync_mutex_destroy(mutex), 0);
            unsafe { crate::sync::__rt__sync_handle_release(mutex) };
            assert!(
                current_task_token().is_none(),
                "cleanup identity escaped into the worker"
            );
            assert_eq!(seen_task, token, "frame cleanup lost its owning task");
            assert!(seen_cancelled, "cleanup did not observe cancellation");
            assert_eq!(status, 0, "cleanup could not release its task-owned mutex");
        }
    }

    struct TimerMutexChildFrame {
        mutex_handle: *mut u8,
        armed: bool,
        ready: mpsc::Sender<()>,
        done: mpsc::Sender<()>,
        drops: Arc<AtomicUsize>,
    }

    unsafe extern "C-unwind" fn timer_mutex_child_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        _out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *(frame as *mut TimerMutexChildFrame) };
        if __rt__executor_is_current_task_cancelled() {
            return 2;
        }
        if !frame.armed {
            assert_eq!(
                crate::sync::__rt__sync_mutex_try_lock(frame.mutex_handle),
                0
            );
            register_sleep(Instant::now() + StdDuration::from_secs(30));
            frame.armed = true;
            let _ = frame.ready.send(());
        }
        0
    }

    unsafe extern "C-unwind" fn timer_mutex_child_drop(frame: *mut u8) {
        let frame = unsafe { Box::from_raw(frame as *mut TimerMutexChildFrame) };
        frame.drops.fetch_add(1, Ordering::AcqRel);
        let _ = frame.done.send(());
    }

    #[test]
    fn task_cancellation_cleans_timer_and_sync_state() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 1);
        let mutex_handle = crate::sync::__rt__sync_mutex_create();
        // This native fixture owns the opaque box directly. The task's lock
        // lease protects registry state; no collector owns the handle box.
        struct Root(*mut u8);
        impl Drop for Root {
            fn drop(&mut self) {
                unsafe { crate::sync::__rt__sync_handle_release(self.0) };
            }
        }
        struct Parked;
        impl Parked {
            fn new() -> Self {
                Self
            }
        }
        impl Drop for Parked {
            fn drop(&mut self) {}
        }
        let _root = Root(mutex_handle);
        let (ready_sender, child_ready) = mpsc::channel();
        let (done_sender, child_done) = mpsc::channel();
        let child_drops = Arc::new(AtomicUsize::new(0));
        let handle = __rt__async_create(
            Box::into_raw(Box::new(TimerMutexChildFrame {
                mutex_handle,
                armed: false,
                ready: ready_sender,
                done: done_sender,
                drops: Arc::clone(&child_drops),
            })) as *mut u8,
            timer_mutex_child_poll as *const () as *const u8,
            timer_mutex_child_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );
        let token = scheduler.add_task(handle, ptr::null_mut(), None, 0, Some(0), false);
        let (task_index, _) = unpack_task_token(token);

        let local = scheduler.start();
        let worker_scheduler = Arc::clone(&scheduler);
        let worker = thread::Builder::new()
            .name("taro-test-cancel-cleanup-worker".into())
            .spawn(move || worker_scheduler.worker_loop(0, local))
            .expect("failed to spawn cancellation cleanup worker");

        let parked = Parked::new();
        child_ready
            .recv_timeout(StdDuration::from_secs(5))
            .expect("child task never reached timer/mutex blocked state");
        assert!(
            scheduler.timers.lock().unwrap().latest[task_index].is_some(),
            "child task should have registered a timer before cancellation"
        );

        scheduler.cancel_task(token);
        child_done
            .recv_timeout(StdDuration::from_secs(5))
            .expect("cancelled child did not finish cleanup");
        // Frame destruction now precedes publishing terminal task state. Its
        // done signal proves destruction, not timer/ownership finalization.
        // The last task shuts this worker down; joining proves both finished.
        worker
            .join()
            .expect("cancellation cleanup worker join failed");
        scheduler.join_background_threads();
        assert_eq!(child_drops.load(Ordering::Acquire), 1);
        assert!(
            scheduler.timers.lock().unwrap().latest[task_index].is_none(),
            "cancelled task timer should be cleared during finalization"
        );
        drop(parked); // Resume before accessing the native mutex handle.
        assert_eq!(
            crate::sync::__rt__sync_mutex_destroy(mutex_handle),
            0,
            "cancelled task should release owned mutex"
        );
    }

    mod reading_the_reactor {
        use super::*;

        const WAIT: StdDuration = StdDuration::from_secs(5);

        enum Then {
            ReadPipe(usize),
            Sleep(StdDuration),
            HandOverWake(mpsc::Sender<TaskWake>),
        }

        /// Waits once as told, then finishes.
        struct WaitOnce {
            then: Then,
            waited: bool,
            armed: mpsc::Sender<()>,
            done: mpsc::Sender<()>,
        }

        unsafe extern "C-unwind" fn wait_once_poll(frame: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
            let frame = unsafe { &mut *(frame as *mut WaitOnce) };
            if frame.waited {
                let _ = frame.done.send(());
                return 1;
            }
            frame.waited = true;
            match &frame.then {
                Then::ReadPipe(source) => register_io_wait(*source, Interest::Read).unwrap(),
                Then::Sleep(duration) => register_sleep(Instant::now() + *duration),
                // The long timer is why it's waiting, as far as the scheduler can tell.
                Then::HandOverWake(wake) => {
                    register_sleep(Instant::now() + StdDuration::from_secs(60));
                    wake.send(current_task_wake()).unwrap();
                }
            }
            let _ = frame.armed.send(());
            0
        }

        unsafe extern "C-unwind" fn wait_once_drop(frame: *mut u8) {
            drop(unsafe { Box::from_raw(frame as *mut WaitOnce) });
        }

        /// Stays runnable, or holds its worker in one long poll, until `until` is set.
        struct Occupy {
            until: Arc<AtomicBool>,
            in_one_poll: bool,
        }

        unsafe extern "C-unwind" fn occupy_poll(frame: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
            let frame = unsafe { &mut *(frame as *mut Occupy) };
            while frame.in_one_poll && !frame.until.load(Ordering::Acquire) {
                std::hint::spin_loop();
            }
            if frame.until.load(Ordering::Acquire) {
                return 1;
            }
            current_task_wake().wake();
            0
        }

        unsafe extern "C-unwind" fn occupy_drop(frame: *mut u8) {
            drop(unsafe { Box::from_raw(frame as *mut Occupy) });
        }

        fn current_task_wake() -> TaskWake {
            WORKER_CONTEXT.with(|cell| {
                let borrow = cell.borrow();
                let context = borrow.as_ref().unwrap();
                TaskWake::new(&context.scheduler, context.current_task.unwrap())
            })
        }

        struct Waiting {
            armed: mpsc::Receiver<()>,
            done: mpsc::Receiver<()>,
        }

        fn add_waiting_task(scheduler: &Arc<Scheduler>, then: Then) -> Waiting {
            let (armed_sender, armed) = mpsc::channel();
            let (done_sender, done) = mpsc::channel();
            let handle = __rt__async_create(
                Box::into_raw(Box::new(WaitOnce {
                    then,
                    waited: false,
                    armed: armed_sender,
                    done: done_sender,
                })) as *mut u8,
                wait_once_poll as *const () as *const u8,
                wait_once_drop as *const () as *const u8,
                TaskMobility::Movable as u8,
            );
            scheduler.add_task(handle, ptr::null_mut(), None, 0, Some(0), false);
            Waiting { armed, done }
        }

        fn add_occupying_task(
            scheduler: &Arc<Scheduler>,
            until: &Arc<AtomicBool>,
            in_one_poll: bool,
        ) {
            let handle = __rt__async_create(
                Box::into_raw(Box::new(Occupy {
                    until: Arc::clone(until),
                    in_one_poll,
                })) as *mut u8,
                occupy_poll as *const () as *const u8,
                occupy_drop as *const () as *const u8,
                if in_one_poll {
                    TaskMobility::Pinned
                } else {
                    TaskMobility::Movable
                } as u8,
            );
            scheduler.add_task(handle, ptr::null_mut(), None, 0, Some(0), false);
        }

        fn run_worker(scheduler: &Arc<Scheduler>) -> thread::JoinHandle<()> {
            let local = scheduler.start();
            let scheduler = Arc::clone(scheduler);
            thread::spawn(move || scheduler.worker_loop(0, local))
        }

        fn wait_for_worker_in_reactor(scheduler: &Scheduler) {
            let deadline = Instant::now() + WAIT;
            while scheduler.reactor_poller.load(Ordering::SeqCst) != POLLER_WORKER
                || !scheduler.worker_idle[GATHERING_WORKER].load(Ordering::SeqCst)
            {
                assert!(Instant::now() < deadline, "worker never slept in the reactor");
                thread::yield_now();
            }
            // A wake left behind by an earlier scheduler returns it from its first read.
            thread::sleep(StdDuration::from_millis(20));
        }

        struct Pipe {
            source: usize,
            write_fd: i32,
        }
        impl Pipe {
            fn new() -> Self {
                let mut fds = [-1_i32; 2];
                assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
                let source = io_poller::adopt_fd(fds[0]);
                assert_ne!(source, 0);
                Self {
                    source,
                    write_fd: fds[1],
                }
            }
            fn make_readable(&self) {
                assert_eq!(unsafe { libc::write(self.write_fd, b"x".as_ptr().cast(), 1) }, 1);
            }
        }
        impl Drop for Pipe {
            fn drop(&mut self) {
                io_poller::__rt__async_io_close_source(self.source);
                unsafe { libc::close(self.write_fd) };
            }
        }

        #[test]
        fn a_lone_worker_sleeps_in_the_reactor_with_no_io_thread() {
            let _guard = TEST_ENV_LOCK.lock().unwrap();
            let scheduler = Scheduler::new(false, 1);
            let pipe = Pipe::new();
            let task = add_waiting_task(&scheduler, Then::ReadPipe(pipe.source));
            let worker = run_worker(&scheduler);
            assert!(scheduler.io_join.lock().unwrap().is_none());
            task.armed.recv_timeout(WAIT).unwrap();
            wait_for_worker_in_reactor(&scheduler);

            pipe.make_readable();
            task.done.recv_timeout(WAIT).expect("readable pipe woke nothing");
            worker.join().unwrap();
            scheduler.join_background_threads();
        }

        #[test]
        fn a_worker_asleep_in_the_reactor_wakes_for_its_next_timer() {
            let _guard = TEST_ENV_LOCK.lock().unwrap();
            let scheduler = Scheduler::new(false, 1);
            let task = add_waiting_task(&scheduler, Then::Sleep(StdDuration::from_millis(20)));
            let worker = run_worker(&scheduler);
            task.done.recv_timeout(WAIT).expect("timer never fired");
            worker.join().unwrap();
            scheduler.join_background_threads();
        }

        #[test]
        fn a_worker_asleep_in_the_reactor_wakes_for_work_from_another_thread() {
            let _guard = TEST_ENV_LOCK.lock().unwrap();
            let scheduler = Scheduler::new(false, 1);
            let (wake_sender, wake) = mpsc::channel();
            let task = add_waiting_task(&scheduler, Then::HandOverWake(wake_sender));
            let worker = run_worker(&scheduler);
            let wake = wake.recv_timeout(WAIT).unwrap();
            task.armed.recv_timeout(WAIT).unwrap();
            wait_for_worker_in_reactor(&scheduler);

            wake.wake();
            task.done.recv_timeout(WAIT).expect("sleeping worker missed a wake");
            worker.join().unwrap();
            scheduler.join_background_threads();
        }

        #[test]
        fn a_worker_whose_queue_never_empties_still_reads_the_reactor() {
            let _guard = TEST_ENV_LOCK.lock().unwrap();
            let scheduler = Scheduler::new(false, 1);
            let pipe = Pipe::new();
            let finished = Arc::new(AtomicBool::new(false));
            let task = add_waiting_task(&scheduler, Then::ReadPipe(pipe.source));
            add_occupying_task(&scheduler, &finished, false);
            let worker = run_worker(&scheduler);
            task.armed.recv_timeout(WAIT).unwrap();

            pipe.make_readable();
            let woken = task.done.recv_timeout(WAIT);
            finished.store(true, Ordering::Release);
            woken.expect("busy worker never read the reactor");
            worker.join().unwrap();
            scheduler.join_background_threads();
        }

        #[test]
        fn a_stuck_worker_leaves_the_reactor_to_the_io_thread() {
            let _guard = TEST_ENV_LOCK.lock().unwrap();
            let scheduler = Scheduler::new(false, 2);
            let pipe = Pipe::new();
            let finished = Arc::new(AtomicBool::new(false));
            let task = add_waiting_task(&scheduler, Then::ReadPipe(pipe.source));
            let worker = run_worker(&scheduler);
            task.armed.recv_timeout(WAIT).unwrap();
            add_occupying_task(&scheduler, &finished, true);
            scheduler.unpark_worker(GATHERING_WORKER);

            // Worker 0 can't read now, and nothing else would until the review notices.
            let deadline = Instant::now() + WAIT;
            while scheduler.gathering.load(Ordering::Relaxed) {
                assert!(Instant::now() < deadline, "the stuck worker went unnoticed");
                thread::yield_now();
            }
            pipe.make_readable();
            let woken = task.done.recv_timeout(WAIT);
            finished.store(true, Ordering::Release);
            woken.expect("nothing read the reactor for a stuck worker");
            worker.join().unwrap();
            scheduler.join_background_threads();
        }

        #[test]
        fn an_idle_worker_takes_the_reactor_back_from_the_io_thread() {
            let _guard = TEST_ENV_LOCK.lock().unwrap();
            let scheduler = Scheduler::new(false, 2);
            scheduler.gathering.store(false, Ordering::Relaxed);
            let pipe = Pipe::new();
            let task = add_waiting_task(&scheduler, Then::ReadPipe(pipe.source));
            let worker = run_worker(&scheduler);
            task.armed.recv_timeout(WAIT).unwrap();

            // The review sees nothing wrong and tasks gather again.
            wait_for_worker_in_reactor(&scheduler);
            pipe.make_readable();
            task.done.recv_timeout(WAIT).expect("nothing read the reactor");
            worker.join().unwrap();
            scheduler.join_background_threads();
        }
    }

    struct PollSpawnedCancelledRoot {
        stage: u8,
        token: u64,
        drops: Arc<AtomicUsize>,
    }

    unsafe extern "C-unwind" fn poll_spawned_cancelled_root_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        _out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *(frame as *mut PollSpawnedCancelledRoot) };
        if frame.stage == 0 {
            let polls = Arc::new(AtomicUsize::new(0));
            frame.token = spawn_test_task(make_pending_handle(polls, Arc::clone(&frame.drops)), 0);
            cancel_task_raw(frame.token);
            frame.stage = 1;
            return 0;
        }

        if poll_test_task(frame.token, std::ptr::null_mut()) == 0 {
            return 0;
        }
        1
    }

    unsafe extern "C-unwind" fn poll_spawned_cancelled_root_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut PollSpawnedCancelledRoot) };
    }

    #[test]
    fn poll_spawned_checked_returns_cancelled_status() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = __rt__async_create(
            Box::into_raw(Box::new(PollSpawnedCancelledRoot {
                stage: 0,
                token: 0,
                drops: Arc::clone(&drops),
            })) as *mut u8,
            poll_spawned_cancelled_root_poll as *const () as *const u8,
            poll_spawned_cancelled_root_drop as *const () as *const u8,
            TaskMobility::Pinned as u8,
        );

        __rt__async_run_root(handle, std::ptr::null_mut());
        assert_eq!(drops.load(Ordering::Acquire), 1);
    }

    struct PollSpawnedCheckedRoot {
        stage: u8,
        token: u64,
        drops: Arc<AtomicUsize>,
    }

    unsafe extern "C-unwind" fn poll_spawned_checked_root_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *(frame as *mut PollSpawnedCheckedRoot) };
        if frame.stage == 0 {
            let polls = Arc::new(AtomicUsize::new(0));
            frame.token = spawn_test_task(
                make_pending_handle(polls, Arc::clone(&frame.drops)),
                std::mem::size_of::<u32>() as u64,
            );
            cancel_task_raw(frame.token);
            frame.stage = 1;
            return 0;
        }

        let mut value = 99_u32;
        let status = poll_test_task(frame.token, (&mut value as *mut u32).cast::<u8>());
        if status == 0 {
            return 0;
        }

        assert_eq!(status, 2);
        assert_eq!(task_completion_status_raw(frame.token), 2);
        if !out.is_null() {
            unsafe { (out as *mut u8).write(status) };
        }
        1
    }

    unsafe extern "C-unwind" fn poll_spawned_checked_root_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut PollSpawnedCheckedRoot) };
    }

    #[test]
    fn checked_poll_reports_cancelled_status() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = __rt__async_create(
            Box::into_raw(Box::new(PollSpawnedCheckedRoot {
                stage: 0,
                token: 0,
                drops: Arc::clone(&drops),
            })) as *mut u8,
            poll_spawned_checked_root_poll as *const () as *const u8,
            poll_spawned_checked_root_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );

        let mut out = 0_u8;
        __rt__async_run_root(handle, (&mut out as *mut u8).cast::<u8>());
        assert_eq!(out, 2);
        assert_eq!(drops.load(Ordering::Acquire), 1);
    }

    struct SelfCancelProbeFrame {
        // Published by the parent after spawn returns; another worker may
        // poll the child before then.
        self_token: AtomicU64,
    }

    unsafe extern "C-unwind" fn self_cancel_probe_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        _out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *(frame as *mut SelfCancelProbeFrame) };
        assert!(
            !__rt__executor_is_current_task_cancelled(),
            "task should not start out cancelled"
        );
        let token = loop {
            match frame.self_token.load(Ordering::Acquire) {
                0 => std::thread::yield_now(),
                token => break token,
            }
        };
        cancel_task_raw(token);
        assert!(
            __rt__executor_is_current_task_cancelled(),
            "task should observe cancellation immediately after self-cancel"
        );
        2 // this authored callback observed cancellation and acknowledges it
    }

    unsafe extern "C-unwind" fn self_cancel_probe_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut SelfCancelProbeFrame) };
    }

    struct SelfCancelProbeRoot {
        stage: u8,
        token: u64,
        child_frame: *mut SelfCancelProbeFrame,
    }

    unsafe extern "C-unwind" fn self_cancel_probe_root_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        _out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *(frame as *mut SelfCancelProbeRoot) };
        if frame.stage == 0 {
            frame.child_frame = Box::into_raw(Box::new(SelfCancelProbeFrame {
                self_token: AtomicU64::new(0),
            }));
            let handle = __rt__async_create(
                frame.child_frame as *mut u8,
                self_cancel_probe_poll as *const () as *const u8,
                self_cancel_probe_drop as *const () as *const u8,
                TaskMobility::Movable as u8,
            );
            frame.token = spawn_test_task(handle, 0);
            unsafe {
                (*frame.child_frame)
                    .self_token
                    .store(frame.token, Ordering::Release)
            };
            frame.stage = 1;
            return 0;
        }

        let status = poll_test_task(frame.token, std::ptr::null_mut());
        if status == 0 {
            return 0;
        }
        assert_eq!(status, 2);
        assert_eq!(task_completion_status_raw(frame.token), 2);
        1
    }

    unsafe extern "C-unwind" fn self_cancel_probe_root_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut SelfCancelProbeRoot) };
    }

    #[test]
    fn current_task_cancellation_is_observable_after_self_cancel() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let handle = __rt__async_create(
            Box::into_raw(Box::new(SelfCancelProbeRoot {
                stage: 0,
                token: 0,
                child_frame: std::ptr::null_mut(),
            })) as *mut u8,
            self_cancel_probe_root_poll as *const () as *const u8,
            self_cancel_probe_root_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );

        __rt__async_run_root(handle, std::ptr::null_mut());
    }

    struct GroupCollectRoot {
        stage: u8,
        group_id: u64,
        sum: u32,
    }

    unsafe extern "C-unwind" fn group_collect_root_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *(frame as *mut GroupCollectRoot) };
        if frame.stage == 0 {
            frame.group_id = __rt__task_group_create(std::mem::size_of::<u32>() as u64, 1);
            let _ = spawn_test_group_task(frame.group_id, make_ready_value_handle(11), 4);
            let _ = spawn_test_group_task(frame.group_id, make_ready_value_handle(31), 4);
            __rt__task_group_close(frame.group_id);
            frame.stage = 1;
            return 0;
        }

        let mut value = 0_u32;
        match __rt__task_group_poll_next(frame.group_id, (&mut value as *mut u32).cast::<u8>()) {
            0 => 0,
            1 => {
                assert_eq!(__rt__task_group_next_status(frame.group_id), 1);
                frame.sum += value;
                0
            }
            2 => {
                assert_eq!(__rt__task_group_next_status(frame.group_id), 2);
                __rt__task_group_destroy(frame.group_id);
                if !out.is_null() {
                    unsafe { (out as *mut u32).write(frame.sum) };
                }
                1
            }
            _ => unreachable!(),
        }
    }

    unsafe extern "C-unwind" fn group_collect_root_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut GroupCollectRoot) };
    }

    #[test]
    fn task_group_lifecycle_collects_results() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let handle = __rt__async_create(
            Box::into_raw(Box::new(GroupCollectRoot {
                stage: 0,
                group_id: 0,
                sum: 0,
            })) as *mut u8,
            group_collect_root_poll as *const () as *const u8,
            group_collect_root_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );

        let mut out = 0_u32;
        __rt__async_run_root(handle, (&mut out as *mut u32).cast::<u8>());
        assert_eq!(out, 42);
    }

    struct GroupCancelAllRoot {
        stage: u8,
        group_id: u64,
        drops: Arc<AtomicUsize>,
    }

    unsafe extern "C-unwind" fn group_cancel_all_root_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *(frame as *mut GroupCancelAllRoot) };
        if frame.stage == 0 {
            let polls_a = Arc::new(AtomicUsize::new(0));
            let polls_b = Arc::new(AtomicUsize::new(0));
            frame.group_id = __rt__task_group_create(std::mem::size_of::<u32>() as u64, 1);
            let _ = spawn_test_group_task(
                frame.group_id,
                make_pending_handle(polls_a, Arc::clone(&frame.drops)),
                4,
            );
            let _ = spawn_test_group_task(
                frame.group_id,
                make_pending_handle(polls_b, Arc::clone(&frame.drops)),
                4,
            );
            __rt__task_group_close(frame.group_id);
            __rt__task_group_cancel_all(frame.group_id);
            frame.stage = 1;
            return 0;
        }

        let mut scratch = 0_u32;
        match __rt__task_group_poll_next(frame.group_id, (&mut scratch as *mut u32).cast::<u8>()) {
            0 => 0,
            1 => panic!("cancelled group should not yield successful results"),
            2 => {
                __rt__task_group_destroy(frame.group_id);
                if !out.is_null() {
                    unsafe { (out as *mut u8).write(1) };
                }
                1
            }
            _ => unreachable!(),
        }
    }

    unsafe extern "C-unwind" fn group_cancel_all_root_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut GroupCancelAllRoot) };
    }

    #[test]
    fn task_group_cancel_all_cancels_remaining_tasks() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = __rt__async_create(
            Box::into_raw(Box::new(GroupCancelAllRoot {
                stage: 0,
                group_id: 0,
                drops: Arc::clone(&drops),
            })) as *mut u8,
            group_cancel_all_root_poll as *const () as *const u8,
            group_cancel_all_root_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );

        let mut out = 0_u8;
        __rt__async_run_root(handle, (&mut out as *mut u8).cast::<u8>());
        assert_eq!(out, 1);
        assert_eq!(drops.load(Ordering::Acquire), 2);
    }

    struct GroupCancelOnPanicRoot {
        stage: u8,
        group_id: u64,
        drops: Arc<AtomicUsize>,
    }

    unsafe extern "C-unwind" fn group_cancel_on_panic_root_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *(frame as *mut GroupCancelOnPanicRoot) };
        if frame.stage == 0 {
            let polls = Arc::new(AtomicUsize::new(0));
            frame.group_id = __rt__task_group_create(std::mem::size_of::<u32>() as u64, 1);
            let _ =
                spawn_test_group_task(frame.group_id, make_panic_handle("group child panic"), 4);
            let _ = spawn_test_group_task(
                frame.group_id,
                make_pending_handle(polls, Arc::clone(&frame.drops)),
                4,
            );
            __rt__task_group_close(frame.group_id);
            frame.stage = 1;
            return 0;
        }

        let mut scratch = 0_u32;
        match __rt__task_group_poll_next(frame.group_id, (&mut scratch as *mut u32).cast::<u8>()) {
            0 => 0,
            1 => panic!("cancel-on-panic group should not yield successful results"),
            2 => {
                __rt__task_group_destroy(frame.group_id);
                if !out.is_null() {
                    unsafe { (out as *mut u8).write(1) };
                }
                1
            }
            _ => unreachable!(),
        }
    }

    unsafe extern "C-unwind" fn group_cancel_on_panic_root_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut GroupCancelOnPanicRoot) };
    }

    #[test]
    fn task_group_cancel_on_panic_cancels_siblings() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = __rt__async_create(
            Box::into_raw(Box::new(GroupCancelOnPanicRoot {
                stage: 0,
                group_id: 0,
                drops: Arc::clone(&drops),
            })) as *mut u8,
            group_cancel_on_panic_root_poll as *const () as *const u8,
            group_cancel_on_panic_root_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );

        let mut out = 0_u8;
        __rt__async_run_root(handle, (&mut out as *mut u8).cast::<u8>());
        assert_eq!(out, 1);
        assert_eq!(drops.load(Ordering::Acquire), 1);
    }

    struct GroupCancelOnPanicOpenRoot {
        stage: u8,
        group_id: u64,
        drops: Arc<AtomicUsize>,
    }

    unsafe extern "C-unwind" fn group_cancel_on_panic_open_root_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *(frame as *mut GroupCancelOnPanicOpenRoot) };
        if frame.stage == 0 {
            let polls = Arc::new(AtomicUsize::new(0));
            frame.group_id = __rt__task_group_create(std::mem::size_of::<u32>() as u64, 1);
            let _ =
                spawn_test_group_task(frame.group_id, make_panic_handle("group child panic"), 4);
            let _ = spawn_test_group_task(
                frame.group_id,
                make_pending_handle(polls, Arc::clone(&frame.drops)),
                4,
            );
            frame.stage = 1;
            return 0;
        }

        let mut scratch = 0_u32;
        match __rt__task_group_poll_next(frame.group_id, (&mut scratch as *mut u32).cast::<u8>()) {
            0 => 0,
            1 => panic!("cancel-on-panic group should not yield successful results"),
            2 => {
                __rt__task_group_destroy(frame.group_id);
                if !out.is_null() {
                    unsafe { (out as *mut u8).write(1) };
                }
                1
            }
            _ => unreachable!(),
        }
    }

    unsafe extern "C-unwind" fn group_cancel_on_panic_open_root_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut GroupCancelOnPanicOpenRoot) };
    }

    #[test]
    fn task_group_cancel_on_panic_closes_group_for_waiters() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = __rt__async_create(
            Box::into_raw(Box::new(GroupCancelOnPanicOpenRoot {
                stage: 0,
                group_id: 0,
                drops: Arc::clone(&drops),
            })) as *mut u8,
            group_cancel_on_panic_open_root_poll as *const () as *const u8,
            group_cancel_on_panic_open_root_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );

        let mut out = 0_u8;
        __rt__async_run_root(handle, (&mut out as *mut u8).cast::<u8>());
        assert_eq!(out, 1);
        assert_eq!(drops.load(Ordering::Acquire), 1);
    }

    struct GroupIndependentRoot {
        stage: u8,
        group_id: u64,
        sum: u32,
        drops: Arc<AtomicUsize>,
    }

    unsafe extern "C-unwind" fn group_independent_root_poll(
        frame: *mut u8,
        _ctx: *mut u8,
        out: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *(frame as *mut GroupIndependentRoot) };
        if frame.stage == 0 {
            frame.group_id = __rt__task_group_create(std::mem::size_of::<u32>() as u64, 0);
            let _ =
                spawn_test_group_task(frame.group_id, make_panic_handle("group child panic"), 4);
            let _ = spawn_test_group_task(
                frame.group_id,
                make_delayed_value_handle(7, 1, Arc::clone(&frame.drops)),
                4,
            );
            __rt__task_group_close(frame.group_id);
            frame.stage = 1;
            return 0;
        }

        let mut value = 0_u32;
        match __rt__task_group_poll_next(frame.group_id, (&mut value as *mut u32).cast::<u8>()) {
            0 => 0,
            1 => {
                frame.sum += value;
                0
            }
            2 => {
                __rt__task_group_destroy(frame.group_id);
                if !out.is_null() {
                    unsafe { (out as *mut u32).write(frame.sum) };
                }
                1
            }
            _ => unreachable!(),
        }
    }

    unsafe extern "C-unwind" fn group_independent_root_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut GroupIndependentRoot) };
    }

    #[test]
    fn task_group_independent_keeps_siblings_running_after_panic() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = __rt__async_create(
            Box::into_raw(Box::new(GroupIndependentRoot {
                stage: 0,
                group_id: 0,
                sum: 0,
                drops: Arc::clone(&drops),
            })) as *mut u8,
            group_independent_root_poll as *const () as *const u8,
            group_independent_root_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );

        let mut out = 0_u32;
        __rt__async_run_root(handle, (&mut out as *mut u32).cast::<u8>());
        assert_eq!(out, 7);
        assert_eq!(drops.load(Ordering::Acquire), 1);
    }

    #[test]
    fn cancellation_and_duplicate_queue_claims_cannot_poll_or_drop_a_running_frame() {
        use std::sync::mpsc;
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        struct Frame {
            entered: mpsc::Sender<()>,
            release: mpsc::Receiver<()>,
            active: Arc<AtomicBool>,
            polls: Arc<AtomicUsize>,
            drops: Arc<AtomicUsize>,
        }
        unsafe extern "C-unwind" fn poll(frame: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
            let frame = unsafe { &mut *frame.cast::<Frame>() };
            assert!(
                !frame.active.swap(true, Ordering::AcqRel),
                "simultaneous poll"
            );
            frame.polls.fetch_add(1, Ordering::AcqRel);
            frame.entered.send(()).unwrap();
            let released = frame.release.recv();
            frame.active.store(false, Ordering::Release);
            released.unwrap();
            1
        }
        unsafe extern "C-unwind" fn drop_frame(frame: *mut u8) {
            let frame = unsafe { Box::from_raw(frame.cast::<Frame>()) };
            assert!(
                !frame.active.load(Ordering::Acquire),
                "drop raced a live poll"
            );
            frame.drops.fetch_add(1, Ordering::AcqRel);
        }
        let (entered, entered_rx) = mpsc::channel();
        let (release, release_rx) = mpsc::channel();
        let active = Arc::new(AtomicBool::new(false));
        let polls = Arc::new(AtomicUsize::new(0));
        let drops = Arc::new(AtomicUsize::new(0));
        let frame = Box::into_raw(Box::new(Frame {
            entered,
            release: release_rx,
            active: active.clone(),
            polls: polls.clone(),
            drops: drops.clone(),
        }));
        let handle = __rt__async_create(
            frame.cast(),
            poll as *const () as *const u8,
            drop_frame as *const () as *const u8,
            TaskMobility::Movable as u8,
        );
        let scheduler = Scheduler::new(false, 2);
        let token = scheduler.add_task(handle, std::ptr::null_mut(), None, 0, None, true);
        let worker_scheduler = scheduler.clone();
        let worker = std::thread::spawn(move || {
            let _runtime_guard = WorkerRuntimeGuard;
            WORKER_CONTEXT.with(|cell| {
                *cell.borrow_mut() = Some(WorkerContext {
                    scheduler: worker_scheduler.clone(),
                    worker_id: 0,
                    current_task: None,
                    current_wait_reason: None,
                    current_cancellation: None,
                })
            });
            let _context_guard = WorkerContextGuard;
            worker_scheduler.run_task(0, token);
        });
        entered_rx.recv_timeout(StdDuration::from_secs(5)).unwrap();
        scheduler.cancel_task(token);
        scheduler.schedule_task(token, Some(1));
        scheduler.run_task(1, token); // must lose the claim before entering poll
        assert!(active.load(Ordering::Acquire));
        assert_eq!(polls.load(Ordering::Acquire), 1);
        assert_eq!(drops.load(Ordering::Acquire), 0);
        release.send(()).unwrap();
        worker.join().unwrap();
        assert!(!active.load(Ordering::Acquire));
        assert_eq!(polls.load(Ordering::Acquire), 1);
        assert_eq!(drops.load(Ordering::Acquire), 1);
    }
}

#[cfg(test)]
mod task_handle_tests;
