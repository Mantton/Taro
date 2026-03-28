use crossbeam_deque::{Injector, Steal, Stealer, Worker};
use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, VecDeque};
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::thread::{self, JoinHandle, Thread};
use std::time::{Duration as StdDuration, Instant};

use crate::garbage_collector::with_gc;
use crate::io_poller::{self, Interest};
use crate::task::{
    __rt__async_destroy, __rt__async_poll, TaskMobility, async_handle_frame, async_handle_mobility,
};

type TaskId = usize;

const IDLE_SPINS: usize = 32;
const IDLE_YIELDS: usize = 8;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct TimerEntry {
    deadline: Instant,
    sequence: u64,
    task_id: TaskId,
}

struct TaskSlot {
    inner: Mutex<TaskSlotInner>,
}

struct TaskSlotInner {
    handle: *mut u8,
    frame: *mut u8,
    out_ptr: *mut u8,
    out_buf: Option<Vec<u8>>,
    completed: bool,
    queued: bool,
    running: bool,
    wake_requested: bool,
    waiters: Vec<TaskId>,
    owner_worker: usize,
    last_worker: usize,
    mobility: TaskMobility,
}

unsafe impl Send for TaskSlot {}
unsafe impl Sync for TaskSlot {}

impl TaskSlot {
    fn new(
        handle: *mut u8,
        out_ptr: *mut u8,
        out_buf: Option<Vec<u8>>,
        owner_worker: usize,
        mobility: TaskMobility,
    ) -> Self {
        Self {
            inner: Mutex::new(TaskSlotInner {
                frame: async_handle_frame(handle),
                handle,
                out_ptr,
                out_buf,
                completed: false,
                queued: false,
                running: false,
                wake_requested: false,
                waiters: Vec::new(),
                owner_worker,
                last_worker: owner_worker,
                mobility,
            }),
        }
    }
}

#[derive(Default)]
struct RuntimeStats {
    steals: AtomicU64,
    parks: AtomicU64,
    wakeups: AtomicU64,
    global_injects: AtomicU64,
    worker_unparks: AtomicU64,
    global_unparks: AtomicU64,
    timer_wakeups: AtomicU64,
    io_wakeups: AtomicU64,
}

/// Current runtime limitations:
/// - Synchronous blocking syscalls still occupy an OS worker thread.
/// - TLS-affine foreign code remains unsafe for movable tasks unless future
///   runtime pinning support is added.
struct Scheduler {
    rooted: bool,
    test_mode: bool,
    worker_count: usize,
    tasks: Mutex<Vec<Arc<TaskSlot>>>,
    injector: Injector<TaskId>,
    local_workers: Mutex<Vec<Option<Worker<TaskId>>>>,
    stealers: Vec<Stealer<TaskId>>,
    pinned_queues: Vec<Mutex<VecDeque<TaskId>>>,
    remote_queues: Vec<Mutex<VecDeque<TaskId>>>,
    worker_threads: Vec<Mutex<Option<Thread>>>,
    worker_joins: Mutex<Vec<JoinHandle<()>>>,
    io_join: Mutex<Option<JoinHandle<()>>>,
    timers: Mutex<BinaryHeap<Reverse<TimerEntry>>>,
    next_timer_sequence: AtomicU64,
    incomplete_tasks: AtomicUsize,
    shutdown: AtomicBool,
    started: AtomicBool,
    wake_cursor: AtomicUsize,
    worker_panic: Mutex<Option<String>>,
    stats: RuntimeStats,
}

thread_local! {
    static WORKER_CONTEXT: RefCell<Option<WorkerContext>> = const { RefCell::new(None) };
}

struct WorkerContext {
    scheduler: Arc<Scheduler>,
    worker_id: usize,
    current_task: Option<TaskId>,
    current_task_blocked: bool,
}

struct WorkerContextGuard;

impl Drop for WorkerContextGuard {
    fn drop(&mut self) {
        WORKER_CONTEXT.with(|cell| {
            *cell.borrow_mut() = None;
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
        crate::garbage_collector::__gc__thread_detach();
    }
}

impl Drop for SessionGuard {
    fn drop(&mut self) {
        if !self.scheduler.shutdown.load(Ordering::Acquire) {
            self.scheduler.force_shutdown();
        }
        self.scheduler.join_background_threads();
        self.scheduler.teardown_remaining_tasks();
        clear_scheduler_if_current(&self.scheduler);
    }
}

#[derive(Clone, Copy)]
struct WakeRequest {
    task_id: TaskId,
    preferred_worker: Option<usize>,
}

struct WakeBatch {
    worker_touched: Vec<bool>,
    global_count: usize,
}

impl WakeBatch {
    fn new(worker_count: usize) -> Self {
        Self {
            worker_touched: vec![false; worker_count],
            global_count: 0,
        }
    }

    fn note_worker(&mut self, worker_id: usize) {
        if let Some(touched) = self.worker_touched.get_mut(worker_id) {
            *touched = true;
        }
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

impl Scheduler {
    fn new(rooted: bool, worker_count: usize) -> Arc<Self> {
        let mut locals = Vec::with_capacity(worker_count);
        let mut stealers = Vec::with_capacity(worker_count);
        let mut pinned_queues = Vec::with_capacity(worker_count);
        let mut remote_queues = Vec::with_capacity(worker_count);
        let mut worker_threads = Vec::with_capacity(worker_count);
        for _ in 0..worker_count {
            let local = Worker::new_lifo();
            stealers.push(local.stealer());
            locals.push(Some(local));
            pinned_queues.push(Mutex::new(VecDeque::new()));
            remote_queues.push(Mutex::new(VecDeque::new()));
            worker_threads.push(Mutex::new(None));
        }

        Arc::new(Self {
            rooted,
            test_mode: crate::panic_unwind::in_test_harness(),
            worker_count,
            tasks: Mutex::new(Vec::new()),
            injector: Injector::new(),
            local_workers: Mutex::new(locals),
            stealers,
            pinned_queues,
            remote_queues,
            worker_threads,
            worker_joins: Mutex::new(Vec::new()),
            io_join: Mutex::new(None),
            timers: Mutex::new(BinaryHeap::new()),
            next_timer_sequence: AtomicU64::new(0),
            incomplete_tasks: AtomicUsize::new(0),
            shutdown: AtomicBool::new(false),
            started: AtomicBool::new(false),
            wake_cursor: AtomicUsize::new(0),
            worker_panic: Mutex::new(None),
            stats: RuntimeStats::default(),
        })
    }

    fn start(self: &Arc<Self>) -> Worker<TaskId> {
        if self.started.swap(true, Ordering::AcqRel) {
            panic!("ICE: scheduler started twice");
        }

        io_poller::initialize().expect("async io reactor initialization failed");

        let io_scheduler = Arc::clone(self);
        let io_join = thread::Builder::new()
            .name("taro-io".into())
            .spawn(move || io_scheduler.io_driver_loop())
            .expect("failed to spawn io driver thread");
        *self.io_join.lock().unwrap() = Some(io_join);

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

    fn take_local_worker(&self, worker_id: usize) -> Worker<TaskId> {
        self.local_workers.lock().unwrap()[worker_id]
            .take()
            .expect("ICE: missing worker deque")
    }

    fn worker_loop(self: Arc<Self>, worker_id: usize, local: Worker<TaskId>) {
        self.register_worker_thread(worker_id);
        crate::garbage_collector::__gc__thread_attach();
        crate::panic_unwind::set_test_harness_active(self.test_mode);
        let _runtime_guard = WorkerRuntimeGuard;

        WORKER_CONTEXT.with(|cell| {
            *cell.borrow_mut() = Some(WorkerContext {
                scheduler: Arc::clone(&self),
                worker_id,
                current_task: None,
                current_task_blocked: false,
            });
        });
        let _guard = WorkerContextGuard;

        loop {
            if let Some(task_id) = self.next_task(worker_id, &local) {
                self.run_task(worker_id, task_id);
                continue;
            }

            if self.shutdown.load(Ordering::Acquire) {
                break;
            }

            let mut found = false;
            for _ in 0..IDLE_SPINS {
                std::hint::spin_loop();
                if let Some(task_id) = self.next_task(worker_id, &local) {
                    self.run_task(worker_id, task_id);
                    found = true;
                    break;
                }
            }
            if found {
                continue;
            }

            for _ in 0..IDLE_YIELDS {
                thread::yield_now();
                if let Some(task_id) = self.next_task(worker_id, &local) {
                    self.run_task(worker_id, task_id);
                    found = true;
                    break;
                }
            }
            if found {
                continue;
            }

            self.stats.parks.fetch_add(1, Ordering::Relaxed);
            thread::park();
        }
    }

    fn io_driver_loop(self: Arc<Self>) {
        crate::garbage_collector::__gc__thread_attach();
        crate::panic_unwind::set_test_harness_active(self.test_mode);
        let _runtime_guard = WorkerRuntimeGuard;
        while !self.shutdown.load(Ordering::Acquire) {
            self.wake_due_timers();
            let timeout = self.next_timer_timeout();
            let ready = io_poller::wait(timeout);
            if !ready.is_empty() {
                self.stats
                    .io_wakeups
                    .fetch_add(ready.len() as u64, Ordering::Relaxed);
                self.wake_tasks(&ready);
            }
            self.wake_due_timers();
        }
    }

    fn worker_thread_entry(self: Arc<Self>, worker_id: usize, local: Worker<TaskId>) {
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

    fn next_task(&self, worker_id: usize, local: &Worker<TaskId>) -> Option<TaskId> {
        if let Some(task_id) = self.pop_pinned_task(worker_id) {
            return Some(task_id);
        }
        self.drain_remote_queue(worker_id, local);

        if let Some(task_id) = local.pop() {
            return Some(task_id);
        }
        if let Some(task_id) = self.steal_batch_and_pop(&self.injector, local) {
            return Some(task_id);
        }

        for offset in 1..self.worker_count {
            let victim = (worker_id + offset) % self.worker_count;
            if let Some(task_id) = self.steal_batch_and_pop(&self.stealers[victim], local) {
                self.stats.steals.fetch_add(1, Ordering::Relaxed);
                return Some(task_id);
            }
        }

        None
    }

    fn pop_pinned_task(&self, worker_id: usize) -> Option<TaskId> {
        self.pinned_queues[worker_id].lock().unwrap().pop_front()
    }

    fn drain_remote_queue(&self, worker_id: usize, local: &Worker<TaskId>) {
        let mut remote = self.remote_queues[worker_id].lock().unwrap();
        let mut drained = Vec::with_capacity(remote.len());
        while let Some(task_id) = remote.pop_front() {
            drained.push(task_id);
        }
        drop(remote);

        for task_id in drained.into_iter().rev() {
            local.push(task_id);
        }
    }

    fn steal_batch_and_pop<S>(&self, stealer: &S, local: &Worker<TaskId>) -> Option<TaskId>
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

    fn register_worker_thread(&self, worker_id: usize) {
        *self.worker_threads[worker_id].lock().unwrap() = Some(thread::current());
    }

    fn add_task(
        &self,
        handle: *mut u8,
        out_ptr: *mut u8,
        out_buf: Option<Vec<u8>>,
        owner_worker: usize,
        preferred_worker: Option<usize>,
    ) -> TaskId {
        let frame = async_handle_frame(handle);
        let mobility = async_handle_mobility(handle);
        let slot = Arc::new(TaskSlot::new(
            handle,
            out_ptr,
            out_buf,
            owner_worker,
            mobility,
        ));

        if !frame.is_null() {
            with_gc(|gc| gc.add_persistent_root(frame as *const u8));
        }

        let task_id = {
            let mut tasks = self.tasks.lock().unwrap();
            let task_id = tasks.len();
            tasks.push(slot);
            task_id
        };
        self.incomplete_tasks.fetch_add(1, Ordering::AcqRel);
        self.schedule_task(task_id, preferred_worker);
        task_id
    }

    fn run_task(&self, worker_id: usize, task_id: TaskId) {
        let slot = self.lookup_task(task_id);
        let (handle, out_ptr) = {
            let mut inner = slot.inner.lock().unwrap();
            if inner.completed || inner.running || !inner.queued {
                return;
            }
            inner.queued = false;
            inner.running = true;
            inner.last_worker = worker_id;
            (inner.handle, inner.out_ptr)
        };

        WORKER_CONTEXT.with(|cell| {
            let mut borrow = cell.borrow_mut();
            let context = borrow.as_mut().expect("ICE: worker context missing");
            context.current_task = Some(task_id);
            context.current_task_blocked = false;
        });

        crate::garbage_collector::leave_safepoint();
        let tag = __rt__async_poll(handle, out_ptr);
        crate::garbage_collector::enter_safepoint();

        let blocked = WORKER_CONTEXT.with(|cell| {
            let mut borrow = cell.borrow_mut();
            let context = borrow.as_mut().expect("ICE: worker context missing");
            context.current_task = None;
            std::mem::take(&mut context.current_task_blocked)
        });

        if tag == 0 {
            let requeue_target = {
                let mut inner = slot.inner.lock().unwrap();
                inner.running = false;
                if inner.completed {
                    None
                } else if inner.wake_requested {
                    inner.wake_requested = false;
                    Some(match inner.mobility {
                        TaskMobility::Pinned => Some(inner.owner_worker),
                        TaskMobility::Movable => Some(inner.last_worker),
                    })
                } else if blocked {
                    None
                } else {
                    Some(match inner.mobility {
                        TaskMobility::Pinned => Some(inner.owner_worker),
                        // Let movable tasks re-enter through the injector so
                        // idle workers can pick them up after cooperative
                        // suspension.
                        TaskMobility::Movable => None,
                    })
                }
            };
            if let Some(preferred_worker) = requeue_target {
                self.schedule_task(task_id, preferred_worker);
            }
        } else {
            self.complete_task(task_id);
        }
    }

    fn complete_task(&self, task_id: TaskId) {
        let slot = self.lookup_task(task_id);
        let (frame, handle, waiters) = {
            let mut inner = slot.inner.lock().unwrap();
            if inner.completed {
                inner.running = false;
                return;
            }
            inner.completed = true;
            inner.running = false;
            inner.queued = false;
            let frame = inner.frame;
            let handle = inner.handle;
            inner.frame = std::ptr::null_mut();
            inner.handle = std::ptr::null_mut();
            (frame, handle, std::mem::take(&mut inner.waiters))
        };

        io_poller::cancel_task(task_id);
        if !frame.is_null() {
            with_gc(|gc| gc.remove_persistent_root(frame as *const u8));
        }
        if !handle.is_null() {
            __rt__async_destroy(handle);
        }

        self.wake_tasks(&waiters);

        if self.incomplete_tasks.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.force_shutdown();
        }
    }

    fn register_sleep(&self, task_id: TaskId, deadline: Instant) {
        let should_notify = {
            let mut timers = self.timers.lock().unwrap();
            let previous = timers.peek().map(|entry| entry.0.deadline);
            let sequence = self.next_timer_sequence.fetch_add(1, Ordering::Relaxed);
            timers.push(Reverse(TimerEntry {
                deadline,
                sequence,
                task_id,
            }));
            previous.is_none_or(|earliest| deadline < earliest)
        };

        if should_notify && self.started.load(Ordering::Acquire) {
            io_poller::notify();
        }
    }

    fn next_timer_timeout(&self) -> Option<StdDuration> {
        let deadline = self
            .timers
            .lock()
            .unwrap()
            .peek()
            .map(|entry| entry.0.deadline)?;
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
            while let Some(Reverse(entry)) = timers.peek().copied() {
                if entry.deadline > now {
                    break;
                }
                let _ = timers.pop();
                due.push(entry.task_id);
            }
        }

        if !due.is_empty() {
            self.stats
                .timer_wakeups
                .fetch_add(due.len() as u64, Ordering::Relaxed);
            self.wake_tasks(&due);
        }
    }

    fn lookup_task(&self, task_id: TaskId) -> Arc<TaskSlot> {
        self.tasks.lock().unwrap()[task_id].clone()
    }

    fn enqueue_task(
        &self,
        task_id: TaskId,
        preferred_worker: Option<usize>,
        batch: &mut WakeBatch,
    ) {
        let slot = self.lookup_task(task_id);
        let target = {
            let mut inner = slot.inner.lock().unwrap();
            if inner.completed || inner.queued {
                return;
            }
            if inner.running {
                inner.wake_requested = true;
                return;
            }
            inner.queued = true;
            match inner.mobility {
                TaskMobility::Pinned => QueueTarget::PinnedWorker(inner.owner_worker),
                TaskMobility::Movable => preferred_worker
                    .map(QueueTarget::Worker)
                    .unwrap_or(QueueTarget::Global),
            }
        };

        self.stats.wakeups.fetch_add(1, Ordering::Relaxed);
        match target {
            QueueTarget::PinnedWorker(worker_id) => {
                self.pinned_queues[worker_id]
                    .lock()
                    .unwrap()
                    .push_back(task_id);
                batch.note_worker(worker_id);
            }
            QueueTarget::Worker(worker_id) => {
                self.remote_queues[worker_id]
                    .lock()
                    .unwrap()
                    .push_back(task_id);
                batch.note_worker(worker_id);
            }
            QueueTarget::Global => {
                self.stats.global_injects.fetch_add(1, Ordering::Relaxed);
                self.injector.push(task_id);
                batch.note_global();
            }
        }
    }

    fn finish_wake_batch(&self, batch: WakeBatch) {
        if !self.started.load(Ordering::Acquire) {
            return;
        }

        for worker_id in batch.touched_workers() {
            self.unpark_worker(worker_id);
            self.stats.worker_unparks.fetch_add(1, Ordering::Relaxed);
        }

        let global_unparks = batch.global_count.min(self.worker_count);
        for _ in 0..global_unparks {
            self.unpark_next_worker();
            self.stats.global_unparks.fetch_add(1, Ordering::Relaxed);
        }
    }

    fn schedule_tasks<I>(&self, requests: I)
    where
        I: IntoIterator<Item = WakeRequest>,
    {
        let mut batch = WakeBatch::new(self.worker_count);
        for request in requests {
            self.enqueue_task(request.task_id, request.preferred_worker, &mut batch);
        }
        self.finish_wake_batch(batch);
    }

    fn schedule_task(&self, task_id: TaskId, preferred_worker: Option<usize>) {
        self.schedule_tasks([WakeRequest {
            task_id,
            preferred_worker,
        }]);
    }

    fn wake_tasks(&self, task_ids: &[TaskId]) {
        self.schedule_tasks(task_ids.iter().copied().map(|task_id| {
            let preferred_worker = {
                let slot = self.lookup_task(task_id);
                let inner = slot.inner.lock().unwrap();
                match inner.mobility {
                    TaskMobility::Pinned => Some(inner.owner_worker),
                    TaskMobility::Movable => Some(inner.last_worker),
                }
            };
            WakeRequest {
                task_id,
                preferred_worker,
            }
        }));
    }

    fn force_shutdown(&self) {
        if self.shutdown.swap(true, Ordering::AcqRel) {
            return;
        }
        io_poller::notify();
        for worker_id in 0..self.worker_count {
            self.unpark_worker(worker_id);
        }
    }

    fn unpark_worker(&self, worker_id: usize) {
        if let Some(thread) = self.worker_threads[worker_id].lock().unwrap().as_ref() {
            thread.unpark();
        }
    }

    fn unpark_next_worker(&self) {
        if self.worker_count == 0 {
            return;
        }

        let current_worker = current_worker_id();
        let start = self.wake_cursor.fetch_add(1, Ordering::Relaxed);
        for offset in 0..self.worker_count {
            let worker_id = (start + offset) % self.worker_count;
            if current_worker == Some(worker_id) {
                continue;
            }
            if self.worker_threads[worker_id].lock().unwrap().is_some() {
                self.unpark_worker(worker_id);
                return;
            }
        }

        if let Some(worker_id) = current_worker {
            if self.worker_threads[worker_id].lock().unwrap().is_some() {
                self.unpark_worker(worker_id);
            }
        }
    }

    fn join_background_threads(&self) {
        if let Some(join) = self.io_join.lock().unwrap().take() {
            let _ = join.join();
        }
        let mut joins = self.worker_joins.lock().unwrap();
        for join in joins.drain(..) {
            let _ = join.join();
        }
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

    fn teardown_remaining_tasks(&self) {
        let tasks = self.tasks.lock().unwrap();
        for (task_id, slot) in tasks.iter().enumerate() {
            let (frame, handle, completed) = {
                let mut inner = slot.inner.lock().unwrap();
                if inner.completed {
                    (std::ptr::null_mut(), std::ptr::null_mut(), true)
                } else {
                    inner.completed = true;
                    inner.running = false;
                    inner.queued = false;
                    let frame = inner.frame;
                    let handle = inner.handle;
                    inner.frame = std::ptr::null_mut();
                    inner.handle = std::ptr::null_mut();
                    (frame, handle, false)
                }
            };
            if completed {
                continue;
            }
            io_poller::cancel_task(task_id);
            if !frame.is_null() {
                with_gc(|gc| gc.remove_persistent_root(frame as *const u8));
            }
            if !handle.is_null() {
                __rt__async_destroy(handle);
            }
        }
    }
}

trait StealSource {
    fn steal_batch_and_pop(&self, local: &Worker<TaskId>) -> Steal<TaskId>;
}

impl StealSource for Injector<TaskId> {
    fn steal_batch_and_pop(&self, local: &Worker<TaskId>) -> Steal<TaskId> {
        self.steal_batch_and_pop(local)
    }
}

impl StealSource for Stealer<TaskId> {
    fn steal_batch_and_pop(&self, local: &Worker<TaskId>) -> Steal<TaskId> {
        self.steal_batch_and_pop(local)
    }
}

enum QueueTarget {
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

fn configured_worker_count() -> usize {
    if let Ok(raw) = std::env::var("TARO_WORKERS") {
        if let Ok(count) = raw.parse::<usize>() {
            if count > 0 {
                return count;
            }
        }
    }
    thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1)
        .max(1)
}

fn create_scheduler(rooted: bool) -> Arc<Scheduler> {
    Scheduler::new(rooted, configured_worker_count())
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

fn current_worker_scheduler() -> Option<Arc<Scheduler>> {
    WORKER_CONTEXT.with(|cell| {
        cell.borrow()
            .as_ref()
            .map(|context| Arc::clone(&context.scheduler))
    })
}

fn current_worker_id() -> Option<usize> {
    WORKER_CONTEXT.with(|cell| cell.borrow().as_ref().map(|context| context.worker_id))
}

/// Entry point: run an async handle to completion using the multithreaded
/// executor.
pub fn run_root(handle: *mut u8, out: *mut u8) {
    let scheduler = install_scheduler(true);
    let _guard = SessionGuard {
        scheduler: Arc::clone(&scheduler),
    };

    scheduler.add_task(handle, out, None, 0, Some(0));
    let local = scheduler.start();
    Arc::clone(&scheduler).worker_loop(0, local);
    if let Some(message) = scheduler.take_worker_panic() {
        crate::panic_unwind::resume_test_panic(message);
    }
}

/// Spawn a new task on the executor. Returns a task ID that can be polled
/// later via `__rt__executor_poll_spawned`.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__executor_spawn(handle: *mut u8, out_size: u64) -> u64 {
    let scheduler = current_worker_scheduler().unwrap_or_else(ensure_rootless_scheduler);
    let owner_worker = current_worker_id().unwrap_or(0);

    let mut out_buf = vec![0u8; out_size as usize];
    let out_ptr = out_buf.as_mut_ptr();
    let preferred_worker = Some(owner_worker);
    let task_id = scheduler.add_task(
        handle,
        out_ptr,
        Some(out_buf),
        owner_worker,
        preferred_worker,
    );
    task_id as u64
}

/// Poll a spawned task by ID. Returns 1 if completed (output copied to `out`),
/// 0 if still pending (current task registered as waiter).
#[unsafe(no_mangle)]
pub extern "C" fn __rt__executor_poll_spawned(task_id: u64, out: *mut u8) -> u8 {
    WORKER_CONTEXT.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let context = borrow
            .as_mut()
            .expect("poll_spawned called outside executor worker");
        let slot = context.scheduler.lookup_task(task_id as usize);
        let mut inner = slot.inner.lock().unwrap();

        if inner.completed {
            let src = inner.out_ptr;
            if let Some(buf) = &inner.out_buf {
                unsafe { std::ptr::copy_nonoverlapping(src, out, buf.len()) };
            }
            1
        } else {
            let current = context
                .current_task
                .expect("poll_spawned called with no current task");
            if !inner.waiters.contains(&current) {
                inner.waiters.push(current);
            }
            context.current_task_blocked = true;
            0
        }
    })
}

pub(crate) fn register_sleep(deadline: Instant) {
    WORKER_CONTEXT.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let context = borrow.as_mut().expect("sleep polled outside executor");
        let task_id = context
            .current_task
            .expect("sleep polled with no current task");
        context.current_task_blocked = true;
        context.scheduler.register_sleep(task_id, deadline);
    });
}

pub(crate) fn register_io_wait(source_id: usize, interest: Interest) -> Result<(), i32> {
    WORKER_CONTEXT.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let context = borrow.as_mut().expect("async io polled outside executor");
        let current = context
            .current_task
            .expect("async io polled with no current task");

        io_poller::register_wait(source_id, current, interest)?;
        context.current_task_blocked = true;
        Ok(())
    })
}

pub(crate) fn wake_tasks(task_ids: &[usize]) {
    if let Some(scheduler) = current_worker_scheduler() {
        scheduler.wake_tasks(task_ids);
        return;
    }

    let scheduler = {
        let session = session_cell().lock().unwrap();
        session.as_ref().cloned()
    };
    if let Some(scheduler) = scheduler {
        scheduler.wake_tasks(task_ids);
    }
}

/// Finish any lazily-created rootless executor work after a synchronous root
/// returns. This is a no-op when no rootless executor was created.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__executor_finish_rootless() {
    let scheduler = {
        let session = session_cell().lock().unwrap();
        let Some(scheduler) = session.as_ref() else {
            return;
        };
        assert!(
            !scheduler.rooted,
            "ICE: finish_rootless called while rooted executor is active"
        );
        Arc::clone(scheduler)
    };

    if scheduler.incomplete_tasks.load(Ordering::Acquire) == 0 {
        clear_scheduler_if_current(&scheduler);
        return;
    }

    let _guard = SessionGuard {
        scheduler: Arc::clone(&scheduler),
    };
    let local = if scheduler.started.load(Ordering::Acquire) {
        panic!("ICE: rootless scheduler already started");
    } else {
        scheduler.start()
    };
    Arc::clone(&scheduler).worker_loop(0, local);
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

    scheduler.force_shutdown();
    scheduler.join_background_threads();
    scheduler.teardown_remaining_tasks();
    clear_scheduler_if_current(&scheduler);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::task::{__rt__async_create, __rt__async_run_root, TaskMobility};
    use std::collections::{HashMap, HashSet};
    use std::ptr;
    use std::sync::{Arc, Mutex};

    static TEST_ENV_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn worker_count_prefers_env_override() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        unsafe { std::env::set_var("TARO_WORKERS", "2") };
        assert_eq!(configured_worker_count(), 2);
        unsafe { std::env::remove_var("TARO_WORKERS") };
    }

    #[test]
    fn batched_wakeups_limit_unparks() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 4);
        scheduler.started.store(true, Ordering::Release);

        for worker_id in 0..scheduler.worker_count {
            *scheduler.worker_threads[worker_id].lock().unwrap() = Some(thread::current());
        }

        let mut tasks = scheduler.tasks.lock().unwrap();
        for _ in 0..8 {
            tasks.push(Arc::new(TaskSlot::new(
                ptr::null_mut(),
                ptr::null_mut(),
                None,
                0,
                TaskMobility::Movable,
            )));
        }
        for _ in 0..5 {
            tasks.push(Arc::new(TaskSlot::new(
                ptr::null_mut(),
                ptr::null_mut(),
                None,
                1,
                TaskMobility::Pinned,
            )));
        }
        for _ in 0..3 {
            tasks.push(Arc::new(TaskSlot::new(
                ptr::null_mut(),
                ptr::null_mut(),
                None,
                2,
                TaskMobility::Pinned,
            )));
        }
        drop(tasks);

        let requests = (0..8)
            .map(|task_id| WakeRequest {
                task_id,
                preferred_worker: None,
            })
            .chain((8..16).map(|task_id| WakeRequest {
                task_id,
                preferred_worker: Some(0),
            }));

        scheduler.schedule_tasks(requests);

        assert_eq!(scheduler.stats.wakeups.load(Ordering::Relaxed), 16);
        assert_eq!(scheduler.stats.global_injects.load(Ordering::Relaxed), 8);
        assert_eq!(scheduler.stats.global_unparks.load(Ordering::Relaxed), 4);
        assert_eq!(scheduler.stats.worker_unparks.load(Ordering::Relaxed), 2);
    }

    #[test]
    fn idle_workers_remain_at_safepoint_during_collection() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 3);
        let local = scheduler.start();
        drop(local);

        let deadline = Instant::now() + StdDuration::from_secs(1);
        while Instant::now() < deadline {
            let all_registered = (1..scheduler.worker_count).all(|worker_id| {
                scheduler.worker_threads[worker_id]
                    .lock()
                    .unwrap()
                    .is_some()
            });
            if all_registered {
                break;
            }
            thread::yield_now();
        }

        thread::sleep(StdDuration::from_millis(20));
        crate::garbage_collector::__gc__thread_attach();
        crate::garbage_collector::__gc__collect();
        crate::garbage_collector::__gc__thread_detach();

        scheduler.force_shutdown();
        scheduler.join_background_threads();
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

    unsafe extern "C" fn child_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut ChildFrame) };
    }

    struct RootFrame {
        mobility: TaskMobility,
        recorder: ThreadRecorder,
        child_ids: Vec<u64>,
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
                frame.child_ids.push(__rt__executor_spawn(handle, 0));
            }
            frame.spawned = true;
            return 0;
        }

        let mut all_done = true;
        for &task_id in &frame.child_ids {
            if __rt__executor_poll_spawned(task_id, std::ptr::null_mut()) == 0 {
                all_done = false;
            }
        }
        u8::from(all_done)
    }

    unsafe extern "C" fn root_drop(frame: *mut u8) {
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
        let visits = run_recording_root(TaskMobility::Movable);
        assert!(visits.values().any(|threads| threads.len() > 1));
    }

    #[test]
    fn pinned_tasks_stay_on_one_worker() {
        let visits = run_recording_root(TaskMobility::Pinned);
        assert!(visits.values().all(|threads| threads.len() == 1));
    }
}
