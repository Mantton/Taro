use crossbeam_deque::{Injector, Steal, Stealer, Worker};
use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, VecDeque};
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock, RwLock};
use std::thread::{self, JoinHandle, Thread};
use std::time::{Duration as StdDuration, Instant};

use crate::garbage_collector::with_gc;
use crate::io_poller::{self, Interest};
use crate::task::{
    __rt__async_destroy, __rt__async_poll, TaskMobility, async_handle_frame, async_handle_mobility,
};

type TaskIndex = usize;
type TaskGeneration = u32;
type TaskToken = u64;

const IDLE_SPINS: usize = 32;
const IDLE_YIELDS: usize = 8;
const TASK_TOKEN_INDEX_BITS: u32 = 32;
const TASK_TOKEN_INDEX_MASK: u64 = (1u64 << TASK_TOKEN_INDEX_BITS) - 1;
const TASK_INITIAL_GENERATION: TaskGeneration = 1;

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
    inner: Mutex<TaskSlotInner>,
}

struct TaskSlotInner {
    generation: TaskGeneration,
    occupied: bool,
    handle: *mut u8,
    frame: *mut u8,
    out_ptr: *mut u8,
    out_buf: Option<Vec<u8>>,
    completed: bool,
    queued: bool,
    running: bool,
    wake_requested: bool,
    waiter: Option<TaskToken>,
    owner_worker: usize,
    last_worker: usize,
    mobility: TaskMobility,
}

unsafe impl Send for TaskSlot {}
unsafe impl Sync for TaskSlot {}

impl TaskSlot {
    fn new(
        generation: TaskGeneration,
        handle: *mut u8,
        out_ptr: *mut u8,
        out_buf: Option<Vec<u8>>,
        owner_worker: usize,
        mobility: TaskMobility,
    ) -> Self {
        Self {
            inner: Mutex::new(TaskSlotInner {
                generation,
                occupied: true,
                frame: async_handle_frame(handle),
                handle,
                out_ptr,
                out_buf,
                completed: false,
                queued: false,
                running: false,
                wake_requested: false,
                waiter: None,
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
    tasks: RwLock<Vec<Arc<TaskSlot>>>,
    free_slots: Mutex<Vec<TaskIndex>>,
    injector: Injector<TaskToken>,
    local_workers: Mutex<Vec<Option<Worker<TaskToken>>>>,
    stealers: Vec<Stealer<TaskToken>>,
    pinned_queues: Vec<Mutex<VecDeque<TaskToken>>>,
    remote_queues: Vec<Mutex<VecDeque<TaskToken>>>,
    worker_threads: Vec<Mutex<Option<Thread>>>,
    worker_registered: Vec<AtomicBool>,
    worker_joins: Mutex<Vec<JoinHandle<()>>>,
    io_join: Mutex<Option<JoinHandle<()>>>,
    timers: Mutex<TimerState>,
    next_timer_sequence: AtomicU64,
    idle_workers: AtomicUsize,
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
    current_task: Option<TaskToken>,
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
    task_token: TaskToken,
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

fn pack_task_token(index: TaskIndex, generation: TaskGeneration) -> TaskToken {
    let raw_index =
        u32::try_from(index).unwrap_or_else(|_| panic!("task slot index {index} exceeds token width"));
    (u64::from(generation) << TASK_TOKEN_INDEX_BITS) | u64::from(raw_index)
}

fn unpack_task_token(token: TaskToken) -> (TaskIndex, TaskGeneration) {
    let index = (token & TASK_TOKEN_INDEX_MASK) as TaskIndex;
    let generation = (token >> TASK_TOKEN_INDEX_BITS) as TaskGeneration;
    (index, generation)
}

fn next_task_generation(generation: TaskGeneration) -> TaskGeneration {
    let next = generation.wrapping_add(1);
    if next == 0 { 1 } else { next }
}

impl Scheduler {
    fn new(rooted: bool, worker_count: usize) -> Arc<Self> {
        let mut locals = Vec::with_capacity(worker_count);
        let mut stealers = Vec::with_capacity(worker_count);
        let mut pinned_queues = Vec::with_capacity(worker_count);
        let mut remote_queues = Vec::with_capacity(worker_count);
        let mut worker_threads = Vec::with_capacity(worker_count);
        let mut worker_registered = Vec::with_capacity(worker_count);
        for _ in 0..worker_count {
            let local = Worker::new_lifo();
            stealers.push(local.stealer());
            locals.push(Some(local));
            pinned_queues.push(Mutex::new(VecDeque::new()));
            remote_queues.push(Mutex::new(VecDeque::new()));
            worker_threads.push(Mutex::new(None));
            worker_registered.push(AtomicBool::new(false));
        }

        Arc::new(Self {
            rooted,
            test_mode: crate::panic_unwind::in_test_harness(),
            worker_count,
            tasks: RwLock::new(Vec::new()),
            free_slots: Mutex::new(Vec::new()),
            injector: Injector::new(),
            local_workers: Mutex::new(locals),
            stealers,
            pinned_queues,
            remote_queues,
            worker_threads,
            worker_registered,
            worker_joins: Mutex::new(Vec::new()),
            io_join: Mutex::new(None),
            timers: Mutex::new(TimerState {
                heap: BinaryHeap::new(),
                latest: Vec::new(),
            }),
            next_timer_sequence: AtomicU64::new(0),
            idle_workers: AtomicUsize::new(0),
            incomplete_tasks: AtomicUsize::new(0),
            shutdown: AtomicBool::new(false),
            started: AtomicBool::new(false),
            wake_cursor: AtomicUsize::new(0),
            worker_panic: Mutex::new(None),
            stats: RuntimeStats::default(),
        })
    }

    fn start(self: &Arc<Self>) -> Worker<TaskToken> {
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

    fn take_local_worker(&self, worker_id: usize) -> Worker<TaskToken> {
        self.local_workers.lock().unwrap()[worker_id]
            .take()
            .expect("ICE: missing worker deque")
    }

    fn worker_loop(self: Arc<Self>, worker_id: usize, local: Worker<TaskToken>) {
        // GC attach first: registers this thread in THREAD_REGISTRY and sets
        // at_safepoint=true before we expose the thread handle to the scheduler.
        // If the order were reversed a concurrent GC could observe the thread
        // in worker_threads but not yet in THREAD_REGISTRY, missing it during
        // the safepoint wait.
        crate::garbage_collector::__gc__thread_attach();
        self.register_worker_thread(worker_id);
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
            self.idle_workers.fetch_add(1, Ordering::AcqRel);
            thread::park();
            self.idle_workers.fetch_sub(1, Ordering::AcqRel);
        }
    }

    fn io_driver_loop(self: Arc<Self>) {
        crate::garbage_collector::__gc__thread_attach();
        crate::panic_unwind::set_test_harness_active(self.test_mode);
        let _runtime_guard = WorkerRuntimeGuard;
        while !self.shutdown.load(Ordering::Acquire) {
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

    fn next_task(&self, worker_id: usize, local: &Worker<TaskToken>) -> Option<TaskToken> {
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

    fn pop_pinned_task(&self, worker_id: usize) -> Option<TaskToken> {
        self.pinned_queues[worker_id].lock().unwrap().pop_front()
    }

    fn drain_remote_queue(&self, worker_id: usize, local: &Worker<TaskToken>) {
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

    fn register_worker_thread(&self, worker_id: usize) {
        *self.worker_threads[worker_id].lock().unwrap() = Some(thread::current());
        self.worker_registered[worker_id].store(true, Ordering::Release);
    }

    fn add_task(
        &self,
        handle: *mut u8,
        out_ptr: *mut u8,
        out_buf: Option<Vec<u8>>,
        owner_worker: usize,
        preferred_worker: Option<usize>,
    ) -> TaskToken {
        let frame = async_handle_frame(handle);
        let mobility = async_handle_mobility(handle);

        let (task_index, task_generation) =
            if let Some(task_index) = self.free_slots.lock().unwrap().pop() {
                let slot = self
                    .lookup_task_slot(task_index)
                    .unwrap_or_else(|| panic!("ICE: recycled task slot {task_index} missing"));
                let mut inner = slot.inner.lock().unwrap();
                assert!(
                    !inner.occupied,
                    "ICE: recycled task slot {task_index} is still occupied"
                );
                let generation = next_task_generation(inner.generation);
                inner.generation = generation;
                inner.occupied = true;
                inner.handle = handle;
                inner.frame = frame;
                inner.out_ptr = out_ptr;
                inner.out_buf = out_buf;
                inner.completed = false;
                inner.queued = false;
                inner.running = false;
                inner.wake_requested = false;
                inner.waiter = None;
                inner.owner_worker = owner_worker;
                inner.last_worker = owner_worker;
                inner.mobility = mobility;
                (task_index, generation)
            } else {
                let task_generation = TASK_INITIAL_GENERATION;
                let slot = Arc::new(TaskSlot::new(
                    task_generation,
                    handle,
                    out_ptr,
                    out_buf,
                    owner_worker,
                    mobility,
                ));
                let task_index = {
                    let mut tasks = self.tasks.write().unwrap();
                    let task_index = tasks.len();
                    tasks.push(slot);
                    task_index
                };
                {
                    let mut timers = self.timers.lock().unwrap();
                    timers.latest.push(None);
                }
                (task_index, task_generation)
            };

        if !frame.is_null() {
            with_gc(|gc| gc.add_persistent_root(frame as *const u8));
        }

        let task_token = pack_task_token(task_index, task_generation);
        self.incomplete_tasks.fetch_add(1, Ordering::AcqRel);
        self.schedule_task(task_token, preferred_worker);
        task_token
    }

    fn run_task(&self, worker_id: usize, task_token: TaskToken) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        let (handle, out_ptr) = {
            let mut inner = slot.inner.lock().unwrap();
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
            inner.last_worker = worker_id;
            (inner.handle, inner.out_ptr)
        };

        WORKER_CONTEXT.with(|cell| {
            let mut borrow = cell.borrow_mut();
            let context = borrow.as_mut().expect("ICE: worker context missing");
            context.current_task = Some(task_token);
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
                if !inner.occupied || inner.generation != task_generation || inner.completed {
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
                self.schedule_task(task_token, preferred_worker);
            }
        } else {
            self.complete_task(task_token);
        }
    }

    fn complete_task(&self, task_token: TaskToken) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        let (frame, handle, waiter) = {
            let mut inner = slot.inner.lock().unwrap();
            if !inner.occupied || inner.generation != task_generation {
                return;
            }
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
            (frame, handle, inner.waiter.take())
        };

        io_poller::cancel_task(task_token);
        self.clear_task_timer(task_token);
        if !frame.is_null() {
            with_gc(|gc| gc.remove_persistent_root(frame as *const u8));
        }
        if !handle.is_null() {
            __rt__async_destroy(handle);
        }

        if let Some(waiter) = waiter {
            self.wake_tasks(&[waiter]);
        }

        if self.incomplete_tasks.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.force_shutdown();
        }
    }

    fn reclaim_task_slot(&self, task_token: TaskToken, inner: &mut TaskSlotInner) {
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
        inner.waiter = None;
        inner.queued = false;
        inner.running = false;
        inner.wake_requested = false;
        inner.handle = std::ptr::null_mut();
        inner.frame = std::ptr::null_mut();
        inner.out_ptr = std::ptr::null_mut();
        inner.out_buf = None;
        self.free_slots.lock().unwrap().push(task_index);
    }

    fn register_sleep(&self, task_token: TaskToken, deadline: Instant) {
        let (task_index, _) = unpack_task_token(task_token);
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
            timers.latest[task_index] = Some(TimerRegistration { deadline, sequence });
            previous.is_none_or(|earliest| deadline < earliest)
        };

        if should_notify && self.started.load(Ordering::Acquire) {
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
            self.stats
                .timer_wakeups
                .fetch_add(due.len() as u64, Ordering::Relaxed);
            self.wake_tasks(&due);
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

    fn lookup_task_slot(&self, task_index: TaskIndex) -> Option<Arc<TaskSlot>> {
        self.tasks.read().unwrap().get(task_index).cloned()
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

    fn enqueue_task(
        &self,
        task_token: TaskToken,
        preferred_worker: Option<usize>,
        batch: &mut WakeBatch,
    ) {
        let (task_index, task_generation) = unpack_task_token(task_token);
        let Some(slot) = self.lookup_task_slot(task_index) else {
            return;
        };
        let target = {
            let mut inner = slot.inner.lock().unwrap();
            if !inner.occupied || inner.generation != task_generation || inner.completed || inner.queued
            {
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
                    .push_back(task_token);
                batch.note_worker(worker_id);
            }
            QueueTarget::Worker(worker_id) => {
                self.remote_queues[worker_id]
                    .lock()
                    .unwrap()
                    .push_back(task_token);
                batch.note_worker(worker_id);
            }
            QueueTarget::Global => {
                self.stats.global_injects.fetch_add(1, Ordering::Relaxed);
                self.injector.push(task_token);
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
            self.enqueue_task(request.task_token, request.preferred_worker, &mut batch);
        }
        self.finish_wake_batch(batch);
    }

    fn schedule_task(&self, task_token: TaskToken, preferred_worker: Option<usize>) {
        self.schedule_tasks([WakeRequest {
            task_token,
            preferred_worker,
        }]);
    }

    fn wake_tasks(&self, task_tokens: &[TaskToken]) {
        self.schedule_tasks(task_tokens.iter().copied().map(|task_token| {
            let (task_index, task_generation) = unpack_task_token(task_token);
            let preferred_worker = {
                let Some(slot) = self.lookup_task_slot(task_index) else {
                    return WakeRequest {
                        task_token,
                        preferred_worker: None,
                    };
                };
                let inner = slot.inner.lock().unwrap();
                if !inner.occupied || inner.generation != task_generation {
                    return WakeRequest {
                        task_token,
                        preferred_worker: None,
                    };
                }
                match inner.mobility {
                    TaskMobility::Pinned => Some(inner.owner_worker),
                    TaskMobility::Movable => Some(inner.last_worker),
                }
            };
            WakeRequest {
                task_token,
                preferred_worker,
            }
        }));
    }

    fn force_shutdown(&self) {
        if self.shutdown.swap(true, Ordering::AcqRel) {
            return;
        }
        // Unblock any thread waiting for a GC cycle to complete. Without this,
        // a worker-thread panic can leave other threads deadlocked forever in
        // wait_for_gc_resume since no collector will ever finish the GC and
        // clear GC_REQUESTED.
        crate::garbage_collector::cancel_pending_collection();
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
        if self.worker_count == 0 || self.idle_workers.load(Ordering::Acquire) == 0 {
            return;
        }

        let current_worker = current_worker_id();
        let start = self.wake_cursor.fetch_add(1, Ordering::Relaxed);
        for offset in 0..self.worker_count {
            let worker_id = (start + offset) % self.worker_count;
            if current_worker == Some(worker_id) {
                continue;
            }
            if self.worker_registered[worker_id].load(Ordering::Acquire) {
                self.unpark_worker(worker_id);
                return;
            }
        }

        if let Some(worker_id) = current_worker {
            if self.worker_registered[worker_id].load(Ordering::Acquire) {
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
        let tasks: Vec<_> = self.tasks.read().unwrap().iter().cloned().collect();
        for (task_index, slot) in tasks.iter().enumerate() {
            let (task_token, frame, handle) = {
                let mut inner = slot.inner.lock().unwrap();
                if !inner.occupied || inner.completed {
                    inner.occupied = false;
                    (None, std::ptr::null_mut(), std::ptr::null_mut())
                } else {
                    let generation = inner.generation;
                    let task_token = pack_task_token(task_index, generation);
                    inner.completed = true;
                    inner.occupied = false;
                    inner.running = false;
                    inner.queued = false;
                    let frame = inner.frame;
                    let handle = inner.handle;
                    inner.frame = std::ptr::null_mut();
                    inner.handle = std::ptr::null_mut();
                    (Some(task_token), frame, handle)
                }
            };
            let Some(task_token) = task_token else {
                continue;
            };
            io_poller::cancel_task(task_token);
            self.clear_task_timer(task_token);
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

/// Spawn a new task on the executor. Returns a task token that can be polled
/// later via `__rt__executor_poll_spawned`.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__executor_spawn(handle: *mut u8, out_size: u64) -> u64 {
    let scheduler = current_worker_scheduler().unwrap_or_else(ensure_rootless_scheduler);
    let owner_worker = current_worker_id().unwrap_or(0);

    let mut out_buf = vec![0u8; out_size as usize];
    let out_ptr = out_buf.as_mut_ptr();
    // Work-first policy: start newly spawned tasks on the current worker to
    // preserve cache locality; movable tasks can still migrate after the first
    // pending poll via injector requeue.
    let preferred_worker = Some(owner_worker);
    let task_token = scheduler.add_task(
        handle,
        out_ptr,
        Some(out_buf),
        owner_worker,
        preferred_worker,
    );
    task_token
}

/// Poll a spawned task by token. Returns 1 if completed (output copied to `out`),
/// 0 if still pending (current task registered as the sole waiter).
#[unsafe(no_mangle)]
pub extern "C" fn __rt__executor_poll_spawned(task_token: u64, out: *mut u8) -> u8 {
    WORKER_CONTEXT.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let context = borrow
            .as_mut()
            .expect("poll_spawned called outside executor worker");
        let current = context
            .current_task
            .expect("poll_spawned called with no current task");
        let (task_index, task_generation) = unpack_task_token(task_token);
        let slot = context
            .scheduler
            .lookup_task_slot(task_index)
            .unwrap_or_else(|| panic!("invalid spawned task token {task_token}"));
        let mut inner = slot.inner.lock().unwrap();
        if !inner.occupied || inner.generation != task_generation {
            panic!("stale spawned task token {task_token}");
        }

        if inner.completed {
            if let Some(waiter) = inner.waiter {
                assert_eq!(
                    waiter, current,
                    "spawned task value already reserved by another waiter"
                );
            }

            if let Some(buf) = inner.out_buf.take() {
                if !out.is_null() && !buf.is_empty() {
                    unsafe { std::ptr::copy_nonoverlapping(buf.as_ptr(), out, buf.len()) };
                }
            }
            inner.waiter = None;
            context.scheduler.reclaim_task_slot(task_token, &mut inner);
            1
        } else {
            match inner.waiter {
                Some(waiter) if waiter != current => {
                    panic!("spawned task value already has an active waiter");
                }
                Some(_) => {}
                None => inner.waiter = Some(current),
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
        let task_token = context
            .current_task
            .expect("sleep polled with no current task");
        context.current_task_blocked = true;
        context.scheduler.register_sleep(task_token, deadline);
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

pub(crate) fn wake_tasks(task_tokens: &[TaskToken]) {
    if let Some(scheduler) = current_worker_scheduler() {
        scheduler.wake_tasks(task_tokens);
        return;
    }

    let scheduler = {
        let session = session_cell().lock().unwrap();
        session.as_ref().cloned()
    };
    if let Some(scheduler) = scheduler {
        scheduler.wake_tasks(task_tokens);
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
    use std::panic::{self, AssertUnwindSafe};
    use std::ptr;
    use std::sync::{Arc, Condvar, Mutex, mpsc};

    static TEST_ENV_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn worker_count_prefers_env_override() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let previous = std::env::var_os("TARO_WORKERS");
        unsafe { std::env::set_var("TARO_WORKERS", "2") };
        assert_eq!(configured_worker_count(), 2);
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
        assert_eq!(configured_worker_count(), expected);
        if let Some(previous) = previous {
            unsafe { std::env::set_var("TARO_WORKERS", previous) };
        }
    }

    #[test]
    fn batched_wakeups_limit_unparks() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 4);
        scheduler.started.store(true, Ordering::Release);

        for worker_id in 0..scheduler.worker_count {
            *scheduler.worker_threads[worker_id].lock().unwrap() = Some(thread::current());
            scheduler.worker_registered[worker_id].store(true, Ordering::Release);
        }

        let mut tasks = scheduler.tasks.write().unwrap();
        for _ in 0..8 {
            tasks.push(Arc::new(TaskSlot::new(
                TASK_INITIAL_GENERATION,
                ptr::null_mut(),
                ptr::null_mut(),
                None,
                0,
                TaskMobility::Movable,
            )));
        }
        for _ in 0..5 {
            tasks.push(Arc::new(TaskSlot::new(
                TASK_INITIAL_GENERATION,
                ptr::null_mut(),
                ptr::null_mut(),
                None,
                1,
                TaskMobility::Pinned,
            )));
        }
        for _ in 0..3 {
            tasks.push(Arc::new(TaskSlot::new(
                TASK_INITIAL_GENERATION,
                ptr::null_mut(),
                ptr::null_mut(),
                None,
                2,
                TaskMobility::Pinned,
            )));
        }
        drop(tasks);

        let requests = (0..8)
            .map(|task_index| WakeRequest {
                task_token: pack_task_token(task_index, TASK_INITIAL_GENERATION),
                preferred_worker: None,
            })
            .chain((8..16).map(|task_index| WakeRequest {
                task_token: pack_task_token(task_index, TASK_INITIAL_GENERATION),
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

    #[test]
    fn task_token_pack_unpack_roundtrip() {
        let token = pack_task_token(17, 42);
        let (index, generation) = unpack_task_token(token);
        assert_eq!(index, 17);
        assert_eq!(generation, 42);
    }

    #[test]
    fn consumed_completed_task_slot_is_reused() {
        let scheduler = Scheduler::new(false, 1);
        let slot = Arc::new(TaskSlot::new(
            TASK_INITIAL_GENERATION,
            ptr::null_mut(),
            ptr::null_mut(),
            Some(Vec::new()),
            0,
            TaskMobility::Movable,
        ));
        {
            let mut inner = slot.inner.lock().unwrap();
            inner.completed = true;
        }
        scheduler.tasks.write().unwrap().push(Arc::clone(&slot));
        scheduler.timers.lock().unwrap().latest.push(None);

        let old_token = pack_task_token(0, TASK_INITIAL_GENERATION);
        {
            let mut inner = slot.inner.lock().unwrap();
            scheduler.reclaim_task_slot(old_token, &mut inner);
        }

        let new_token = scheduler.add_task(ptr::null_mut(), ptr::null_mut(), Some(Vec::new()), 0, None);
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
            Some(Vec::new()),
            0,
            TaskMobility::Movable,
        ));
        {
            let mut inner = slot.inner.lock().unwrap();
            inner.completed = true;
        }
        scheduler.tasks.write().unwrap().push(Arc::clone(&slot));
        scheduler.timers.lock().unwrap().latest.push(None);

        let stale_token = pack_task_token(0, TASK_INITIAL_GENERATION);
        {
            let mut inner = slot.inner.lock().unwrap();
            scheduler.reclaim_task_slot(stale_token, &mut inner);
        }
        let _current_token =
            scheduler.add_task(ptr::null_mut(), ptr::null_mut(), Some(Vec::new()), 0, None);

        let panicked =
            panic::catch_unwind(AssertUnwindSafe(|| scheduler.assert_spawned_token_live_or_panic(stale_token)));
        assert!(panicked.is_err());
    }

    #[test]
    fn completed_unconsumed_task_remains_until_teardown() {
        let scheduler = Scheduler::new(false, 1);
        let token = scheduler.add_task(ptr::null_mut(), ptr::null_mut(), Some(Vec::new()), 0, None);
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

    fn note_max(counter: &AtomicUsize, candidate: usize) {
        let mut current = counter.load(Ordering::Relaxed);
        while current < candidate {
            match counter.compare_exchange_weak(
                current,
                candidate,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(observed) => current = observed,
            }
        }
    }

    #[derive(Clone)]
    struct OneShotRecorder {
        in_flight: Arc<AtomicUsize>,
        max_in_flight: Arc<AtomicUsize>,
        threads: Arc<Mutex<HashSet<String>>>,
    }

    impl OneShotRecorder {
        fn enter(&self) {
            let thread_name = thread::current()
                .name()
                .map(str::to_string)
                .unwrap_or_else(|| format!("{:?}", thread::current().id()));
            self.threads.lock().unwrap().insert(thread_name);
            let in_flight = self.in_flight.fetch_add(1, Ordering::AcqRel) + 1;
            note_max(&self.max_in_flight, in_flight);
        }

        fn exit(&self) {
            self.in_flight.fetch_sub(1, Ordering::AcqRel);
        }

        fn max_in_flight(&self) -> usize {
            self.max_in_flight.load(Ordering::Acquire)
        }

        fn thread_count(&self) -> usize {
            self.threads.lock().unwrap().len()
        }
    }

    struct OneShotFrame {
        recorder: OneShotRecorder,
        sleep: StdDuration,
    }

    unsafe extern "C-unwind" fn one_shot_poll(frame: *mut u8, _ctx: *mut u8, _out: *mut u8) -> u8 {
        let frame = unsafe { &mut *(frame as *mut OneShotFrame) };
        frame.recorder.enter();
        thread::sleep(frame.sleep);
        frame.recorder.exit();
        1
    }

    unsafe extern "C" fn one_shot_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut OneShotFrame) };
    }

    fn run_one_shot_scheduler(task_count: usize, sleep: StdDuration) -> (usize, usize, u64) {
        let scheduler = Scheduler::new(false, 4);
        let recorder = OneShotRecorder {
            in_flight: Arc::new(AtomicUsize::new(0)),
            max_in_flight: Arc::new(AtomicUsize::new(0)),
            threads: Arc::new(Mutex::new(HashSet::new())),
        };

        for _ in 0..task_count {
            let frame = Box::new(OneShotFrame {
                recorder: recorder.clone(),
                sleep,
            });
            let handle = __rt__async_create(
                Box::into_raw(frame) as *mut u8,
                one_shot_poll as *const () as *const u8,
                one_shot_drop as *const () as *const u8,
                TaskMobility::Movable as u8,
            );
            let _ = scheduler.add_task(handle, ptr::null_mut(), None, 0, Some(0));
        }

        let local = scheduler.start();
        Arc::clone(&scheduler).worker_loop(0, local);
        scheduler.join_background_threads();
        (
            recorder.max_in_flight(),
            recorder.thread_count(),
            scheduler.stats.steals.load(Ordering::Relaxed),
        )
    }

    #[test]
    fn movable_work_executes_with_overlap() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let (max_in_flight, thread_count, _steals) =
            run_one_shot_scheduler(128, StdDuration::from_millis(8));
        assert!(
            max_in_flight > 1,
            "expected concurrent overlap across workers, observed max in-flight {max_in_flight}"
        );
        assert!(
            thread_count > 1,
            "expected work to run on multiple workers, observed {thread_count} worker thread(s)"
        );
    }

    #[test]
    fn victim_queue_steals_happen() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let (_max_in_flight, _thread_count, steals) =
            run_one_shot_scheduler(128, StdDuration::from_millis(8));
        assert!(steals > 0, "expected at least one victim-queue steal, observed {steals}");
    }

    struct GcGateFrame {
        entered: Arc<AtomicBool>,
        gate: Arc<(Mutex<bool>, Condvar)>,
    }

    unsafe extern "C-unwind" fn gc_gate_poll(frame: *mut u8, _ctx: *mut u8, _out: *mut u8) -> u8 {
        let frame = unsafe { &mut *(frame as *mut GcGateFrame) };
        frame.entered.store(true, Ordering::Release);
        let (lock, condvar) = &*frame.gate;
        let mut open = lock.lock().unwrap();
        while !*open {
            open = condvar.wait(open).unwrap();
        }
        1
    }

    unsafe extern "C" fn gc_gate_drop(frame: *mut u8) {
        let _ = unsafe { Box::from_raw(frame as *mut GcGateFrame) };
    }

    #[test]
    fn gc_waits_for_active_worker_then_resumes() {
        let _guard = TEST_ENV_LOCK.lock().unwrap();
        let scheduler = Scheduler::new(false, 2);
        let entered = Arc::new(AtomicBool::new(false));
        let gate = Arc::new((Mutex::new(false), Condvar::new()));
        let handle = __rt__async_create(
            Box::into_raw(Box::new(GcGateFrame {
                entered: Arc::clone(&entered),
                gate: Arc::clone(&gate),
            })) as *mut u8,
            gc_gate_poll as *const () as *const u8,
            gc_gate_drop as *const () as *const u8,
            TaskMobility::Movable as u8,
        );
        let _ = scheduler.add_task(handle, ptr::null_mut(), None, 0, Some(0));

        let local = scheduler.start();
        let worker_scheduler = Arc::clone(&scheduler);
        let worker0_join = thread::Builder::new()
            .name("taro-test-worker-0".into())
            .spawn(move || worker_scheduler.worker_thread_entry(0, local))
            .expect("failed to spawn worker 0 test thread");

        let deadline = Instant::now() + StdDuration::from_secs(1);
        while Instant::now() < deadline && !entered.load(Ordering::Acquire) {
            thread::yield_now();
        }
        assert!(
            entered.load(Ordering::Acquire),
            "blocking task never entered poll; GC rendezvous test did not start"
        );

        let (gc_done_tx, gc_done_rx) = mpsc::channel();
        let gc_join = thread::Builder::new()
            .name("taro-test-gc".into())
            .spawn(move || {
                crate::garbage_collector::__gc__thread_attach();
                crate::garbage_collector::__gc__collect();
                crate::garbage_collector::__gc__thread_detach();
                gc_done_tx.send(()).expect("failed to report GC completion");
            })
            .expect("failed to spawn GC thread");

        thread::sleep(StdDuration::from_millis(25));
        assert!(
            matches!(gc_done_rx.try_recv(), Err(mpsc::TryRecvError::Empty)),
            "GC completed while worker was still executing outside safepoint"
        );

        {
            let (lock, condvar) = &*gate;
            let mut open = lock.lock().unwrap();
            *open = true;
            condvar.notify_all();
        }

        gc_done_rx
            .recv_timeout(StdDuration::from_secs(2))
            .expect("GC did not resume/complete after worker reached safepoint");
        gc_join.join().expect("GC thread join failed");
        worker0_join.join().expect("worker 0 join failed");
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
                frame.child_ids.push(__rt__executor_spawn(handle, 0));
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
            if __rt__executor_poll_spawned(task_id, std::ptr::null_mut()) == 0 {
                all_done = false;
            } else {
                frame.child_done[index] = true;
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
        let visits = run_recording_root(TaskMobility::Movable);
        assert!(visits.values().any(|threads| threads.len() > 1));
    }

    #[test]
    fn pinned_tasks_stay_on_one_worker() {
        let visits = run_recording_root(TaskMobility::Pinned);
        assert!(visits.values().all(|threads| threads.len() == 1));
    }
}
