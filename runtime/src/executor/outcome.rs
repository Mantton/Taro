//! A spawned task's handle is one collected object shared by every copy of
//! its `Task` value. The object traces the task's result allocation and owns a
//! native outcome record. The executor publishes the terminal outcome into
//! that record after task cleanup finishes; observers copy the cached outcome
//! without consuming it, so repeated and concurrent observation see the same
//! result. Dropping or collecting handles never cancels the work, and a
//! retained handle keeps its outcome after its executor session ends.
use super::*;
use crate::garbage_collector::root_slots::RootLease;
use crate::garbage_collector::{__gc__alloc, GcDesc, with_gc};
use crate::gc_layout::{GC_LAYOUT_POINTER, GcLayoutNode};

#[derive(Clone)]
enum Outcome {
    Pending,
    Completed,
    Cancelled,
    Panicked(crate::panic_unwind::PanicReport),
}

/// A task blocked on another task's outcome, routed through its own executor.
#[derive(Clone)]
pub(crate) struct OutcomeWaiter {
    scheduler: Weak<Scheduler>,
    task: TaskToken,
}
impl OutcomeWaiter {
    fn current() -> Self {
        let scheduler = current_worker_scheduler().expect("task observed outside an executor");
        let task = current_task_token().expect("task observed with no current task");
        Self {
            scheduler: Arc::downgrade(&scheduler),
            task,
        }
    }
    fn same(&self, other: &Self) -> bool {
        self.task == other.task && Weak::ptr_eq(&self.scheduler, &other.scheduler)
    }
    fn wake_after_completion(&self) {
        if let Some(scheduler) = self.scheduler.upgrade() {
            // Publication happens after cleanup. The publishing worker is
            // returning to its queue, so a local continuation needs no peer
            // wake. Foreign executors and pinned observers keep normal routing.
            let worker = if crate::task::in_inline_poll() {
                None
            } else {
                WORKER_CONTEXT.with(|cell| {
                    let context = cell.try_borrow().ok()?;
                    let context = context.as_ref()?;
                    (context.current_task.is_none() && Arc::ptr_eq(&context.scheduler, &scheduler))
                        .then_some(context.worker_id)
                })
            };
            if let Some(worker) = worker {
                scheduler.schedule_tasks([WakeRequest {
                    task_token: self.task,
                    placement: Placement::Continuation(worker),
                }]);
            } else {
                scheduler.wake_tasks(&[self.task], false);
            }
        }
    }
    fn wake(&self) {
        if let Some(scheduler) = self.scheduler.upgrade() {
            scheduler.wake_tasks(&[self.task], false);
        }
    }
}

struct OutcomeState {
    outcome: Outcome,
    waiters: WaiterList,
    poll_waiters: WaiterList,
}

/// Nearly every task has one waiter at most, which needs no allocation.
#[derive(Default)]
struct WaiterList {
    first: Option<OutcomeWaiter>,
    rest: Vec<OutcomeWaiter>,
}
impl WaiterList {
    fn add_once(&mut self, waiter: &OutcomeWaiter) {
        match &self.first {
            None => self.first = Some(waiter.clone()),
            Some(first) if first.same(waiter) => {}
            Some(_) => {
                if !self.rest.iter().any(|existing| existing.same(waiter)) {
                    self.rest.push(waiter.clone());
                }
            }
        }
    }
    #[cfg(test)]
    fn len(&self) -> usize {
        usize::from(self.first.is_some()) + self.rest.len()
    }
    fn remove(&mut self, waiter: &OutcomeWaiter) {
        if self.first.as_ref().is_some_and(|first| first.same(waiter)) {
            self.first = (!self.rest.is_empty()).then(|| self.rest.remove(0));
        } else {
            self.rest.retain(|existing| !existing.same(waiter));
        }
    }
}
impl IntoIterator for WaiterList {
    type Item = OutcomeWaiter;
    type IntoIter =
        std::iter::Chain<std::option::IntoIter<OutcomeWaiter>, std::vec::IntoIter<OutcomeWaiter>>;
    fn into_iter(self) -> Self::IntoIter {
        self.first.into_iter().chain(self.rest)
    }
}

pub(crate) struct TaskShared {
    home: Weak<Scheduler>,
    task: TaskToken,
    output_size: usize,
    /// Set once the task has finished a poll. A timeout whose deadline has
    /// already passed gives the operation that first poll before expiring. Written
    /// under `state`, as no poll waiter can register once this is set.
    polled: AtomicBool,
    state: crate::hot_mutex::HotMutex<OutcomeState>,
}

impl TaskShared {
    fn new(home: &Arc<Scheduler>, task: TaskToken, output_size: usize) -> Self {
        Self {
            home: Arc::downgrade(home),
            task,
            output_size,
            polled: AtomicBool::new(false),
            state: crate::hot_mutex::HotMutex::new(OutcomeState {
                outcome: Outcome::Pending,
                waiters: WaiterList::default(),
                poll_waiters: WaiterList::default(),
            }),
        }
    }

    fn publish(&self, outcome: Outcome) {
        let wake = {
            let mut state = self.state.lock().unwrap();
            if !matches!(state.outcome, Outcome::Pending) {
                return;
            }
            state.outcome = outcome;
            (
                std::mem::take(&mut state.waiters),
                std::mem::take(&mut state.poll_waiters),
            )
        };
        for waiter in wake.0.into_iter().chain(wake.1) {
            waiter.wake_after_completion();
        }
    }
    pub(super) fn publish_completed(&self) {
        self.publish(Outcome::Completed);
    }
    pub(super) fn publish_cancelled(&self) {
        self.publish(Outcome::Cancelled);
    }
    pub(super) fn publish_panicked(&self, report: crate::panic_unwind::PanicReport) {
        self.publish(Outcome::Panicked(report));
    }

    /// After this, `finished_poll` has nothing left to do for any later poll.
    pub(super) fn has_finished_a_poll(&self) -> bool {
        self.polled.load(Ordering::Acquire)
    }

    pub(super) fn finished_poll(&self) {
        let wake = {
            let mut state = self.state.lock().unwrap();
            self.polled.store(true, Ordering::Release);
            std::mem::take(&mut state.poll_waiters)
        };
        for waiter in wake {
            waiter.wake();
        }
    }

    /// 0 = pending, 1 = completed, 2 = cancelled, 3 = panicked. Work whose
    /// executor ended without publishing an outcome reports cancellation.
    fn status_locked(&self, state: &OutcomeState) -> u8 {
        match state.outcome {
            Outcome::Pending if self.home.strong_count() == 0 => 2,
            Outcome::Pending => 0,
            Outcome::Completed => 1,
            Outcome::Cancelled => 2,
            Outcome::Panicked(_) => 3,
        }
    }
    fn status(&self) -> u8 {
        self.status_locked(&self.state.lock().unwrap())
    }

    /// Return the terminal status, or register `waiter` for publication.
    fn observe(&self, waiter: &OutcomeWaiter) -> u8 {
        let mut state = self.state.lock().unwrap();
        let status = self.status_locked(&state);
        if status == 0 {
            state.waiters.add_once(waiter);
        } else {
            state.waiters.remove(waiter);
        }
        status
    }
    /// Register `waiter` to be woken after the task's next finished poll.
    /// Returns true when a poll has already finished or the task is terminal.
    fn observe_poll(&self, waiter: &OutcomeWaiter) -> bool {
        let mut state = self.state.lock().unwrap();
        if self.polled.load(Ordering::Relaxed) || self.status_locked(&state) != 0 {
            return true;
        }
        state.poll_waiters.add_once(waiter);
        false
    }
    fn unregister(&self, waiter: &OutcomeWaiter) {
        let mut state = self.state.lock().unwrap();
        state.waiters.remove(waiter);
        state.poll_waiters.remove(waiter);
    }

    fn cancel(&self) {
        if self.status() != 0 {
            return;
        }
        if let Some(scheduler) = self.home.upgrade() {
            scheduler.cancel_task(self.task);
        }
    }

    /// Scope the task to the current task, when both share an executor: the
    /// current task's outcome then waits for this one to finish.
    fn scope_to_current_task(&self) {
        let (Some(scheduler), Some(parent)) = (self.home.upgrade(), current_task_token()) else {
            return;
        };
        if current_scheduler().is_some_and(|current| Arc::ptr_eq(&current, &scheduler)) {
            scheduler.adopt_scoped_child(parent, self.task);
        }
    }

    /// The observed task's queue token, when it shares the observer's executor.
    fn local_token(&self, waiter: &OutcomeWaiter) -> Option<TaskToken> {
        Weak::ptr_eq(&self.home, &waiter.scheduler).then_some(self.task)
    }
    fn wait_reason(&self, waiter: &OutcomeWaiter) -> WaitReason {
        self.local_token(waiter)
            .map_or(WaitReason::ForeignTask, WaitReason::Task)
    }
}

/// Collected handle object. `output` is a traced edge to the result storage;
/// `shared` is released by the collector once no handle can reach it.
#[repr(C)]
struct TaskObject {
    shared: *const TaskShared,
    output: *mut u8,
}
static TASK_OBJECT_NODES: [GcLayoutNode; 1] = [GcLayoutNode {
    offset: std::mem::offset_of!(TaskObject, output) as u64,
    stride: 0,
    first_child: 0,
    child_count: 0,
    kind: GC_LAYOUT_POINTER,
    width: 0,
    reserved: [0; 6],
}];
static TASK_OBJECT_DESC: GcDesc = GcDesc {
    size: std::mem::size_of::<TaskObject>(),
    align: std::mem::align_of::<TaskObject>(),
    nodes: TASK_OBJECT_NODES.as_ptr(),
    node_count: 1,
};
fn release_shared(shared: usize) {
    drop(unsafe { Arc::from_raw(shared as *const TaskShared) });
}

/// # Safety
/// object is a live task handle object returned by spawn.
unsafe fn shared_of(object: *mut u8) -> Arc<TaskShared> {
    if object.is_null() {
        crate::abi::invalid_metadata("null task handle");
    }
    let shared = unsafe { (*object.cast::<TaskObject>()).shared };
    unsafe {
        Arc::increment_strong_count(shared);
        Arc::from_raw(shared)
    }
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_spawn_with_metadata(
    handle: *mut u8,
    descriptor: *const u8,
    name: crate::panic_unwind::RtString,
    file: crate::panic_unwind::RtString,
    line: usize,
    column: usize,
) -> *mut u8 {
    // Root the handle object across scheduling: it is the only edge to the
    // result storage once the task completes and retires its slot's root.
    let object = __gc__alloc(TASK_OBJECT_DESC.size, &TASK_OBJECT_DESC);
    let root = RootLease::new(object.cast_const());
    let shared = super::spawn_shared_task(
        handle,
        descriptor,
        SpawnMetadata::from_runtime(name, file, line, column),
        |scheduler, task, output, output_size| {
            unsafe {
                object.cast::<TaskObject>().write(TaskObject {
                    shared: std::ptr::null(),
                    output,
                })
            };
            Arc::new(TaskShared::new(scheduler, task, output_size))
        },
    );
    let shared = Arc::into_raw(shared);
    unsafe { (*object.cast::<TaskObject>()).shared = shared };
    with_gc(|gc| gc.register_reclaimer(object.cast_const(), release_shared, shared as usize));
    // Nothing can collect between ending this lease and the object reaching its
    // caller.
    drop(root);
    object
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_cancel(object: *mut u8) {
    unsafe { shared_of(object) }.cancel();
}

/// Bind a spawned task handle to the currently running task so that early
/// termination (cancellation or panic) of the parent cancels the child and
/// defers publishing the parent's outcome until the child finishes.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_scope_to_current(object: *mut u8) {
    unsafe { shared_of(object) }.scope_to_current_task();
}

/// Terminal status of an observed task: 1 completed, 2 cancelled, 3 panicked.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__task_status(object: *mut u8) -> u8 {
    let status = unsafe { shared_of(object) }.status();
    assert_ne!(status, 0, "task status read before completion");
    status
}

/// Managed copy of a panicked task's payload, matching main's {data, len}
/// task-panic wire. Every observer receives its own immutable copy.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __gc__task_panic_payload(
    object: *mut u8,
) -> crate::panic_unwind::RtString {
    let shared = unsafe { shared_of(object) };
    let report = match &shared.state.lock().unwrap().outcome {
        Outcome::Panicked(report) => Some(report.clone()),
        _ => None,
    };
    let Some(report) = report else {
        return crate::panic_unwind::RtString {
            ptr: std::ptr::null(),
            len: 0,
        };
    };
    // No outcome lock is held while the allocation may park this worker.
    let bytes = crate::panic_unwind::serialize_panic_report(&report);
    crate::panic_unwind::RtString {
        ptr: unsafe { crate::gc_strings::__gc__string_copy(bytes.as_ptr(), bytes.len()) },
        len: bytes.len(),
    }
}

struct ResultFrame {
    object: *mut u8,
    shared: Arc<TaskShared>,
    waiter: Option<OutcomeWaiter>,
    _root: RootLease,
}
impl Drop for ResultFrame {
    fn drop(&mut self) {
        // An abandoned wait releases only this observer; the task keeps running.
        if let Some(waiter) = self.waiter.take() {
            self.shared.unregister(&waiter);
        }
    }
}

/// Returns 1 only when a T was copied out; 3 means terminal without a T. The
/// caller reads `__rt__task_status` after resuming.
unsafe extern "C-unwind" fn result_poll(frame: *mut u8, _: *mut u8, out: *mut u8) -> u8 {
    let frame = unsafe { &mut *frame.cast::<ResultFrame>() };
    // Results are mostly read once the task is known to be over, needing no waiter.
    if frame.waiter.is_none() {
        match frame.shared.status() {
            0 => {}
            1 => {
                let output = unsafe { (*frame.object.cast::<TaskObject>()).output };
                if !out.is_null() && frame.shared.output_size != 0 {
                    // An ordinary value copy: references inside keep their identity.
                    unsafe { std::ptr::copy_nonoverlapping(output, out, frame.shared.output_size) };
                }
                return 1;
            }
            _ => return 3,
        }
    }
    let waiter = OutcomeWaiter::current();
    match frame.shared.observe(&waiter) {
        0 => {
            set_current_wait_reason(frame.shared.wait_reason(&waiter));
            frame.waiter = Some(waiter);
            0
        }
        1 => {
            frame.waiter = None;
            let output = unsafe { (*frame.object.cast::<TaskObject>()).output };
            if !out.is_null() && frame.shared.output_size != 0 {
                // An ordinary value copy: references inside keep their identity.
                unsafe { std::ptr::copy_nonoverlapping(output, out, frame.shared.output_size) };
            }
            1
        }
        _ => {
            frame.waiter = None;
            3
        }
    }
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_task_result(object: *mut u8) -> *mut u8 {
    let shared = unsafe { shared_of(object) };
    // The wait copies from storage reachable only through the handle object.
    crate::task::create_inline_wait(
        ResultFrame {
            object,
            shared,
            waiter: None,
            _root: RootLease::new(object.cast_const()),
        },
        result_poll as *const u8,
        TaskMobility::Movable as u8,
    )
}

struct SelectionFrame {
    first: Arc<TaskShared>,
    second: Arc<TaskShared>,
    waiter: Option<OutcomeWaiter>,
}
impl SelectionFrame {
    fn finish(&mut self, out: *mut u8, winner: u8) -> u8 {
        if let Some(waiter) = self.waiter.take() {
            self.first.unregister(&waiter);
            self.second.unregister(&waiter);
        }
        if !out.is_null() {
            unsafe { out.write(winner) };
        }
        1
    }
}
impl Drop for SelectionFrame {
    fn drop(&mut self) {
        self.finish(std::ptr::null_mut(), 0);
    }
}

/// Neither outcome is consumed. The first task wins when both are terminal in
/// the same observation.
unsafe extern "C-unwind" fn selection_poll(frame: *mut u8, _: *mut u8, out: *mut u8) -> u8 {
    let frame = unsafe { &mut *frame.cast::<SelectionFrame>() };
    let waiter = OutcomeWaiter::current();
    frame.waiter = Some(waiter.clone());
    if frame.first.observe(&waiter) != 0 {
        return frame.finish(out, 0);
    }
    if frame.second.observe(&waiter) != 0 {
        // Recheck after registration closes the completion/register race.
        let winner = u8::from(frame.first.status() == 0);
        return frame.finish(out, winner);
    }
    set_current_wait_reason(
        match (
            frame.first.local_token(&waiter),
            frame.second.local_token(&waiter),
        ) {
            (Some(first), Some(second)) => WaitReason::Tasks([first, second]),
            _ => WaitReason::ForeignTask,
        },
    );
    0
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_select_tasks(first: *mut u8, second: *mut u8) -> *mut u8 {
    // select/race spawn both tasks for this wait: if the caller is cancelled
    // or panics before draining them, its outcome waits for both to finish.
    let first = unsafe { shared_of(first) };
    let second = unsafe { shared_of(second) };
    first.scope_to_current_task();
    second.scope_to_current_task();
    crate::task::create_inline_wait(
        SelectionFrame {
            first,
            second,
            waiter: None,
        },
        selection_poll as *const u8,
        TaskMobility::Movable as u8,
    )
}

struct MultiSelectionFrame {
    tasks: Vec<Arc<TaskShared>>,
    held: Vec<bool>,
    waiter: Option<OutcomeWaiter>,
}

impl MultiSelectionFrame {
    fn release_unpolled_held(&mut self, cancel_first: bool) {
        for (task, held) in self.tasks.iter().zip(self.held.iter_mut()) {
            if std::mem::replace(held, false) {
                if cancel_first {
                    task.cancel();
                }
                if let Some(scheduler) = task.home.upgrade() {
                    scheduler.release_held_spawn(task.task);
                }
            }
        }
    }

    fn finish(&mut self, out: *mut u8, winner: usize) -> u8 {
        self.release_unpolled_held(true);
        if let Some(waiter) = self.waiter.take() {
            for task in &self.tasks {
                task.unregister(&waiter);
            }
        }
        if !out.is_null() {
            unsafe { out.cast::<usize>().write(winner) };
        }
        1
    }
}

impl Drop for MultiSelectionFrame {
    fn drop(&mut self) {
        self.finish(std::ptr::null_mut(), 0);
    }
}

/// Neither outcome is consumed. Held arms are polled inline in source order on
/// the first observation so already-ready arms deterministically win in source
/// order without racing across workers.
unsafe extern "C-unwind" fn multi_selection_poll(frame: *mut u8, _: *mut u8, out: *mut u8) -> u8 {
    let frame = unsafe { &mut *frame.cast::<MultiSelectionFrame>() };
    if frame.held.iter().any(|&h| h) {
        let scheduler = current_worker_scheduler().expect("select polled by an executor");
        for idx in 0..frame.tasks.len() {
            if !std::mem::replace(&mut frame.held[idx], false) {
                continue;
            }
            let task = &frame.tasks[idx];
            let local = std::ptr::eq(task.home.as_ptr(), Arc::as_ptr(&scheduler));
            if local && scheduler.poll_spawned_inline(task.task) {
                if task.status() != 0 {
                    return frame.finish(out, idx);
                }
            } else if let Some(home) = task.home.upgrade() {
                home.release_held_spawn(task.task);
            }
        }
    }
    let waiter = OutcomeWaiter::current();
    frame.waiter = Some(waiter.clone());
    for (idx, task) in frame.tasks.iter().enumerate() {
        if task.observe(&waiter) != 0 {
            for (earlier_idx, earlier) in frame.tasks[..idx].iter().enumerate() {
                if earlier.status() != 0 {
                    return frame.finish(out, earlier_idx);
                }
            }
            return frame.finish(out, idx);
        }
    }
    let reason = match (
        frame.tasks.first().and_then(|t| t.local_token(&waiter)),
        frame.tasks.get(1).and_then(|t| t.local_token(&waiter)),
    ) {
        (Some(first), Some(second)) => WaitReason::Tasks([first, second]),
        (Some(first), None) => WaitReason::Task(first),
        _ => WaitReason::ForeignTask,
    };
    set_current_wait_reason(reason);
    0
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_select_many(tasks_ptr: *const u8, count: usize) -> *mut u8 {
    assert!(count > 0, "select requires at least one arm");
    let slice = unsafe { std::slice::from_raw_parts(tasks_ptr.cast::<*mut u8>(), count) };
    let mut tasks = Vec::with_capacity(count);
    let mut held = Vec::with_capacity(count);
    for &handle in slice {
        let shared = unsafe { shared_of(handle) };
        shared.scope_to_current_task();
        let is_held = crate::task::claim_held_spawn(shared.task);
        tasks.push(shared);
        held.push(is_held);
    }
    crate::task::create_inline_wait(
        MultiSelectionFrame {
            tasks,
            held,
            waiter: None,
        },
        multi_selection_poll as *const u8,
        TaskMobility::Movable as u8,
    )
}

struct TimeoutFrame {
    shared: Arc<TaskShared>,
    deadline: Instant,
    short: bool,
    // The operation, spawned for this wait and in no queue until its first poll.
    held: Option<TaskToken>,
    waiter: Option<OutcomeWaiter>,
    armed: bool,
}
impl TimeoutFrame {
    fn finish(&mut self, out: *mut u8, winner: u8) -> u8 {
        if let Some(waiter) = self.waiter.take() {
            self.shared.unregister(&waiter);
            if let Some(scheduler) = waiter.scheduler.upgrade() {
                scheduler.clear_task_timer(waiter.task);
            }
        }
        if !out.is_null() {
            unsafe { out.write(winner) };
        }
        1
    }
}
impl Drop for TimeoutFrame {
    fn drop(&mut self) {
        // A cancelled caller can destroy this wait without ever polling it.
        if let (Some(held), Some(scheduler)) = (self.held.take(), self.shared.home.upgrade()) {
            self.shared.scope_to_current_task();
            scheduler.release_held_spawn(held);
        }
        self.finish(std::ptr::null_mut(), 0);
    }
}

/// An already-expired initial deadline waits for the operation's first poll
/// to finish, so immediately-ready work wins independently of queue priority.
/// Later observations check the task before the deadline.
unsafe extern "C-unwind" fn timeout_poll(frame: *mut u8, _: *mut u8, out: *mut u8) -> u8 {
    let frame = unsafe { &mut *frame.cast::<TimeoutFrame>() };
    let mut initial = !frame.armed;
    frame.armed = true;
    // The operation was only just spawned, usually needs no waiting, and this
    // task has nothing to do but wait for it, so let it start right away. If it
    // then waits, its first poll is over and this is a normal timeout from here.
    // Only a timeout too long to expire meanwhile can defer starting its timer.
    if let Some(held) = frame.held.take() {
        let scheduler = current_worker_scheduler().expect("timeout polled by an executor");
        let local = std::ptr::eq(frame.shared.home.as_ptr(), Arc::as_ptr(&scheduler));
        if local && frame.shared.task == held && scheduler.poll_spawned_inline(held) {
            initial = false;
            // This task couldn't finish with its operation running on top of it.
            // One that is already over needs no link, waiter or timer.
            if frame.shared.status() != 0 {
                return frame.finish(out, 0);
            }
            frame.shared.scope_to_current_task();
        } else {
            frame.shared.scope_to_current_task();
            scheduler.release_held_spawn(held);
        }
    }
    let waiter = OutcomeWaiter::current();
    frame.waiter = Some(waiter.clone());
    let scheduler = waiter
        .scheduler
        .upgrade()
        .expect("timeout polled by a live executor");
    let local_task = frame.shared.local_token(&waiter);
    if frame.shared.observe(&waiter) != 0 {
        return frame.finish(out, 0);
    }
    let reason = match local_task {
        Some(task) => WaitReason::TaskTimeout {
            task,
            deadline: frame.deadline,
        },
        None => WaitReason::Sleep(frame.deadline),
    };
    // Otherwise requeue once behind it, instead of paying for a timer it would
    // then cancel.
    if initial && !frame.short {
        return 0;
    }
    if initial && frame.short && Instant::now() >= frame.deadline {
        if frame.shared.observe_poll(&waiter) {
            scheduler.wake_tasks(&[waiter.task], false);
        }
        set_current_wait_reason(reason);
        return 0;
    }
    scheduler.register_sleep(waiter.task, frame.deadline);
    if !initial && Instant::now() >= frame.deadline {
        return frame.finish(out, 1);
    }
    set_current_wait_reason(reason);
    0
}
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_task_timeout(
    object: *mut u8,
    secs: u64,
    nanos: u32,
) -> *mut u8 {
    let shared = unsafe { shared_of(object) };
    let release_held = |held: Option<TaskToken>| {
        if let (Some(held), Some(scheduler)) = (held, shared.home.upgrade()) {
            scheduler.release_held_spawn(held);
        }
    };
    let mut held = crate::task::take_held_spawn();
    let Some(deadline) = Instant::now().checked_add(StdDuration::new(secs, nanos)) else {
        release_held(held);
        panic!("timeout duration overflow");
    };
    let short = secs == 0;
    // A short timeout runs its operation through the queues, as it has to let
    // that operation's first poll finish under whatever deadline remains.
    if short {
        release_held(held.take());
    }
    // withTimeout spawns the operation for this wait; scope it like select. A held
    // operation is scoped once its first poll shows that it needs to be.
    if held.is_none() {
        shared.scope_to_current_task();
    }
    crate::task::create_inline_wait(
        TimeoutFrame {
            shared,
            deadline,
            // Reading the clock again is only worthwhile if the deadline can have
            // passed already, which would take a stall of over a second here.
            short,
            held,
            waiter: None,
            armed: false,
        },
        timeout_poll as *const u8,
        TaskMobility::Movable as u8,
    )
}

/// Give an already-prepared task a handle object, as spawn does. The object
/// stays rooted for the rest of the process so Rust tests cannot lose it to a
/// concurrent test's collection.
#[cfg(test)]
pub(super) fn attach_test_handle(
    scheduler: &Arc<Scheduler>,
    task: TaskToken,
    output: *mut u8,
    output_size: usize,
) -> *mut u8 {
    let object = __gc__alloc(TASK_OBJECT_DESC.size, &TASK_OBJECT_DESC);
    with_gc(|gc| gc.add_persistent_root(object.cast_const()));
    let shared = Arc::new(TaskShared::new(scheduler, task, output_size));
    let raw = Arc::into_raw(Arc::clone(&shared));
    unsafe {
        object.cast::<TaskObject>().write(TaskObject {
            shared: raw,
            output,
        })
    };
    with_gc(|gc| gc.register_reclaimer(object.cast_const(), release_shared, raw as usize));
    let (index, _) = unpack_task_token(task);
    let slot = scheduler
        .lookup_task_slot(index)
        .expect("prepared task slot");
    let mut inner = slot.inner.lock().unwrap();
    inner.shared = Some(shared);
    inner.detached = true;
    object
}

/// Observe a handle from the current task: 0 registers a waiter, 1 copies
/// the completed result into `out`, 2 and 3 report cancellation and panic.
#[cfg(test)]
pub(super) fn poll_test_task(object: *mut u8, out: *mut u8) -> u8 {
    let shared = unsafe { shared_of(object) };
    let waiter = OutcomeWaiter::current();
    let status = shared.observe(&waiter);
    if status == 0 {
        set_current_wait_reason(shared.wait_reason(&waiter));
    }
    if status == 1 && !out.is_null() && shared.output_size != 0 {
        let output = unsafe { (*object.cast::<TaskObject>()).output };
        unsafe { std::ptr::copy_nonoverlapping(output, out, shared.output_size) };
    }
    status
}

#[cfg(test)]
pub(super) fn test_waiter_count(object: *mut u8) -> usize {
    let shared = unsafe { shared_of(object) };
    let state = shared.state.lock().unwrap();
    state.waiters.len() + state.poll_waiters.len()
}

#[cfg(test)]
mod tests {
    fn listed_waiter(task: TaskToken) -> OutcomeWaiter {
        OutcomeWaiter {
            scheduler: Weak::new(),
            task,
        }
    }
    fn listed_tasks(list: WaiterList) -> Vec<TaskToken> {
        list.into_iter().map(|waiter| waiter.task).collect()
    }

    #[test]
    fn waiter_list_keeps_each_waiter_once_in_arrival_order() {
        let mut list = WaiterList::default();
        for task in [1, 2, 1, 3, 2, 1] {
            list.add_once(&listed_waiter(task));
        }
        assert_eq!(list.len(), 3);
        assert_eq!(listed_tasks(list), [1, 2, 3]);
    }

    #[test]
    fn removing_a_waiter_keeps_the_others_in_order() {
        let list = || {
            let mut list = WaiterList::default();
            for task in [1, 2, 3] {
                list.add_once(&listed_waiter(task));
            }
            list
        };
        for (removed, expected) in [(1, [2, 3]), (2, [1, 3]), (3, [1, 2])] {
            let mut list = list();
            list.remove(&listed_waiter(removed));
            list.remove(&listed_waiter(99));
            assert_eq!(listed_tasks(list), expected);
        }
        let mut last = WaiterList::default();
        last.add_once(&listed_waiter(1));
        last.remove(&listed_waiter(1));
        assert_eq!(last.len(), 0);
        last.add_once(&listed_waiter(2));
        assert_eq!(listed_tasks(last), [2]);
    }

    use super::*;
    use std::ptr;

    fn context(scheduler: &Arc<Scheduler>, current_task: TaskToken) -> WorkerContextGuard {
        WORKER_CONTEXT.with(|cell| {
            cell.replace(Some(WorkerContext {
                scheduler: scheduler.clone(),
                worker_id: 0,
                current_task: Some(current_task),
                current_wait_reason: None,
                current_cancellation: None,
            }))
        });
        WorkerContextGuard
    }
    fn spawned(scheduler: &Arc<Scheduler>) -> (TaskToken, *mut u8) {
        let task = scheduler.add_task(
            ptr::null_mut(),
            ptr::null_mut(),
            Some(TaskOutput::empty()),
            0,
            None,
            true,
        );
        (
            task,
            attach_test_handle(scheduler, task, ptr::null_mut(), 0),
        )
    }
    fn waiter(scheduler: &Arc<Scheduler>) -> TaskToken {
        scheduler.add_task(ptr::null_mut(), ptr::null_mut(), None, 0, None, false)
    }
    fn poll_byte(handle: *mut u8) -> (u8, u8) {
        let mut out = u8::MAX;
        let status = crate::task::__rt__async_poll(handle, &raw mut out);
        (status, out)
    }

    #[test]
    fn terminal_outcome_continues_locally_without_migrating_pinned_waiters() {
        let scheduler = Scheduler::new(false, 2);
        for (owner, mobility) in [
            (1, TaskMobility::Movable),
            (1, TaskMobility::Pinned),
            (0, TaskMobility::Movable),
        ] {
            scheduler.push_task_slot(Arc::new(TaskSlot::new(
                TASK_INITIAL_GENERATION,
                ptr::null_mut(),
                ptr::null_mut(),
                None,
                owner,
                mobility,
            )));
        }
        let token = |index| pack_task_token(index, TASK_INITIAL_GENERATION);
        let _context = context(&scheduler, token(2));
        // run_task clears the current task after the poll, before publishing.
        WORKER_CONTEXT.with(|cell| cell.borrow_mut().as_mut().unwrap().current_task = None);
        scheduler.worker_polling[0].store(true, Ordering::Release);
        let shared = TaskShared::new(&scheduler, token(2), 0);
        for index in 0..2 {
            assert_eq!(
                shared.observe(&OutcomeWaiter {
                    scheduler: Arc::downgrade(&scheduler),
                    task: token(index),
                }),
                0
            );
        }
        shared.publish_completed();
        assert_eq!(scheduler.remote_queues[0].pop_front(), Some(token(0)));
        assert_eq!(scheduler.pinned_queues[1].pop_front(), Some(token(1)));
        assert!(scheduler.remote_queues[1].is_empty());

        // A publication during somebody else's active poll cannot assume that
        // poll is about to return; preserve the ordinary peer-routing policy.
        WORKER_CONTEXT
            .with(|cell| cell.borrow_mut().as_mut().unwrap().current_task = Some(token(2)));
        scheduler
            .lookup_task_slot(0)
            .unwrap()
            .inner
            .lock()
            .unwrap()
            .queued = false;
        let another = TaskShared::new(&scheduler, token(2), 0);
        assert_eq!(
            another.observe(&OutcomeWaiter {
                scheduler: Arc::downgrade(&scheduler),
                task: token(0),
            }),
            0
        );
        another.publish_completed();
        assert_eq!(scheduler.remote_queues[1].pop_front(), Some(token(0)));
        assert!(scheduler.remote_queues[0].is_empty());

        // Native wait registration may hold the worker context during a wake.
        // Fall back instead of trying to reborrow that context or panicking.
        scheduler
            .lookup_task_slot(0)
            .unwrap()
            .inner
            .lock()
            .unwrap()
            .queued = false;
        let borrowed = TaskShared::new(&scheduler, token(2), 0);
        assert_eq!(
            borrowed.observe(&OutcomeWaiter {
                scheduler: Arc::downgrade(&scheduler),
                task: token(0),
            }),
            0
        );
        WORKER_CONTEXT.with(|cell| {
            let _borrow = cell.borrow_mut();
            borrowed.publish_completed();
        });
        assert_eq!(scheduler.remote_queues[1].pop_front(), Some(token(0)));
    }

    #[test]
    fn an_inline_poll_runs_as_the_spawned_task_and_restores_the_caller() {
        let scheduler = Scheduler::new(false, 1);
        let (task, operation) = spawned(&scheduler);
        let caller = waiter(&scheduler);
        let _context = context(&scheduler, caller);
        let flag = Arc::new(AtomicBool::new(false));
        WORKER_CONTEXT.with(|cell| {
            cell.borrow_mut().as_mut().unwrap().current_cancellation = Some(flag.clone());
        });
        crate::task::set_polled_cancellation(Arc::as_ptr(&flag));
        let current = || {
            WORKER_CONTEXT.with(|cell| {
                let context = cell.borrow();
                let context = context.as_ref().unwrap();
                (context.current_task, context.current_cancellation.clone())
            })
        };

        assert!(scheduler.poll_spawned_inline(task));
        assert_eq!(
            scheduler.yielded[0].polls.load(Ordering::Relaxed),
            0,
            "an inline child does not service another queued turn"
        );
        let (restored, cancellation) = current();
        assert_eq!(restored, Some(caller));
        assert!(Arc::ptr_eq(&cancellation.unwrap(), &flag));
        assert_eq!(crate::task::polled_task_cancelled(), Some(false));
        assert!(scheduler.worker_polling[0].load(Ordering::Acquire));
        assert!(!crate::task::in_inline_poll());
        assert_eq!(unsafe { shared_of(operation) }.status(), 1);

        // Never from within another inline poll, nor for a cancelled caller.
        let (second, second_handle) = spawned(&scheduler);
        crate::task::set_inline_poll(true);
        assert!(!scheduler.poll_spawned_inline(second));
        crate::task::set_inline_poll(false);
        flag.store(true, Ordering::Release);
        assert!(!scheduler.poll_spawned_inline(second));
        assert_eq!(unsafe { shared_of(second_handle) }.status(), 0);
        crate::task::set_polled_cancellation(ptr::null());
    }

    fn held_spawn_is_queued(scheduler: &Arc<Scheduler>, task: TaskToken) -> bool {
        let (index, _) = unpack_task_token(task);
        let slot = scheduler.lookup_task_slot(index).unwrap();
        slot.inner.lock().unwrap().queued
    }

    #[test]
    fn releasing_a_held_spawn_queues_it_once_and_ignores_anything_stale() {
        let scheduler = Scheduler::new(false, 1);
        let (task, _) = spawned(&scheduler);
        // `spawned` queues it, and a held spawn has that same flag set. Releasing
        // goes back through the ordinary enqueue, which sets it again.
        assert!(held_spawn_is_queued(&scheduler, task));
        scheduler.release_held_spawn(task);
        assert!(held_spawn_is_queued(&scheduler, task));
        scheduler.complete_task(task);
        scheduler.release_held_spawn(task);
    }

    #[test]
    fn a_held_spawn_is_claimed_once_and_the_end_of_a_poll_clears_it() {
        crate::task::__rt__task_hold_next_spawn();
        assert!(crate::task::take_hold_next_spawn());
        assert!(!crate::task::take_hold_next_spawn());
        crate::task::set_held_spawn(7);
        assert_eq!(crate::task::take_held_spawn(), Some(7));
        assert_eq!(crate::task::take_held_spawn(), None);
        crate::task::__rt__task_hold_next_spawn();
        crate::task::set_held_spawn(9);
        assert_eq!(crate::task::end_poll_holds(), Some(9));
        assert!(!crate::task::take_hold_next_spawn());
        assert_eq!(crate::task::end_poll_holds(), None);
    }

    #[test]
    fn scope_links_are_counted_until_their_child_publishes() {
        let scheduler = Scheduler::new(false, 1);
        let (child, _) = spawned(&scheduler);
        let parent = waiter(&scheduler);
        let count = |scheduler: &Arc<Scheduler>| scheduler.scope_link_count.load(Ordering::SeqCst);
        assert_eq!(count(&scheduler), 0);
        scheduler.adopt_scoped_child(parent, child);
        scheduler.adopt_scoped_child(parent, child);
        assert_eq!(count(&scheduler), 1, "adopting twice links once");
        scheduler.complete_task(child);
        assert_eq!(count(&scheduler), 0);
        assert!(scheduler.scope_links.lock().unwrap().parent.is_empty());
        assert!(scheduler.scope_links.lock().unwrap().children.is_empty());
        // Finished already: there's nothing to wait for, so no link is left behind.
        scheduler.adopt_scoped_child(parent, child);
        assert_eq!(count(&scheduler), 0);
    }

    #[test]
    fn a_parent_with_a_linked_child_waits_for_it_to_publish() {
        let scheduler = Scheduler::new(false, 1);
        let (child, child_handle) = spawned(&scheduler);
        let (parent, parent_handle) = spawned(&scheduler);
        scheduler.adopt_scoped_child(parent, child);
        scheduler.complete_task(parent);
        assert_eq!(unsafe { shared_of(parent_handle) }.status(), 0);
        scheduler.complete_task(child);
        assert_eq!(unsafe { shared_of(child_handle) }.status(), 1);
        assert_eq!(unsafe { shared_of(parent_handle) }.status(), 1);
        assert_eq!(scheduler.scope_link_count.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn only_the_first_finished_poll_has_waiters_to_wake() {
        let scheduler = Scheduler::new(false, 1);
        let (_, operation) = spawned(&scheduler);
        let shared = unsafe { shared_of(operation) };
        let caller = waiter(&scheduler);
        let _context = context(&scheduler, caller);
        let observer = OutcomeWaiter::current();
        assert!(!shared.has_finished_a_poll());
        assert!(!shared.observe_poll(&observer));
        shared.finished_poll();
        assert!(shared.has_finished_a_poll());
        // No waiter can join now, which is what lets later polls skip this.
        assert!(shared.observe_poll(&observer));
        assert_eq!(shared.state.lock().unwrap().poll_waiters.len(), 0);
    }

    #[test]
    fn selection_prefers_the_first_terminal_task_and_clears_waiters() {
        let scheduler = Scheduler::new(false, 1);
        let (first_task, first) = spawned(&scheduler);
        let (second_task, second) = spawned(&scheduler);
        let _context = context(&scheduler, waiter(&scheduler));
        let selection = __rt__async_select_tasks(first, second);
        assert_eq!(poll_byte(selection).0, 0);
        assert_eq!(
            (test_waiter_count(first), test_waiter_count(second)),
            (1, 1)
        );
        scheduler.complete_task(second_task);
        scheduler.complete_task(first_task);
        assert_eq!(poll_byte(selection), (1, 0));
        crate::task::__rt__async_destroy(selection);
        assert_eq!(
            (test_waiter_count(first), test_waiter_count(second)),
            (0, 0)
        );
    }

    #[test]
    fn abandoned_selection_unregisters_both_waiters() {
        let scheduler = Scheduler::new(false, 1);
        let (_, first) = spawned(&scheduler);
        let (_, second) = spawned(&scheduler);
        let _context = context(&scheduler, waiter(&scheduler));
        let selection = __rt__async_select_tasks(first, second);
        assert_eq!(poll_byte(selection).0, 0);
        crate::task::__rt__async_cancel(selection);
        assert_eq!(
            (test_waiter_count(first), test_waiter_count(second)),
            (0, 0)
        );
    }

    #[test]
    fn zero_duration_timeout_yields_once_then_expires_and_unregisters() {
        let scheduler = Scheduler::new(false, 1);
        let (task, operation) = spawned(&scheduler);
        let current = waiter(&scheduler);
        let _context = context(&scheduler, current);
        let timeout = __rt__async_task_timeout(operation, 0, 0);
        assert_eq!(poll_byte(timeout).0, 0);
        assert_eq!(test_waiter_count(operation), 2);
        // The operation's first finished poll ends the grace turn.
        let (index, _) = unpack_task_token(task);
        let shared = scheduler
            .lookup_task_slot(index)
            .unwrap()
            .inner
            .lock()
            .unwrap()
            .shared
            .clone();
        shared.unwrap().finished_poll();
        assert_eq!(poll_byte(timeout), (1, 1));
        crate::task::__rt__async_destroy(timeout);
        assert_eq!(test_waiter_count(operation), 0);
        let (waiter_index, _) = unpack_task_token(current);
        assert!(scheduler.timers.lock().unwrap().latest[waiter_index].is_none());
    }

    #[test]
    fn ready_operation_wins_an_expired_timeout() {
        let scheduler = Scheduler::new(false, 1);
        let (task, operation) = spawned(&scheduler);
        let _context = context(&scheduler, waiter(&scheduler));
        let timeout = __rt__async_task_timeout(operation, 0, 0);
        assert_eq!(poll_byte(timeout).0, 0);
        scheduler.complete_task(task);
        assert_eq!(poll_byte(timeout), (1, 0));
        crate::task::__rt__async_destroy(timeout);
    }

    #[test]
    fn publication_wakes_every_waiter_and_abandoning_one_keeps_the_task_running() {
        let scheduler = Scheduler::new(false, 1);
        let (task, handle) = spawned(&scheduler);
        let (first, second) = (waiter(&scheduler), waiter(&scheduler));
        let mut waits = Vec::new();
        for current in [first, second] {
            let _context = context(&scheduler, current);
            let wait = __rt__async_task_result(handle);
            assert_eq!(crate::task::__rt__async_poll(wait, ptr::null_mut()), 0);
            waits.push(wait);
        }
        assert_eq!(test_waiter_count(handle), 2);
        crate::task::__rt__async_cancel(waits.remove(0));
        assert_eq!(test_waiter_count(handle), 1);
        let (index, _) = unpack_task_token(task);
        assert!(
            !scheduler
                .lookup_task_slot(index)
                .unwrap()
                .inner
                .lock()
                .unwrap()
                .cancelled
                .load(Ordering::Acquire),
            "abandoning one observer must not cancel the task"
        );
        for current in [first, second] {
            let (index, _) = unpack_task_token(current);
            scheduler
                .lookup_task_slot(index)
                .unwrap()
                .inner
                .lock()
                .unwrap()
                .queued = false;
        }
        scheduler.complete_task(task);
        let (second_index, _) = unpack_task_token(second);
        assert!(
            scheduler
                .lookup_task_slot(second_index)
                .unwrap()
                .inner
                .lock()
                .unwrap()
                .queued
        );
        let _context = context(&scheduler, second);
        assert_eq!(crate::task::__rt__async_poll(waits[0], ptr::null_mut()), 1);
        crate::task::__rt__async_destroy(waits.remove(0));
        assert_eq!(__rt__task_status(handle), 1);
    }

    #[test]
    fn retained_outcome_survives_its_executor_session() {
        let original = Scheduler::new(false, 1);
        let mut output = unsafe {
            TaskOutput::new(crate::test_layout::noscan(
                size_of::<usize>(),
                align_of::<usize>(),
            ))
        };
        let storage = output.as_mut_ptr();
        let task = original.add_task(ptr::null_mut(), storage, Some(output), 0, None, true);
        let handle = attach_test_handle(&original, task, storage, size_of::<usize>());
        let (pending_task, pending) = spawned(&original);
        let _ = pending_task;
        unsafe { storage.cast::<usize>().write(41) };
        original.complete_task(task);
        drop(original);

        let later = Scheduler::new(false, 1);
        let _context = context(&later, waiter(&later));
        for _ in 0..2 {
            let mut value = 0usize;
            assert_eq!(poll_test_task(handle, (&raw mut value).cast()), 1);
            assert_eq!(value, 41);
        }
        // Work its session never finished reports cancellation.
        assert_eq!(poll_test_task(pending, ptr::null_mut()), 2);
    }
}
