//! Deferred execution for public GC cleanup callbacks.
//!
//! Sweep only transfers rooted async handles into this queue. A dedicated,
//! GC-aware worker invokes the compiler-generated synchronous adapters after
//! the stop-the-world pause has ended.

use std::collections::VecDeque;
use std::sync::{Condvar, Mutex, OnceLock};
use std::thread;

use crate::garbage_collector::{CleanupRegistration, with_gc};
use crate::task::{__rt__async_destroy, __rt__async_poll};

pub(crate) const REGISTER_NOT_MANAGED: usize = 0;
pub(crate) const REGISTER_OWNER_RETAINED: usize = 1;

#[derive(Default)]
struct QueueState {
    handles: VecDeque<usize>,
    active: usize,
    queued_total: u64,
    executed_total: u64,
    cancelled_total: u64,
    panicked_total: u64,
    peak_pending: usize,
}

struct CleanupQueue {
    state: Mutex<QueueState>,
    work_available: Condvar,
    idle: Condvar,
}

impl CleanupQueue {
    fn new() -> Self {
        Self {
            state: Mutex::new(QueueState::default()),
            work_available: Condvar::new(),
            idle: Condvar::new(),
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct CleanupStatsSnapshot {
    pub queued: u64,
    pub executed: u64,
    pub cancelled: u64,
    pub panicked: u64,
    pub pending: usize,
    pub peak_pending: usize,
}

fn queue() -> &'static CleanupQueue {
    static QUEUE: OnceLock<CleanupQueue> = OnceLock::new();
    QUEUE.get_or_init(CleanupQueue::new)
}

fn ensure_worker() {
    static WORKER: OnceLock<()> = OnceLock::new();
    WORKER.get_or_init(|| {
        thread::Builder::new()
            .name("taro-cleanup".into())
            .spawn(cleanup_worker_loop)
            .expect("failed to spawn runtime cleanup worker");
    });
}

pub(crate) fn enqueue(handles: Vec<usize>) {
    if handles.is_empty() {
        return;
    }

    let queue = queue();
    {
        let mut state = queue.state.lock().unwrap();
        state.queued_total = state.queued_total.saturating_add(handles.len() as u64);
        state.handles.extend(handles);
        let pending = state.handles.len().saturating_add(state.active);
        state.peak_pending = state.peak_pending.max(pending);
    }
    ensure_worker();
    queue.work_available.notify_one();
}

fn cleanup_worker_loop() {
    crate::garbage_collector::__gc__thread_attach();
    loop {
        let handle = {
            let queue = queue();
            let mut state = queue.state.lock().unwrap();
            while state.handles.is_empty() {
                state = queue.work_available.wait(state).unwrap();
            }
            let handle = state
                .handles
                .pop_front()
                .expect("cleanup queue became empty while locked");
            state.active = state.active.saturating_add(1);
            handle
        };

        crate::garbage_collector::leave_safepoint();
        let panicked = execute_cleanup(handle as *mut u8);
        crate::garbage_collector::enter_safepoint();

        let queue = queue();
        let mut state = queue.state.lock().unwrap();
        state.active = state.active.saturating_sub(1);
        state.executed_total = state.executed_total.saturating_add(1);
        if panicked {
            state.panicked_total = state.panicked_total.saturating_add(1);
        }
        if state.handles.is_empty() && state.active == 0 {
            queue.idle.notify_all();
        }
    }
}

fn execute_cleanup(handle: *mut u8) -> bool {
    let result = crate::panic_unwind::catch_executor_panic(|| {
        let status = __rt__async_poll(handle, std::ptr::null_mut());
        if status == 0 {
            crate::panic_unwind::write_cleanup_warning(
                "cleanup callback suspended; cleanup callbacks must be synchronous",
            );
        }
    });
    __rt__async_destroy(handle);

    match result {
        Ok(()) => false,
        Err(report) => {
            crate::panic_unwind::write_unobserved_cleanup_panic(&report);
            true
        }
    }
}

pub(crate) fn record_cancelled() {
    let mut state = queue().state.lock().unwrap();
    state.cancelled_total = state.cancelled_total.saturating_add(1);
}

pub(crate) fn stats_snapshot() -> CleanupStatsSnapshot {
    let state = queue().state.lock().unwrap();
    CleanupStatsSnapshot {
        queued: state.queued_total,
        executed: state.executed_total,
        cancelled: state.cancelled_total,
        panicked: state.panicked_total,
        pending: state.handles.len().saturating_add(state.active),
        peak_pending: state.peak_pending,
    }
}

fn wait_until_idle() {
    let queue = queue();
    let mut state = queue.state.lock().unwrap();
    while !state.handles.is_empty() || state.active != 0 {
        state = queue.idle.wait(state).unwrap();
    }
}

/// Register a compiler-generated cleanup adapter. The runtime takes ownership
/// of `handle` on every return path.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__cleanup_register(owner: *const u8, handle: *mut u8) -> usize {
    let frame = crate::task::async_handle_frame(handle);
    let registration = with_gc(|gc| gc.register_cleanup(owner, frame, handle));
    match registration {
        CleanupRegistration::Registered(token) => token,
        CleanupRegistration::NotManaged => {
            __rt__async_destroy(handle);
            REGISTER_NOT_MANAGED
        }
        CleanupRegistration::OwnerRetained => {
            __rt__async_destroy(handle);
            REGISTER_OWNER_RETAINED
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__cleanup_cancel(token: usize) -> bool {
    let handle = with_gc(|gc| gc.cancel_cleanup(token));
    let Some(handle) = handle else {
        return false;
    };
    __rt__async_destroy(handle as *mut u8);
    record_cancelled();
    true
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__cleanup_wait() {
    // The waiting thread must not prevent a callback from initiating a
    // collection. This mirrors other blocking runtime waits: publish a stable
    // shadow stack, then resume ordinary mutator execution before returning.
    crate::garbage_collector::enter_safepoint();
    wait_until_idle();
    crate::garbage_collector::leave_safepoint();
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__keep_alive(value: *const u8) {
    std::hint::black_box(value);
}

#[cfg(test)]
mod tests {
    use super::{CleanupStatsSnapshot, QueueState};

    #[test]
    fn cleanup_stats_count_pending_and_peak_work() {
        let state = QueueState {
            handles: [11, 12].into_iter().collect(),
            active: 1,
            queued_total: 5,
            executed_total: 2,
            cancelled_total: 1,
            panicked_total: 1,
            peak_pending: 4,
        };
        let snapshot = CleanupStatsSnapshot {
            queued: state.queued_total,
            executed: state.executed_total,
            cancelled: state.cancelled_total,
            panicked: state.panicked_total,
            pending: state.handles.len() + state.active,
            peak_pending: state.peak_pending,
        };
        assert_eq!(snapshot.pending, 3);
        assert_eq!(snapshot.peak_pending, 4);
    }
}
