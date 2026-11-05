//! Native request completion is independent of Taro frame lifetime. A backend
//! owns one completion token until its last use of borrowed memory. Cancellation
//! is only a request; frame/pin destruction waits for acknowledgment. Completion
//! wakeups carry an executor identity and never dereference the submitting frame.
use super::AsyncHandle;
use std::sync::{Arc, Condvar, Mutex};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    Running,
    Cancelling,
    Draining,
    Finished,
}

struct State {
    phase: Phase,
    cancelled: bool,
    waiter: Option<crate::executor::TaskWake>,
}
struct Record {
    state: Mutex<State>,
    finished: Condvar,
}

pub(super) struct NativeRequest(Arc<Record>);

/// One backend's completion obligation. Move this with the native request,
/// never with a borrowed Taro frame. Dropping it acknowledges that the backend
/// will no longer touch any protected address, including during error cleanup.
/// It is deliberately not Clone: every submitted operation acknowledges once.
///
/// The backend may query cancellation on any thread. Acknowledgment needs no
/// Taro callback, attached mutator, or submitting executor; an expired wake target
/// is harmless. This does not itself make any Taro payload Sendable.
pub struct NativeCompletion(Arc<Record>);
impl NativeCompletion {
    pub fn is_cancelled(&self) -> bool {
        self.0.state.lock().unwrap().cancelled
    }

    /// Acknowledge after the final native buffer access. Consumes the token.
    pub fn finish(self) {
        drop(self);
    }
}
impl Drop for NativeCompletion {
    fn drop(&mut self) {
        let waiter = {
            let mut state = self.0.state.lock().unwrap();
            state.phase = Phase::Finished;
            state.waiter.take()
        };
        self.0.finished.notify_all();
        if let Some(waiter) = waiter {
            waiter.wake();
        }
    }
}

/// Attach one submitted native operation to its actual async owner. The returned
/// token belongs to the backend, not to a frame-local cleanup guard. Register
/// before submitting the address: even eager work in an unstarted future must
/// remain protected. A submission failure must drop/finish the token too.
///
/// # Safety
/// `handle` is uniquely owned, unpolled and incomplete, and no poll/destruction or
/// other registration runs concurrently. Its frame/pins own every borrowed
/// address used by this request. The backend must stop using those addresses
/// before dropping the token, and acknowledgment must not wait for Taro code to
/// run (synchronous destruction may be waiting for it). Raw pointer/thread and
/// descriptor validity remain the backend's responsibility.
pub unsafe fn register_native_request(handle: *mut u8) -> NativeCompletion {
    if handle.is_null() {
        crate::abi::invalid_metadata("null native request owner");
    }
    let handle = unsafe { &mut *AsyncHandle::of(handle) };
    if handle.started || handle.completed || handle.cancel_by_drop {
        crate::abi::invalid_metadata("native request needs a live draining owner");
    }
    let record = Arc::new(Record {
        state: Mutex::new(State {
            phase: Phase::Running,
            cancelled: false,
            waiter: crate::executor::current_task_wake(),
        }),
        finished: Condvar::new(),
    });
    handle.native_requests.push(NativeRequest(record.clone()));
    NativeCompletion(record)
}

impl NativeRequest {
    pub(super) fn is_finished(&self) -> bool {
        self.0.state.lock().unwrap().phase == Phase::Finished
    }
    pub(super) fn register_waiter(&self) {
        if let Some(waiter) = crate::executor::current_task_wake() {
            let mut state = self.0.state.lock().unwrap();
            if state.phase != Phase::Finished {
                state.waiter = Some(waiter);
            }
        }
    }
    fn request_cancel(&self) {
        let mut state = self.0.state.lock().unwrap();
        if state.phase != Phase::Finished {
            state.cancelled = true;
            if state.phase == Phase::Running {
                state.phase = Phase::Cancelling;
            }
        }
    }
    fn drain(&self) {
        if self.is_finished() {
            return;
        }
        // Do not remain an active mutator while a backend is completing. Also
        // release the record lock before restoring mutator participation.
        let mut state = self.0.state.lock().unwrap();
        if state.phase != Phase::Finished {
            state.phase = Phase::Draining;
        }
        while state.phase != Phase::Finished {
            state = self.0.finished.wait(state).unwrap();
        }
    }
}

pub(super) fn request_all(requests: &[NativeRequest]) {
    // Request every sibling before waiting for any: backends can coordinate
    // completion without leaving a sibling unaware of cancellation.
    for request in requests {
        request.request_cancel();
    }
}
pub(super) fn drain_all(requests: &[NativeRequest]) {
    request_all(requests);
    for request in requests {
        request.drain();
    }
}

pub(super) fn wait_for_progress() {
    // Synchronous drop cannot yield a live frame to its caller. Backend work
    // completes independently; a short parked wait avoids an active-mutator
    // spin. Ordinary awaited cancellation returns Pending to the executor.
    std::thread::park_timeout(std::time::Duration::from_millis(1));
}

#[cfg(test)]
mod tests;
