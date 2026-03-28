use std::cell::RefCell;
use std::cmp::Reverse;
use std::collections::{BinaryHeap, VecDeque};
use std::time::{Duration as StdDuration, Instant};

use crate::garbage_collector::with_gc;
use crate::io_poller::{self, Interest};
use crate::task::{__rt__async_destroy, __rt__async_poll, async_handle_frame};

type TaskId = usize;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct TimerEntry {
    deadline: Instant,
    sequence: u64,
    task_id: TaskId,
}

struct ExecutorTask {
    handle: *mut u8,
    frame: *mut u8,
    out_ptr: *mut u8,
    /// Owned output buffer for spawned tasks (root task uses caller's pointer).
    _out_buf: Option<Vec<u8>>,
    completed: bool,
    /// Whether this task ID is currently present in the ready queue.
    /// Used to prevent duplicate entries that cause wasted polls.
    in_ready_queue: bool,
    /// Tasks waiting for this one to complete.
    waiters: Vec<TaskId>,
}

struct Executor {
    tasks: Vec<Option<ExecutorTask>>,
    ready_queue: VecDeque<TaskId>,
    timers: BinaryHeap<Reverse<TimerEntry>>,
    current_task: Option<TaskId>,
    /// Set to true during a poll if the current task blocked on some external
    /// wakeup source (another spawned task or a timer). When true, the
    /// scheduler does not immediately re-enqueue the task after a pending poll.
    current_task_blocked: bool,
    next_timer_sequence: u64,
    rooted: bool,
}

thread_local! {
    static EXECUTOR: RefCell<Option<Executor>> = const { RefCell::new(None) };
}

impl Executor {
    fn new(rooted: bool) -> Self {
        Self {
            tasks: Vec::new(),
            ready_queue: VecDeque::new(),
            timers: BinaryHeap::new(),
            current_task: None,
            current_task_blocked: false,
            next_timer_sequence: 0,
            rooted,
        }
    }

    fn add_task(
        &mut self,
        handle: *mut u8,
        out_ptr: *mut u8,
        out_buf: Option<Vec<u8>>,
    ) -> TaskId {
        let frame = async_handle_frame(handle);
        let id = self.tasks.len();
        self.tasks.push(Some(ExecutorTask {
            handle,
            frame,
            out_ptr,
            _out_buf: out_buf,
            completed: false,
            in_ready_queue: true,
            waiters: Vec::new(),
        }));

        // Register the frame as a GC root so it survives collection while
        // the task is suspended.
        if !frame.is_null() {
            with_gc(|gc| gc.add_persistent_root(frame as *const u8));
        }

        self.ready_queue.push_back(id);
        id
    }

    /// Enqueue a task into the ready queue, deduplicating entries.
    fn enqueue_task(&mut self, task_id: TaskId) {
        let Some(task) = self.tasks[task_id].as_mut() else {
            return;
        };
        if task.completed || task.in_ready_queue {
            return;
        }
        task.in_ready_queue = true;
        self.ready_queue.push_back(task_id);
    }

    fn complete_task(&mut self, id: TaskId) {
        let task = self.tasks[id].as_mut().expect("ICE: completing absent task");
        task.completed = true;

        // Remove the frame from GC roots — locals have been consumed.
        if !task.frame.is_null() {
            with_gc(|gc| gc.remove_persistent_root(task.frame as *const u8));
        }

        // Wake all tasks that were waiting for this one.
        let waiters: Vec<TaskId> = task.waiters.drain(..).collect();
        for waiter_id in waiters {
            self.enqueue_task(waiter_id);
        }
    }

    fn has_incomplete_tasks(&self) -> bool {
        self.tasks
            .iter()
            .flatten()
            .any(|task| !task.completed)
    }

    fn add_sleep_timer(&mut self, task_id: TaskId, deadline: Instant) {
        let sequence = self.next_timer_sequence;
        self.next_timer_sequence = self
            .next_timer_sequence
            .checked_add(1)
            .expect("sleep timer sequence overflow");
        self.timers.push(Reverse(TimerEntry {
            deadline,
            sequence,
            task_id,
        }));
    }

    fn wake_due_timers(&mut self, now: Instant) {
        while let Some(Reverse(entry)) = self.timers.peek().copied() {
            if entry.deadline > now {
                break;
            }
            let _ = self.timers.pop();
            self.enqueue_task(entry.task_id);
        }
    }

    fn next_timer_deadline(&self) -> Option<Instant> {
        self.timers.peek().map(|entry| entry.0.deadline)
    }
}

enum DriveAction {
    Poll(TaskId, *mut u8, *mut u8),
    Sleep(StdDuration),
    WaitIo(Option<StdDuration>),
    Done,
    Deadlock,
}

fn drive_executor() {
    loop {
        let action = EXECUTOR.with(|cell| {
            let mut borrow = cell.borrow_mut();
            let executor = borrow.as_mut().expect("ICE: executor missing");

            loop {
                if !executor.has_incomplete_tasks() {
                    return DriveAction::Done;
                }

                executor.wake_due_timers(Instant::now());

                let Some(task_id) = executor.ready_queue.pop_front().map(|id| {
                    // Clear the in_ready_queue flag as we dequeue.
                    if let Some(Some(task)) = executor.tasks.get_mut(id) {
                        task.in_ready_queue = false;
                    }
                    id
                }) else {
                    let timeout = executor.next_timer_deadline().map(|deadline| {
                        let now = Instant::now();
                        if deadline <= now {
                            StdDuration::ZERO
                        } else {
                            deadline.duration_since(now)
                        }
                    });

                    if io_poller::has_waiters() {
                        return DriveAction::WaitIo(timeout);
                    }

                    if let Some(duration) = timeout {
                        return DriveAction::Sleep(duration);
                    }
                    return DriveAction::Deadlock;
                };

                let task = executor.tasks[task_id]
                    .as_ref()
                    .expect("ICE: scheduled absent task");

                // Skip already-completed tasks (e.g. woken after completion).
                if task.completed {
                    continue;
                }

                executor.current_task = Some(task_id);
                executor.current_task_blocked = false;
                return DriveAction::Poll(task_id, task.handle, task.out_ptr);
            }
        });

        let (task_id, handle, out_ptr) = match action {
            DriveAction::Poll(task_id, handle, out_ptr) => (task_id, handle, out_ptr),
            DriveAction::Sleep(duration) => {
                std::thread::sleep(duration);
                continue;
            }
            DriveAction::WaitIo(timeout) => {
                let ready = io_poller::wait(timeout);
                EXECUTOR.with(|cell| {
                    let mut borrow = cell.borrow_mut();
                    let executor = borrow.as_mut().expect("ICE: executor missing");
                    for task_id in ready {
                        executor.enqueue_task(task_id);
                    }
                });
                continue;
            }
            DriveAction::Done => break,
            DriveAction::Deadlock => {
                panic!(
                    "async executor deadlock: no ready tasks, no pending timers or io waits, and incomplete tasks remain"
                );
            }
        };

        // Poll outside the borrow — this may call __rt__executor_spawn or
        // __rt__executor_poll_spawned, which re-enter the executor.
        let tag = __rt__async_poll(handle, out_ptr);

        // Re-acquire the borrow and process the result.
        EXECUTOR.with(|cell| {
            let mut borrow = cell.borrow_mut();
            let executor = borrow.as_mut().expect("ICE: executor missing");

            executor.current_task = None;

            if tag == 0 {
                if !executor.current_task_blocked {
                    executor.enqueue_task(task_id);
                }
            } else {
                // Ready.
                executor.complete_task(task_id);
                __rt__async_destroy(handle);
            }
        });
    }
}

fn teardown_executor() {
    EXECUTOR.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if let Some(executor) = borrow.take() {
            for (task_id, task) in executor.tasks.into_iter().enumerate() {
                let Some(task) = task else {
                    continue;
                };
                io_poller::cancel_task(task_id);
                if !task.frame.is_null() {
                    with_gc(|gc| gc.remove_persistent_root(task.frame as *const u8));
                }
                if !task.completed {
                    __rt__async_destroy(task.handle);
                }
            }
        }
    });
}

struct ExecutorTeardownGuard;

impl Drop for ExecutorTeardownGuard {
    fn drop(&mut self) {
        teardown_executor();
    }
}

/// Entry point: run an async handle to completion using the cooperative
/// executor.  Replaces the old busy-loop `while poll == 0 {}`.
pub fn run_root(handle: *mut u8, out: *mut u8) {
    EXECUTOR.with(|cell| {
        let mut executor = Executor::new(true);
        executor.add_task(handle, out, None);
        *cell.borrow_mut() = Some(executor);
    });
    let _teardown = ExecutorTeardownGuard;
    drive_executor();
}

/// Spawn a new task on the executor.  Returns a task ID that can be polled
/// later via `__rt__executor_poll_spawned`.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__executor_spawn(handle: *mut u8, out_size: u64) -> u64 {
    EXECUTOR.with(|cell| {
        let mut borrow = cell.borrow_mut();
        if borrow.is_none() {
            *borrow = Some(Executor::new(false));
        }
        let executor = borrow.as_mut().expect("ICE: executor missing after init");

        let mut buf = vec![0u8; out_size as usize];
        let out_ptr = buf.as_mut_ptr();
        let id = executor.add_task(handle, out_ptr, Some(buf));
        id as u64
    })
}

/// Poll a spawned task by ID.  Returns 1 if completed (output copied to `out`),
/// 0 if still pending (current task registered as waiter).
#[unsafe(no_mangle)]
pub extern "C" fn __rt__executor_poll_spawned(task_id: u64, out: *mut u8) -> u8 {
    EXECUTOR.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let executor = borrow.as_mut().expect("poll_spawned called outside executor");
        let id = task_id as usize;

        let task = executor.tasks[id]
            .as_ref()
            .expect("ICE: polling absent spawned task");

        if task.completed {
            // Copy the completed output to the caller's buffer.
            let src = task.out_ptr;
            if let Some(buf) = &task._out_buf {
                unsafe { std::ptr::copy_nonoverlapping(src, out, buf.len()) };
            }
            1
        } else {
            // Register the current task as a waiter (deduplicated).
            if let Some(current) = executor.current_task {
                let target = executor.tasks[id]
                    .as_mut()
                    .expect("ICE: polling absent spawned task");
                if !target.waiters.contains(&current) {
                    target.waiters.push(current);
                }
                executor.current_task_blocked = true;
            }
            0
        }
    })
}

pub(crate) fn register_sleep(deadline: Instant) {
    EXECUTOR.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let executor = borrow.as_mut().expect("sleep polled outside executor");
        let current = executor
            .current_task
            .expect("sleep polled with no current task");
        executor.add_sleep_timer(current, deadline);
        executor.current_task_blocked = true;
    });
}

pub(crate) fn register_io_wait(source_id: usize, interest: Interest) -> Result<(), i32> {
    EXECUTOR.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let executor = borrow.as_mut().expect("async io polled outside executor");
        let current = executor
            .current_task
            .expect("async io polled with no current task");

        io_poller::register_wait(source_id, current, interest)?;
        executor.current_task_blocked = true;
        Ok(())
    })
}

pub(crate) fn wake_tasks(task_ids: &[usize]) {
    EXECUTOR.with(|cell| {
        let mut borrow = cell.borrow_mut();
        let Some(executor) = borrow.as_mut() else {
            return;
        };

        for &task_id in task_ids {
            executor.enqueue_task(task_id);
        }
    });
}

/// Finish any lazily-created rootless executor work after a synchronous root
/// returns.  This is a no-op when no rootless executor was created.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__executor_finish_rootless() {
    let should_drive = EXECUTOR.with(|cell| {
        let borrow = cell.borrow();
        let Some(executor) = borrow.as_ref() else {
            return false;
        };
        assert!(
            !executor.rooted,
            "ICE: finish_rootless called while rooted executor is active"
        );
        true
    });

    if !should_drive {
        return;
    }

    let _teardown = ExecutorTeardownGuard;
    drive_executor();
}

/// Abort any lazily-created rootless executor state without polling queued
/// tasks.  Used by the test harness after a panicking sync test.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__executor_abort_rootless() {
    EXECUTOR.with(|cell| {
        let borrow = cell.borrow();
        if let Some(executor) = borrow.as_ref() {
            assert!(
                !executor.rooted,
                "ICE: abort_rootless called while rooted executor is active"
            );
        }
    });

    teardown_executor();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_deadline_timers_are_fifo() {
        let deadline = Instant::now()
            .checked_add(StdDuration::from_millis(1))
            .expect("deadline");
        let mut timers = BinaryHeap::new();
        timers.push(Reverse(TimerEntry {
            deadline,
            sequence: 1,
            task_id: 11,
        }));
        timers.push(Reverse(TimerEntry {
            deadline,
            sequence: 0,
            task_id: 7,
        }));

        assert_eq!(timers.pop().unwrap().0.task_id, 7);
        assert_eq!(timers.pop().unwrap().0.task_id, 11);
    }
}
