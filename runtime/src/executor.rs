use std::cell::RefCell;
use std::collections::VecDeque;

use crate::garbage_collector::with_gc;
use crate::task::{__rt__async_destroy, __rt__async_poll, async_handle_frame};

type TaskId = usize;

struct ExecutorTask {
    handle: *mut u8,
    frame: *mut u8,
    out_ptr: *mut u8,
    /// Owned output buffer for spawned tasks (root task uses caller's pointer).
    _out_buf: Option<Vec<u8>>,
    completed: bool,
    /// Tasks waiting for this one to complete.
    waiters: Vec<TaskId>,
}

struct Executor {
    tasks: Vec<Option<ExecutorTask>>,
    ready_queue: VecDeque<TaskId>,
    current_task: Option<TaskId>,
    /// Set to true during a poll if the current task registered itself as a
    /// waiter on a spawned task (via `__rt__executor_poll_spawned`).  When true
    /// the scheduler does NOT re-enqueue the task after a pending poll — the
    /// task will be woken when the target completes.
    current_registered_waiter: bool,
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
            current_task: None,
            current_registered_waiter: false,
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
            self.ready_queue.push_back(waiter_id);
        }
    }

    fn has_incomplete_tasks(&self) -> bool {
        self.tasks
            .iter()
            .flatten()
            .any(|task| !task.completed)
    }
}

fn drive_executor() {
    loop {
        // Extract the next ready task's info, releasing the borrow before
        // calling poll (which may re-enter via spawn/poll_spawned).
        let poll_info = EXECUTOR.with(|cell| {
            let mut borrow = cell.borrow_mut();
            let executor = borrow.as_mut().expect("ICE: executor missing");

            if !executor.has_incomplete_tasks() {
                return None;
            }
            if executor.ready_queue.is_empty() {
                panic!("async executor deadlock: no ready tasks and incomplete tasks remain");
            }

            loop {
                let Some(task_id) = executor.ready_queue.pop_front() else {
                    if executor.has_incomplete_tasks() {
                        panic!(
                            "async executor deadlock: ready queue exhausted while incomplete tasks remain"
                        );
                    }
                    return None;
                };

                let task = executor.tasks[task_id]
                    .as_ref()
                    .expect("ICE: scheduled absent task");

                // Skip already-completed tasks (e.g. woken after completion).
                if task.completed {
                    continue;
                }

                executor.current_task = Some(task_id);
                executor.current_registered_waiter = false;
                return Some((task_id, task.handle, task.out_ptr));
            }
        });

        let Some((task_id, handle, out_ptr)) = poll_info else {
            break;
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
                // Pending.  Re-enqueue unless the task registered a waiter
                // (in which case it will be woken when the target completes).
                if !executor.current_registered_waiter {
                    executor.ready_queue.push_back(task_id);
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
            for task in executor.tasks.into_iter().flatten() {
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
            // Register the current task as a waiter.
            if let Some(current) = executor.current_task {
                let target = executor.tasks[id]
                    .as_mut()
                    .expect("ICE: polling absent spawned task");
                target.waiters.push(current);
                executor.current_registered_waiter = true;
            }
            0
        }
    })
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
