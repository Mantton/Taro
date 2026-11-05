//! Process drain is distinct from stopping workers: cleanup may enqueue more
//! work, but its user body must never start after the root has finished.
use super::*;

impl Scheduler {
    pub(super) fn begin_shutdown_drain(&self) {
        let tasks = {
            // Registration uses this same lock through publication/accounting.
            let _admission = self.lock_admission();
            if self.draining.swap(true, Ordering::AcqRel) {
                return;
            }
            self.tasks
                .read()
                .unwrap()
                .iter()
                .enumerate()
                .filter_map(|(index, slot)| {
                    let inner = slot.inner.lock().unwrap();
                    (inner.occupied && !inner.completed)
                        .then(|| pack_task_token(index, inner.generation))
                })
                .collect::<Vec<_>>()
        };
        // No user cleanup, wake callback or backend cancellation runs under
        // admission. Requests still follow S39's asynchronous acknowledgment.
        for task in tasks {
            self.cancel_task(task);
        }
    }

    pub(super) fn finish_root_if_needed(&self, task: TaskToken) {
        if !self.rooted {
            return;
        }
        let (index, generation) = unpack_task_token(task);
        let root = self.lookup_task_slot(index).is_some_and(|slot| {
            let inner = slot.inner.lock().unwrap();
            inner.occupied
                && inner.generation == generation
                && !inner.is_spawned
                && inner.group_id.is_none()
        });
        if !root {
            return;
        }
        if self.exit_on_root.load(Ordering::Acquire) {
            self.signal_root_exit();
        } else {
            self.begin_shutdown_drain();
        }
    }

    pub(super) fn signal_root_exit(&self) {
        *self.root_exited.lock().unwrap() = true;
        self.root_exit_signal.notify_all();
    }

    pub(super) fn task_finished(&self) {
        if self.incomplete_tasks.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.finish_quiescent_drain();
        }
    }

    /// Close admission once every task has finished, then retire completed
    /// result roots and report unobserved panics outside scheduler locks.
    pub(super) fn finish_quiescent_drain(&self) {
        let (outputs, reports) = {
            let _admission = self.lock_admission();
            if self.incomplete_tasks.load(Ordering::Acquire) != 0 {
                return;
            }
            if !self.draining.load(Ordering::Acquire) {
                self.force_shutdown();
                return;
            }
            let mut outputs = Vec::new();
            let mut reports = Vec::new();
            for slot in self.tasks.read().unwrap().iter() {
                let mut inner = slot.inner.lock().unwrap();
                if !inner.occupied || !inner.completed {
                    continue;
                }
                if let Some(output) = inner.out_buf.take() {
                    inner.out_ptr = std::ptr::null_mut();
                    outputs.push(output);
                }
                if let Some(report) = inner.panic_info.take() {
                    reports.push(report);
                }
            }
            for group in self.task_groups.lock().unwrap().iter_mut().flatten() {
                outputs.extend(group.completed.drain(..).map(|entry| entry.buf));
                if let Some(report) = group.panic_report.take() {
                    reports.push(report);
                }
            }
            // Result retirement cannot execute language cleanup or spawn work.
            // Closing admission and checking the final count are atomic here.
            self.force_shutdown();
            (outputs, reports)
        };
        for report in reports {
            crate::panic_unwind::write_unobserved_task_panic(&report);
        }
        drop(outputs);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[derive(Default)]
    struct Counts {
        polls: AtomicUsize,
        drops: AtomicUsize,
    }
    struct Frame {
        counts: Arc<Counts>,
        spawn_on_drop: Option<(Weak<Scheduler>, Arc<Counts>)>,
    }
    unsafe extern "C-unwind" fn poll(frame: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
        unsafe { &*frame.cast::<Frame>() }
            .counts
            .polls
            .fetch_add(1, Ordering::SeqCst);
        0
    }
    unsafe extern "C-unwind" fn destroy(frame: *mut u8) {
        let frame = unsafe { Box::from_raw(frame.cast::<Frame>()) };
        frame.counts.drops.fetch_add(1, Ordering::SeqCst);
        if let Some((scheduler, child)) = &frame.spawn_on_drop {
            let scheduler = scheduler.upgrade().unwrap();
            let _admission = scheduler.open_admission();
            let handle = handle(Arc::clone(child), None);
            scheduler.add_task(handle, std::ptr::null_mut(), None, 0, None, true);
        }
    }
    fn handle(counts: Arc<Counts>, spawn: Option<(Weak<Scheduler>, Arc<Counts>)>) -> *mut u8 {
        crate::task::create_runtime_wait(
            Box::into_raw(Box::new(Frame {
                counts,
                spawn_on_drop: spawn,
            }))
            .cast(),
            poll as *const () as *const u8,
            destroy as *const () as *const u8,
            TaskMobility::Movable as u8,
        )
    }
    fn drive(scheduler: &Arc<Scheduler>) {
        let local = scheduler.start();
        Arc::clone(scheduler).worker_loop(0, local);
        scheduler.join_background_threads();
        scheduler.teardown_remaining_tasks();
    }
    #[test]
    fn drain_never_polls_new_tasks_and_releases_their_captures() {
        let scheduler = Scheduler::new(false, 1);
        scheduler.begin_shutdown_drain();
        let counts = Arc::new(Counts::default());
        scheduler.add_task(
            handle(Arc::clone(&counts), None),
            std::ptr::null_mut(),
            None,
            0,
            None,
            true,
        );
        drive(&scheduler);
        assert_eq!(counts.polls.load(Ordering::SeqCst), 0);
        assert_eq!(counts.drops.load(Ordering::SeqCst), 1);
    }
    #[test]
    fn cancellation_cleanup_can_spawn_cancelled_work_before_admission_closes() {
        let scheduler = Scheduler::new(false, 1);
        let parent = Arc::new(Counts::default());
        let child = Arc::new(Counts::default());
        scheduler.add_task(
            handle(
                Arc::clone(&parent),
                Some((Arc::downgrade(&scheduler), Arc::clone(&child))),
            ),
            std::ptr::null_mut(),
            None,
            0,
            None,
            true,
        );
        scheduler.begin_shutdown_drain();
        drive(&scheduler);
        assert_eq!(parent.drops.load(Ordering::SeqCst), 1);
        assert_eq!(child.polls.load(Ordering::SeqCst), 0);
        assert_eq!(child.drops.load(Ordering::SeqCst), 1);
    }
}

#[cfg(test)]
mod reporting_tests {
    use super::*;
    #[test]
    fn spawned_task_panic_is_reported_once_when_it_escapes() {
        const PROBE: &str = "TARO_TASK_PANIC_REPORT";
        if std::env::var_os(PROBE).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "executor::shutdown::reporting_tests::spawned_task_panic_is_reported_once_when_it_escapes", "--nocapture"])
                .env(PROBE, "1").output().unwrap();
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(stderr.matches("task panic: escaped").count(), 1, "{stderr}");
            return;
        }
        let scheduler = Scheduler::new(false, 1);
        let task = scheduler.add_task(
            std::ptr::null_mut(),
            std::ptr::null_mut(),
            None,
            0,
            None,
            true,
        );
        let handle =
            super::super::outcome::attach_test_handle(&scheduler, task, std::ptr::null_mut(), 0);
        scheduler.complete_task_panicked(
            task,
            crate::panic_unwind::PanicReport {
                message: "escaped".into(),
                backtrace: String::new(),
                location: None,
                logical_stack: Vec::new(),
                task_trace: Vec::new(),
            },
        );
        // Observation and session teardown do not report it again.
        assert_eq!(super::super::__rt__task_status(handle), 3);
        scheduler.teardown_remaining_tasks();
    }
}
