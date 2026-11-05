//! S40 regressions exercise the real observer and output ownership boundaries.
use super::*;
use std::ptr;

fn context(scheduler: &Arc<Scheduler>, current_task: Option<TaskToken>) -> WorkerContextGuard {
    WORKER_CONTEXT.with(|cell| {
        cell.replace(Some(WorkerContext {
            scheduler: scheduler.clone(),
            worker_id: 0,
            current_task,
            current_wait_reason: None,
            current_cancellation: None,
        }))
    });
    WorkerContextGuard
}

fn spawned(scheduler: &Arc<Scheduler>) -> (TaskToken, *mut u8) {
    let child = scheduler.add_task(
        ptr::null_mut(),
        ptr::null_mut(),
        Some(TaskOutput::empty()),
        0,
        Some(0),
        true,
    );
    (
        child,
        attach_test_handle(scheduler, child, ptr::null_mut(), 0),
    )
}

#[test]
fn failed_task_result_does_not_publish_uninitialized_value_bytes() {
    let scheduler = Scheduler::new(false, 1);
    let (child, handle) = spawned(&scheduler);
    scheduler.complete_task_cancelled(child);
    let parent = scheduler.add_task(ptr::null_mut(), ptr::null_mut(), None, 0, Some(0), false);
    let _context = context(&scheduler, Some(parent));
    let future = __rt__async_task_result(handle);
    let publication = AtomicBool::new(false);
    let mut output = 0x1234usize;
    let tag = unsafe {
        crate::task::__rt__async_poll_published(
            future,
            (&raw mut output).cast(),
            publication.as_ptr().cast(),
        )
    };
    crate::task::__rt__async_destroy(future);
    assert_eq!(tag, 3, "completed failure has no initialized T");
    assert!(!publication.load(Ordering::Acquire));
    assert_eq!(output, 0x1234);
    assert_eq!(__rt__task_status(handle), 2);
}

#[test]
fn terminal_result_is_observed_repeatedly() {
    let scheduler = Scheduler::new(false, 1);
    let (child, handle) = spawned(&scheduler);
    scheduler.complete_task(child);
    let parent = scheduler.add_task(ptr::null_mut(), ptr::null_mut(), None, 0, Some(0), false);
    let _context = context(&scheduler, Some(parent));
    for _ in 0..3 {
        let future = __rt__async_task_result(handle);
        assert_eq!(crate::task::__rt__async_poll(future, ptr::null_mut()), 1);
        crate::task::__rt__async_destroy(future);
        assert_eq!(__rt__task_status(handle), 1);
    }
}

#[test]
fn successful_completion_preserves_value_despite_unobserved_cancellation_request() {
    let scheduler = Scheduler::new(false, 1);
    let (child, handle) = spawned(&scheduler);
    let _context = context(&scheduler, None);
    __rt__task_cancel(handle);
    // A running body can finish successfully before its next cancellation
    // check; only an actual cancelled poll publishes cancellation.
    scheduler.complete_task(child);
    assert_eq!(__rt__task_status(handle), 1);
    __rt__task_cancel(handle);
    assert_eq!(__rt__task_status(handle), 1);
}

#[test]
fn root_poll_panic_is_preserved_before_shutdown_drain() {
    unsafe extern "C-unwind" fn poll(_: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
        crate::panic_unwind::rethrow_panic_message("root poll failure".into());
    }
    unsafe extern "C-unwind" fn destroy(frame: *mut u8) {
        let drops = unsafe { Box::from_raw(frame.cast::<Arc<AtomicUsize>>()) };
        drops.fetch_add(1, Ordering::SeqCst);
    }
    let drops = Arc::new(AtomicUsize::new(0));
    let handle = crate::task::__rt__async_create(
        Box::into_raw(Box::new(drops.clone())).cast(),
        poll as *const u8,
        destroy as *const u8,
        0,
    );
    let scheduler = Scheduler::new(true, 1);
    let root = scheduler.add_task(handle, ptr::null_mut(), None, 0, Some(0), false);
    let ctx = context(&scheduler, None);
    scheduler.run_task(0, root);
    let failure = scheduler.root_panic.lock().unwrap().take().unwrap();
    assert_eq!(failure.message, "root poll failure");
    assert!(scheduler.draining.load(Ordering::Acquire));
    let (index, _) = unpack_task_token(root);
    assert!(
        scheduler
            .lookup_task_slot(index)
            .unwrap()
            .inner
            .lock()
            .unwrap()
            .handle
            .is_null()
    );
    assert_eq!(drops.load(Ordering::SeqCst), 1);
    assert!(
        !scheduler
            .lookup_task_slot(index)
            .unwrap()
            .inner
            .lock()
            .unwrap()
            .running,
        "captured root failure must release its running claim for shutdown"
    );
    drop(ctx);
    scheduler.teardown_remaining_tasks();
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn a_second_panic_in_poll_unwind_cleanup_is_fatal() {
    const PROBE: &str = "TARO_S40_DOUBLE_PANIC";
    if std::env::var_os(PROBE).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "executor::task_handle_tests::a_second_panic_in_poll_unwind_cleanup_is_fatal",
                "--nocapture",
            ])
            .env(PROBE, "1")
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("panic while unwinding"));
        return;
    }
    unsafe extern "C-unwind" fn poll(_: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
        crate::panic_unwind::rethrow_panic_message("first task panic".into());
    }
    unsafe extern "C-unwind" fn destroy(_: *mut u8) {
        crate::panic_unwind::rethrow_panic_message("second cleanup panic".into());
    }
    let scheduler = Scheduler::new(false, 1);
    let handle = crate::task::__rt__async_create(
        ptr::null_mut(),
        poll as *const u8,
        destroy as *const u8,
        0,
    );
    let child = scheduler.add_task(handle, ptr::null_mut(), None, 0, Some(0), true);
    let _context = context(&scheduler, None);
    scheduler.run_task(0, child);
    panic!("a second cleanup panic was caught and ignored");
}
