use super::*;
use crate::task::*;
use std::sync::atomic::{AtomicUsize, Ordering};

struct Frame {
    value: usize,
    observed: Arc<AtomicUsize>,
    drops: Arc<AtomicUsize>,
    polls: usize,
}
unsafe extern "C-unwind" fn poll(frame: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
    let frame = unsafe { &mut *frame.cast::<Frame>() };
    frame.polls += 1;
    if crate::executor::__rt__executor_is_current_task_cancelled() {
        2
    } else {
        0
    }
}
unsafe extern "C-unwind" fn destroy(frame: *mut u8) {
    let frame = unsafe { Box::from_raw(frame.cast::<Frame>()) };
    frame.observed.store(frame.value, Ordering::Release);
    frame.drops.fetch_add(1, Ordering::AcqRel);
}
fn make() -> (*mut u8, *mut Frame, Arc<AtomicUsize>, Arc<AtomicUsize>) {
    let drops = Arc::new(AtomicUsize::new(0));
    let observed = Arc::new(AtomicUsize::new(0));
    let frame = Box::into_raw(Box::new(Frame {
        value: 7,
        observed: observed.clone(),
        drops: drops.clone(),
        polls: 0,
    }));
    let handle = __rt__async_create(frame.cast(), poll as *const u8, destroy as *const u8, 1);
    (handle, frame, observed, drops)
}

#[test]
fn pending_cancellation_keeps_native_buffer_live_until_explicit_acknowledgment() {
    let (handle, frame, observed, drops) = make();
    let completion = unsafe { register_native_request(handle) };
    assert_eq!(__rt__async_poll(handle, std::ptr::null_mut()), 0);
    for _ in 0..3 {
        assert_eq!(__rt__async_cancel_poll(handle), 0);
        assert!(completion.is_cancelled());
        assert_eq!(drops.load(Ordering::Acquire), 0);
    }
    // Backend can still use the old address after cancellation was requested.
    let address = frame as usize;
    std::thread::spawn(move || {
        unsafe { (*(address as *mut Frame)).value = 42 };
        completion.finish();
    })
    .join()
    .unwrap();
    assert_eq!(__rt__async_cancel_poll(handle), 2); // consumes handle
    assert_eq!(drops.load(Ordering::Acquire), 1);
    assert_eq!(observed.load(Ordering::Acquire), 42);
}

#[test]
fn destruction_of_eager_unpolled_native_work_waits_without_entering_body() {
    let (handle, frame, observed, drops) = make();
    let completion = unsafe { register_native_request(handle) };
    let address = handle as usize;
    let worker = std::thread::spawn(move || __rt__async_destroy(address as *mut u8));
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    while !completion.is_cancelled() {
        assert!(
            std::time::Instant::now() < deadline,
            "cancellation was never requested"
        );
        std::thread::yield_now();
    }
    assert_eq!(drops.load(Ordering::Acquire), 0);
    unsafe {
        assert_eq!((*frame).polls, 0);
        (*frame).value = 99;
    }
    completion.finish();
    worker.join().unwrap();
    assert_eq!(observed.load(Ordering::Acquire), 99);
    assert_eq!(drops.load(Ordering::Acquire), 1);
}

#[test]
fn all_sibling_requests_are_cancelled_before_waiting_for_any_acknowledgment() {
    let (handle, _, _, drops) = make();
    let first = unsafe { register_native_request(handle) };
    let second = unsafe { register_native_request(handle) };
    let address = handle as usize;
    let worker = std::thread::spawn(move || __rt__async_cancel(address as *mut u8));
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    while !first.is_cancelled() || !second.is_cancelled() {
        assert!(std::time::Instant::now() < deadline);
        std::thread::yield_now();
    }
    assert_eq!(drops.load(Ordering::Acquire), 0);
    second.finish();
    assert_eq!(drops.load(Ordering::Acquire), 0);
    first.finish();
    worker.join().unwrap();
    assert_eq!(drops.load(Ordering::Acquire), 1);
}

#[test]
fn cancellation_and_backend_completion_race_destroy_exactly_once() {
    for _ in 0..64 {
        let (handle, _, _, drops) = make();
        let completion = unsafe { register_native_request(handle) };
        let worker = std::thread::spawn(move || completion.finish());
        __rt__async_cancel(handle);
        worker.join().unwrap();
        assert_eq!(drops.load(Ordering::Acquire), 1);
    }
}

#[test]
fn pending_cancel_callback_is_repolled_instead_of_destroyed_after_one_poll() {
    unsafe extern "C-unwind" fn delayed(frame: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
        let frame = unsafe { &mut *frame.cast::<Frame>() };
        frame.polls += 1;
        if frame.polls < 4 {
            0
        } else {
            frame.value = 81;
            2
        }
    }
    let (handle, _, observed, drops) = make();
    unsafe { (*AsyncHandle::of(handle)).poll_fn = delayed as *const u8 };
    assert_eq!(__rt__async_poll(handle, std::ptr::null_mut()), 0);
    __rt__async_cancel(handle);
    assert_eq!(observed.load(Ordering::Acquire), 81);
    assert_eq!(drops.load(Ordering::Acquire), 1);
}

#[test]
fn suspended_frame_cleanup_can_remain_pending_until_acknowledged() {
    unsafe extern "C-unwind" fn pending_then_cancelled(
        frame: *mut u8,
        _: *mut u8,
        _: *mut u8,
    ) -> u8 {
        let count = unsafe { &mut *frame.cast::<usize>() };
        *count += 1;
        if *count < 3 { 0 } else { 2 }
    }
    let mut count = 0usize;
    unsafe {
        __rt__async_cancel_frame((&raw mut count).cast(), pending_then_cancelled as *const u8)
    };
    assert_eq!(count, 3);
}

#[test]
fn successful_output_is_not_published_before_native_buffer_completion() {
    unsafe extern "C-unwind" fn ready(frame: *mut u8, _: *mut u8, output: *mut u8) -> u8 {
        let frame = unsafe { &*frame.cast::<Frame>() };
        unsafe { output.cast::<usize>().write(frame.value) };
        1
    }
    let (handle, frame, observed, drops) = make();
    unsafe { (*AsyncHandle::of(handle)).poll_fn = ready as *const u8 };
    let completion = unsafe { register_native_request(handle) };
    let published = std::sync::atomic::AtomicBool::new(false);
    let mut output = 0usize;
    assert_eq!(
        unsafe {
            __rt__async_poll_published(handle, (&raw mut output).cast(), published.as_ptr().cast())
        },
        0
    );
    assert!(!published.load(Ordering::Acquire));
    assert_eq!(drops.load(Ordering::Acquire), 0);
    assert!(!completion.is_cancelled());
    unsafe { (*frame).value = 67 };
    completion.finish();
    assert_eq!(
        unsafe {
            __rt__async_poll_published(handle, (&raw mut output).cast(), published.as_ptr().cast())
        },
        1
    );
    assert!(published.load(Ordering::Acquire));
    assert_eq!(output, 67);
    assert_eq!(observed.load(Ordering::Acquire), 67);
    __rt__async_destroy(handle);
    assert_eq!(drops.load(Ordering::Acquire), 1);
}
