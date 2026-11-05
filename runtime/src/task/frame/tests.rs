//! Probe stable frame addresses directly. These are
//! not unregistered mutators racing a real collector on Rust test threads.
use super::*;
use crate::task::*;
use std::{
    cell::Cell,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
};

#[repr(C, align(64))]
struct Data {
    target: usize,
    sentinel: usize,
}
static TRACE: GcDesc = GcDesc {
    size: size_of::<Data>(),
    align: align_of::<Data>(),
    nodes: std::ptr::null(),
    node_count: 0,
};
thread_local! {
    static DROPS: Cell<usize> = const { Cell::new(0) };
    static PENDING: Cell<bool> = const { Cell::new(false) };
    static PANIC: Cell<bool> = const { Cell::new(false) };
}
unsafe extern "C-unwind" fn poll(_: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
    if crate::executor::__rt__executor_is_current_task_cancelled() {
        2
    } else {
        u8::from(!PENDING.get())
    }
}
unsafe extern "C-unwind" fn cleanup(data: *mut u8) {
    let data = unsafe { &mut *data.cast::<Data>() };

    assert_eq!(data.sentinel, 17);
    data.sentinel = 19;
    DROPS.set(DROPS.get() + 1);
    assert!(!PANIC.get(), "expected native frame cleanup panic");
}
unsafe fn fixture(target: usize) -> (*mut u8, *mut u8) {
    let owner = unsafe { __gc__async_frame_allocate(&TRACE) };
    let data = unsafe { __rt__async_frame_data(owner) };
    assert_eq!(data as usize % align_of::<Data>(), 0);
    assert_eq!(unsafe { (*data.cast::<Data>()).sentinel }, 0);
    unsafe {
        data.cast::<Data>().write(Data {
            target,
            sentinel: 17,
        })
    };

    let handle =
        unsafe { __rt__async_create_owned(owner, poll as *const u8, cleanup as *const u8, 0) };
    assert_eq!(async_handle_frame(handle), data);

    (handle, data)
}

#[test]
fn collected_frame_keeps_stable_bytes_through_every_handle_exit() {
    for mode in 0..4 {
        DROPS.set(0);
        PENDING.set(mode == 2);
        PANIC.set(mode == 3);
        let target = Box::new(1u8);
        let address = (&*target as *const u8) as usize;
        let (handle, data) = unsafe { fixture(address) };
        if mode == 1 {
            assert_eq!(__rt__async_poll(handle, std::ptr::null_mut()), 1);
            assert_eq!(async_handle_frame(handle), data);
        } else if mode == 2 {
            assert_eq!(__rt__async_poll(handle, std::ptr::null_mut()), 0);
        }
        let result = std::panic::catch_unwind(|| {
            if mode == 2 {
                __rt__async_cancel(handle);
            } else {
                __rt__async_destroy(handle);
            }
        });
        assert_eq!(result.is_err(), mode == 3);
        assert_eq!(DROPS.get(), 1);
    }
    PANIC.set(false);
}

#[test]
fn executor_completion_retires_a_movable_gc_frame() {
    #[repr(C, align(64))]
    struct Scheduled {
        target: usize,
        counter: *const AtomicUsize,
    }
    unsafe extern "C-unwind" fn poll(data: *mut u8, _: *mut u8, out: *mut u8) -> u8 {
        let _data = unsafe { &*data.cast::<Scheduled>() };

        unsafe { out.cast::<i32>().write(17) };
        1
    }
    unsafe extern "C-unwind" fn destroy(data: *mut u8) {
        let data = unsafe { &mut *data.cast::<Scheduled>() };

        let counter = unsafe { Arc::from_raw(data.counter) };
        data.counter = std::ptr::null();
        counter.fetch_add(1, Ordering::SeqCst);
    }
    let target = Box::new(3u8);
    let address = (&*target as *const u8) as usize;
    let count = Arc::new(AtomicUsize::new(0));
    // Taken before the first managed allocation registers this thread: a mutator
    // blocked on this lock outside a safepoint would stall other tests' collections.
    let _guard = crate::executor::tests::TEST_ENV_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let owner = unsafe { __gc__async_frame_allocate(&TRACE) };
    let data = unsafe { __rt__async_frame_data(owner) };
    unsafe {
        data.cast::<Scheduled>().write(Scheduled {
            target: address,
            counter: Arc::into_raw(count.clone()),
        })
    };
    // The native caller's transfer proof is explicit here: immutable probe data
    // and an atomic Arc counter permit polling/destruction on any worker.
    let handle =
        unsafe { __rt__async_create_owned(owner, poll as *const u8, destroy as *const u8, 1) };

    let mut result: i32 = 0;
    __rt__async_run_root(handle, (&raw mut result).cast());
    assert_eq!(result, 17);
    assert_eq!(count.load(Ordering::SeqCst), 1);
}
