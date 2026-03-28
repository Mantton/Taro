use std::time::{Duration as StdDuration, Instant};

use crate::io_poller::Interest;

type PollThunk = unsafe extern "C-unwind" fn(frame: *mut u8, ctx: *mut u8, out: *mut u8) -> u8;
type DropThunk = unsafe extern "C" fn(frame: *mut u8);

#[repr(C)]
struct AsyncHandle {
    frame: *mut u8,
    poll_fn: *const u8,
    drop_fn: *const u8,
    completed: bool,
}

pub(crate) fn async_handle_frame(handle: *mut u8) -> *mut u8 {
    if handle.is_null() {
        return std::ptr::null_mut();
    }
    unsafe { (*(handle as *mut AsyncHandle)).frame }
}

fn decode_poll(ptr: *const u8) -> Option<PollThunk> {
    (!ptr.is_null()).then(|| unsafe { std::mem::transmute(ptr) })
}

fn decode_drop(ptr: *const u8) -> Option<DropThunk> {
    (!ptr.is_null()).then(|| unsafe { std::mem::transmute(ptr) })
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_create(
    frame: *mut u8,
    poll_fn: *const u8,
    drop_fn: *const u8,
) -> *mut u8 {
    let handle = Box::new(AsyncHandle {
        frame,
        poll_fn,
        drop_fn,
        completed: false,
    });
    Box::into_raw(handle) as *mut u8
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_poll(handle: *mut u8, out: *mut u8) -> u8 {
    if handle.is_null() {
        return 1;
    }

    let handle = unsafe { &mut *(handle as *mut AsyncHandle) };
    if handle.completed {
        return 1;
    }

    let Some(poll) = decode_poll(handle.poll_fn) else {
        handle.completed = true;
        return 1;
    };

    let tag = unsafe { poll(handle.frame, std::ptr::null_mut(), out) };
    if tag != 0 {
        if let Some(drop) = decode_drop(handle.drop_fn) {
            unsafe { drop(handle.frame) };
            handle.drop_fn = std::ptr::null();
        }
        handle.completed = true;
    }

    tag
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_destroy(handle: *mut u8) {
    if handle.is_null() {
        return;
    }

    let mut handle = unsafe { Box::from_raw(handle as *mut AsyncHandle) };
    if !handle.completed {
        if let Some(drop) = decode_drop(handle.drop_fn) {
            unsafe { drop(handle.frame) };
            handle.drop_fn = std::ptr::null();
        }
        handle.completed = true;
    }
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_run_root(handle: *mut u8, out: *mut u8) {
    if handle.is_null() {
        return;
    }

    crate::executor::run_root(handle, out);
}

unsafe extern "C-unwind" fn yield_now_poll(frame: *mut u8, _ctx: *mut u8, _out: *mut u8) -> u8 {
    if frame.is_null() {
        return 1;
    }

    let yielded = unsafe { frame.read() };
    if yielded == 0 {
        unsafe { frame.write(1) };
        0
    } else {
        1
    }
}

unsafe extern "C" fn yield_now_drop(frame: *mut u8) {
    if frame.is_null() {
        return;
    }

    let _ = unsafe { Box::from_raw(frame) };
}

#[repr(C)]
struct SpawnedTaskValueFrame {
    task_id: u64,
}

#[repr(C)]
struct SleepFrame {
    deadline: Instant,
}

#[repr(C)]
struct IoWaitFrame {
    source_id: usize,
    interest: u8,
    armed: bool,
}

unsafe extern "C-unwind" fn spawned_task_value_poll(
    frame: *mut u8,
    _ctx: *mut u8,
    out: *mut u8,
) -> u8 {
    if frame.is_null() {
        return 1;
    }

    let task_id = unsafe { (*(frame as *mut SpawnedTaskValueFrame)).task_id };
    crate::executor::__rt__executor_poll_spawned(task_id, out)
}

unsafe extern "C" fn spawned_task_value_drop(frame: *mut u8) {
    if frame.is_null() {
        return;
    }

    let _ = unsafe { Box::from_raw(frame as *mut SpawnedTaskValueFrame) };
}

unsafe extern "C-unwind" fn sleep_poll(frame: *mut u8, _ctx: *mut u8, _out: *mut u8) -> u8 {
    if frame.is_null() {
        return 1;
    }

    let deadline = unsafe { (*(frame as *mut SleepFrame)).deadline };
    if Instant::now() >= deadline {
        1
    } else {
        crate::executor::register_sleep(deadline);
        0
    }
}

unsafe extern "C" fn sleep_drop(frame: *mut u8) {
    if frame.is_null() {
        return;
    }

    let _ = unsafe { Box::from_raw(frame as *mut SleepFrame) };
}

unsafe extern "C-unwind" fn io_wait_poll(frame: *mut u8, _ctx: *mut u8, out: *mut u8) -> u8 {
    if frame.is_null() {
        return 1;
    }

    let wait = unsafe { &mut *(frame as *mut IoWaitFrame) };
    if wait.armed {
        if !out.is_null() {
            unsafe { (out as *mut i32).write(0) };
        }
        return 1;
    }

    let interest = match wait.interest {
        0 => Interest::Read,
        1 => Interest::Write,
        _ => panic!("invalid async io wait interest"),
    };

    match crate::executor::register_io_wait(wait.source_id, interest) {
        Ok(()) => {
            wait.armed = true;
            0
        }
        Err(err) => {
            if !out.is_null() {
                unsafe { (out as *mut i32).write(err) };
            }
            1
        }
    }
}

unsafe extern "C" fn io_wait_drop(frame: *mut u8) {
    if frame.is_null() {
        return;
    }

    let _ = unsafe { Box::from_raw(frame as *mut IoWaitFrame) };
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_from_spawned(task_id: u64) -> *mut u8 {
    let frame = Box::into_raw(Box::new(SpawnedTaskValueFrame { task_id }));
    __rt__async_create(
        frame as *mut u8,
        spawned_task_value_poll as *const () as *const u8,
        spawned_task_value_drop as *const () as *const u8,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_yield_now() -> *mut u8 {
    let frame = Box::into_raw(Box::new(0u8));
    __rt__async_create(
        frame,
        yield_now_poll as *const () as *const u8,
        yield_now_drop as *const () as *const u8,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_sleep(secs: u64, nanos: u32) -> *mut u8 {
    let duration = StdDuration::new(secs, nanos);
    let deadline = Instant::now()
        .checked_add(duration)
        .unwrap_or_else(|| panic!("sleep duration overflow"));
    let frame = Box::into_raw(Box::new(SleepFrame { deadline }));
    __rt__async_create(
        frame as *mut u8,
        sleep_poll as *const () as *const u8,
        sleep_drop as *const () as *const u8,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_wait_readable(source_id: usize) -> *mut u8 {
    let frame = Box::into_raw(Box::new(IoWaitFrame {
        source_id,
        interest: 0,
        armed: false,
    }));
    __rt__async_create(
        frame as *mut u8,
        io_wait_poll as *const () as *const u8,
        io_wait_drop as *const () as *const u8,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_wait_writable(source_id: usize) -> *mut u8 {
    let frame = Box::into_raw(Box::new(IoWaitFrame {
        source_id,
        interest: 1,
        armed: false,
    }));
    __rt__async_create(
        frame as *mut u8,
        io_wait_poll as *const () as *const u8,
        io_wait_drop as *const () as *const u8,
    )
}
