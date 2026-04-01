use std::time::{Duration as StdDuration, Instant};

use crate::garbage_collector::with_gc;
use crate::io_poller::Interest;
use crate::sync::WaitKind;

type PollThunk = unsafe extern "C-unwind" fn(frame: *mut u8, ctx: *mut u8, out: *mut u8) -> u8;
type DropThunk = unsafe extern "C" fn(frame: *mut u8);

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TaskMobility {
    Pinned = 0,
    Movable = 1,
}

impl TaskMobility {
    pub(crate) fn from_runtime_byte(value: u8) -> Self {
        match value {
            1 => Self::Movable,
            _ => Self::Pinned,
        }
    }
}

#[repr(C)]
struct AsyncHandle {
    frame: *mut u8,
    poll_fn: *const u8,
    drop_fn: *const u8,
    completed: bool,
    mobility: u8,
}

pub(crate) fn async_handle_frame(handle: *mut u8) -> *mut u8 {
    if handle.is_null() {
        return std::ptr::null_mut();
    }
    unsafe { (*(handle as *mut AsyncHandle)).frame }
}

pub(crate) fn async_handle_mobility(handle: *mut u8) -> TaskMobility {
    if handle.is_null() {
        return TaskMobility::Pinned;
    }
    TaskMobility::from_runtime_byte(unsafe { (*(handle as *mut AsyncHandle)).mobility })
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
    mobility: u8,
) -> *mut u8 {
    if !frame.is_null() {
        with_gc(|gc| gc.add_persistent_root(frame as *const u8));
    }
    let handle = Box::new(AsyncHandle {
        frame,
        poll_fn,
        drop_fn,
        completed: false,
        mobility,
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
    if !handle.frame.is_null() {
        crate::garbage_collector::unlink_shadow_frame_if_present(
            handle.frame as *mut crate::garbage_collector::GcShadowFrame,
        );
        with_gc(|gc| gc.remove_persistent_root(handle.frame as *const u8));
    }
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
    /// Whether we have registered a wait with the IO poller.  Once the
    /// executor re-polls us (after the IO poller wakes the task), we return
    /// Ready and clear this flag.
    armed: bool,
}

#[repr(C)]
struct SyncWaitFrame {
    sync_id: usize,
    kind: u8,
    armed: bool,
}

unsafe extern "C" fn spawned_task_drop(frame: *mut u8) {
    if frame.is_null() {
        return;
    }

    let _ = unsafe { Box::from_raw(frame as *mut SpawnedTaskValueFrame) };
}

/// Checked poll for spawned task result — does NOT panic on cancellation.
/// Returns 1 (ready) for both completed and cancelled tasks.
/// The caller must query `__rt__executor_task_completion_status` after resume.
unsafe extern "C-unwind" fn spawned_task_result_poll(
    frame: *mut u8,
    _ctx: *mut u8,
    out: *mut u8,
) -> u8 {
    if frame.is_null() {
        return 1;
    }

    let task_id = unsafe { (*(frame as *mut SpawnedTaskValueFrame)).task_id };
    let status = crate::executor::__rt__executor_poll_spawned_checked(task_id, out);
    match status {
        0 => 0,
        _ => 1, // 1 (completed) or 2 (cancelled) both -> ready
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_from_spawned_checked(task_id: u64) -> *mut u8 {
    let frame = Box::into_raw(Box::new(SpawnedTaskValueFrame { task_id }));
    __rt__async_create(
        frame as *mut u8,
        spawned_task_result_poll as *const () as *const u8,
        spawned_task_drop as *const () as *const u8,
        TaskMobility::Movable as u8,
    )
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

    // After arming, the executor will only re-poll us once the IO poller has
    // delivered a wakeup (ready queue dedup prevents spurious re-entries).
    // Return Ready and clear the armed flag so the frame can be reused.
    if wait.armed {
        wait.armed = false;
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

unsafe extern "C-unwind" fn sync_wait_poll(frame: *mut u8, _ctx: *mut u8, out: *mut u8) -> u8 {
    if frame.is_null() {
        return 1;
    }

    let wait = unsafe { &mut *(frame as *mut SyncWaitFrame) };

    if wait.armed {
        wait.armed = false;
        if !out.is_null() {
            unsafe { (out as *mut i32).write(0) };
        }
        return 1;
    }

    let kind = match wait.kind {
        0 => WaitKind::ChannelSend,
        1 => WaitKind::ChannelRecv,
        2 => WaitKind::Mutex,
        3 => WaitKind::RwRead,
        4 => WaitKind::RwWrite,
        _ => panic!("invalid sync wait kind"),
    };

    match crate::executor::register_sync_wait(wait.sync_id, kind) {
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

unsafe extern "C" fn sync_wait_drop(frame: *mut u8) {
    if frame.is_null() {
        return;
    }

    let _ = unsafe { Box::from_raw(frame as *mut SyncWaitFrame) };
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_yield_now() -> *mut u8 {
    let frame = Box::into_raw(Box::new(0u8));
    __rt__async_create(
        frame,
        yield_now_poll as *const () as *const u8,
        yield_now_drop as *const () as *const u8,
        TaskMobility::Movable as u8,
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
        TaskMobility::Movable as u8,
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
        TaskMobility::Movable as u8,
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
        TaskMobility::Movable as u8,
    )
}

fn create_sync_wait(sync_id: usize, kind: u8) -> *mut u8 {
    let frame = Box::into_raw(Box::new(SyncWaitFrame {
        sync_id,
        kind,
        armed: false,
    }));
    __rt__async_create(
        frame as *mut u8,
        sync_wait_poll as *const () as *const u8,
        sync_wait_drop as *const () as *const u8,
        TaskMobility::Movable as u8,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_channel_wait_send(channel_id: usize) -> *mut u8 {
    create_sync_wait(channel_id, 0)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_channel_wait_recv(channel_id: usize) -> *mut u8 {
    create_sync_wait(channel_id, 1)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_mutex_lock(mutex_id: usize) -> *mut u8 {
    create_sync_wait(mutex_id, 2)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_rwlock_read(lock_id: usize) -> *mut u8 {
    create_sync_wait(lock_id, 3)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_rwlock_write(lock_id: usize) -> *mut u8 {
    create_sync_wait(lock_id, 4)
}

// --- Task group poll ---

#[repr(C)]
struct GroupNextFrame {
    group_id: u64,
}

/// Poll for the next completed result from a task group.
/// Returns 0 (pending) or 1 (ready — result written to `out`, or group exhausted
/// indicated by a tag byte the compiler interprets).
unsafe extern "C-unwind" fn group_next_poll(frame: *mut u8, _ctx: *mut u8, out: *mut u8) -> u8 {
    if frame.is_null() {
        return 1;
    }

    let group_id = unsafe { (*(frame as *mut GroupNextFrame)).group_id };
    let status = crate::executor::__rt__task_group_poll_next(group_id, out);
    match status {
        0 => 0,
        _ => 1, // 1 (got result) or 2 (exhausted) → both ready
    }
}

unsafe extern "C" fn group_next_drop(frame: *mut u8) {
    if frame.is_null() {
        return;
    }
    let _ = unsafe { Box::from_raw(frame as *mut GroupNextFrame) };
}

/// Create an async handle that polls for the next completed result from a task group.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_group_next(group_id: u64) -> *mut u8 {
    let frame = Box::into_raw(Box::new(GroupNextFrame { group_id }));
    __rt__async_create(
        frame as *mut u8,
        group_next_poll as *const () as *const u8,
        group_next_drop as *const () as *const u8,
        TaskMobility::Movable as u8,
    )
}
