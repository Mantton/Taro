use std::time::{Duration as StdDuration, Instant};

use crate::garbage_collector::root_slots;
use crate::io_poller::Interest;
use crate::sync::WaitKind;

thread_local! {
    // A synchronous cancellation poll may run without an executor task (for
    // example while destroying a native frame). Scope it to the current task
    // identity so reentrant execution of another task does not inherit it.
    static FORCED_CANCELLATION: std::cell::RefCell<Vec<Option<crate::executor::TaskIdentity>>> = const {
        std::cell::RefCell::new(Vec::new())
    };
    // Every async poll asks whether its task was cancelled. Answer from one
    // plain thread-local when no scoped cancellation can apply. Null means no
    // answer is cached here, which sends the caller to the full check.
    static POLLED_TASK: PolledTask = const {
        PolledTask {
            cancellation: std::cell::Cell::new(std::ptr::null()),
            forced_depth: std::cell::Cell::new(0),
            inline_poll: std::cell::Cell::new(false),
            hold_next_spawn: std::cell::Cell::new(false),
            held_spawn: std::cell::Cell::new(None),
        }
    };
}
struct PolledTask {
    cancellation: std::cell::Cell<*const std::sync::atomic::AtomicBool>,
    forced_depth: std::cell::Cell<usize>,
    inline_poll: std::cell::Cell<bool>,
    hold_next_spawn: std::cell::Cell<bool>,
    held_spawn: std::cell::Cell<Option<crate::executor::TaskToken>>,
}
/// Keep the next task this poll spawns out of the queues, for a caller about to
/// claim it with a wait that decides how it runs. Waking a peer for it would be
/// wasted. The poll's end releases a task nothing claimed, as an ordinary spawn.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__task_hold_next_spawn() {
    POLLED_TASK.with(|task| task.hold_next_spawn.set(true));
}
/// Whether this worker could do anything better than keep polling for a result
/// about to arrive: other work is runnable, or a collection is waiting for it.
/// Whether a connection on this worker should busy-wait for its next request.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__task_may_spin() -> bool {
    crate::executor::may_spin()
}
#[unsafe(no_mangle)]
pub extern "C" fn __rt__task_should_stop_spinning() -> bool {
    crate::garbage_collector::collection_requested() || crate::executor::other_work_runnable()
}
pub(crate) fn take_hold_next_spawn() -> bool {
    POLLED_TASK.with(|task| task.hold_next_spawn.replace(false))
}
pub(crate) fn set_held_spawn(token: crate::executor::TaskToken) {
    POLLED_TASK.with(|task| task.held_spawn.set(Some(token)));
}
pub(crate) fn take_held_spawn() -> Option<crate::executor::TaskToken> {
    POLLED_TASK.with(|task| task.held_spawn.take())
}
/// Clear anything a poll left behind, returning a task it never claimed.
pub(crate) fn end_poll_holds() -> Option<crate::executor::TaskToken> {
    POLLED_TASK.with(|task| {
        task.hold_next_spawn.set(false);
        task.held_spawn.take()
    })
}
pub(crate) fn in_inline_poll() -> bool {
    POLLED_TASK.with(|task| task.inline_poll.get())
}
pub(crate) fn set_inline_poll(active: bool) {
    POLLED_TASK.with(|task| task.inline_poll.set(active));
}
/// Install the current task's flag, for as long as its worker context holds it.
pub(crate) fn set_polled_cancellation(flag: *const std::sync::atomic::AtomicBool) {
    POLLED_TASK.with(|task| task.cancellation.set(flag));
}
#[inline]
pub(crate) fn polled_task_cancelled() -> Option<bool> {
    POLLED_TASK.with(|task| {
        let flag = task.cancellation.get();
        if flag.is_null() || task.forced_depth.get() != 0 {
            return None;
        }
        // The worker context keeps the flag's owner alive until it clears this.
        Some(unsafe { &*flag }.load(std::sync::atomic::Ordering::Acquire))
    })
}
struct ForcedCancellation(std::marker::PhantomData<*mut ()>);
impl ForcedCancellation {
    fn new() -> Self {
        Self::scoped(crate::executor::current_task_identity())
    }
    fn scoped(task: Option<crate::executor::TaskIdentity>) -> Self {
        FORCED_CANCELLATION.with(|stack| stack.borrow_mut().push(task));
        POLLED_TASK.with(|task| task.forced_depth.set(task.forced_depth.get() + 1));
        Self(std::marker::PhantomData)
    }
}
impl Drop for ForcedCancellation {
    fn drop(&mut self) {
        FORCED_CANCELLATION.with(|stack| {
            stack.borrow_mut().pop().expect("scoped cancellation");
        });
        POLLED_TASK.with(|task| task.forced_depth.set(task.forced_depth.get() - 1));
    }
}
pub(crate) fn forced_cancellation_for(task: Option<crate::executor::TaskIdentity>) -> bool {
    FORCED_CANCELLATION.with(|stack| stack.borrow().iter().rev().any(|entry| *entry == task))
}

mod cancellation;
pub use cancellation::{NativeCompletion, register_native_request};

mod frame;
pub use frame::__rt__async_frame_data;

type PollThunk = unsafe extern "C-unwind" fn(frame: *mut u8, ctx: *mut u8, out: *mut u8) -> u8;
type DropThunk = unsafe extern "C-unwind" fn(frame: *mut u8);

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

/// A handle is the payload of its frame's root lease, and its opaque address is
/// the lease. A generated frame thus stays rooted through polling, runtime
/// cleanup and acknowledgment of every native request that can still access its
/// bytes, with no separate allocation. Runtime waitables hold an empty lease.
#[repr(C)]
struct AsyncHandle {
    frame: *mut u8,
    poll_fn: *const u8,
    drop_fn: *const u8,
    // Backend completion records never contain a pointer into this frame.
    native_requests: Vec<cancellation::NativeRequest>,
    completed: bool,
    // Only audited runtime waitables can cancel by dropping without polling.
    cancel_by_drop: bool,
    // Poll/drop are serialized by the handle owner. Constructor state must
    // be disposable without entering the poll callback at all.
    started: bool,
    mobility: u8,
}
/// Room left in a handle's slot for a runtime waitable's own frame.
const INLINE_WAIT_BYTES: usize = root_slots::PAYLOAD_BYTES - size_of::<AsyncHandle>();
const _: () = assert!(size_of::<AsyncHandle>() == 56);
const _: () = assert!(align_of::<AsyncHandle>() <= 8);

impl AsyncHandle {
    /// # Safety
    /// `slot` is a root lease the caller exclusively owns, with no live handle.
    unsafe fn install(slot: *mut root_slots::RootSlot, handle: Self) -> *mut u8 {
        unsafe { root_slots::payload(slot).cast::<Self>().write(handle) };
        slot.cast()
    }
    /// # Safety
    /// `handle` is non-null and came from `install`, and has not been retired.
    unsafe fn of(handle: *mut u8) -> *mut Self {
        unsafe { root_slots::payload(handle.cast()).cast() }
    }
}

/// Ends a handle on every exit from destruction, including unwinding out of its
/// frame's cleanup: the root outlives both that cleanup and the native requests.
struct RetireHandle(*mut u8);
impl Drop for RetireHandle {
    fn drop(&mut self) {
        unsafe {
            std::ptr::drop_in_place(AsyncHandle::of(self.0));
            root_slots::release(self.0.cast());
        }
    }
}

/// One native ownership obligation for an opaque handle. Keep this guard inside
/// the same panic boundary as polling so frame cleanup happens during unwind,
/// before the original panic state is reset. It carries no mobility proof.
pub(crate) struct OwnedAsyncHandle(*mut u8);
impl OwnedAsyncHandle {
    /// # Safety
    /// pointer carries one unique live/quiescent handle obligation. No other
    /// owner may destroy or poll it until this guard transfers ownership.
    pub(crate) unsafe fn from_raw(pointer: *mut u8) -> Self {
        Self(pointer)
    }
    pub(crate) fn as_ptr(&self) -> *mut u8 {
        self.0
    }

    /// Transfer the unique destruction obligation to an installed task slot.
    pub(crate) fn into_raw(self) -> *mut u8 {
        let pointer = self.0;
        std::mem::forget(self);
        pointer
    }
}
impl Drop for OwnedAsyncHandle {
    fn drop(&mut self) {
        __rt__async_destroy(self.0);
    }
}

#[cfg(test)]
pub(crate) fn async_handle_frame(handle: *mut u8) -> *mut u8 {
    if handle.is_null() {
        return std::ptr::null_mut();
    }
    unsafe { (*AsyncHandle::of(handle)).frame }
}

pub(crate) fn async_handle_mobility(handle: *mut u8) -> TaskMobility {
    if handle.is_null() {
        return TaskMobility::Pinned;
    }
    TaskMobility::from_runtime_byte(unsafe { (*AsyncHandle::of(handle)).mobility })
}

fn decode_poll(ptr: *const u8) -> Option<PollThunk> {
    (!ptr.is_null()).then(|| unsafe { std::mem::transmute(ptr) })
}

fn decode_drop(ptr: *const u8) -> Option<DropThunk> {
    (!ptr.is_null()).then(|| unsafe { std::mem::transmute(ptr) })
}

/// Consume the cleanup callback before running foreign code. The handle's GC
/// root stays registered throughout frame cleanup. A panic during a completion
/// drop may subsequently destroy the handle, but cannot re-enter this drop.
fn take_frame_drop(handle: &mut AsyncHandle) -> Option<DropThunk> {
    handle.completed = true;
    decode_drop(std::mem::replace(&mut handle.drop_fn, std::ptr::null()))
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_create(
    frame: *mut u8,
    poll_fn: *const u8,
    drop_fn: *const u8,
    mobility: u8,
) -> *mut u8 {
    let handle = AsyncHandle {
        frame,
        poll_fn,
        drop_fn,
        native_requests: Vec::new(),
        completed: false,
        cancel_by_drop: false,
        started: false,
        mobility,
    };
    unsafe { AsyncHandle::install(root_slots::acquire(std::ptr::null()), handle) }
}

/// Runtime-authored waitables retain IDs or independently owned work, never
/// borrowed caller buffers. Their drop callback releases frame-local state or
/// transfers independently owned blocking work to its worker. Reactor entries
/// retain only wake identities and retire at task finalization. Do not use this
/// constructor for native operations that retain a caller's address.
pub(crate) fn create_runtime_wait(
    frame: *mut u8,
    poll_fn: *const u8,
    drop_fn: *const u8,
    mobility: u8,
) -> *mut u8 {
    let handle = __rt__async_create(frame, poll_fn, drop_fn, mobility);
    unsafe { (*AsyncHandle::of(handle)).cancel_by_drop = true };
    handle
}

/// A runtime waitable whose frame lives beside its handle, needing no allocation.
pub(crate) fn create_inline_wait<T>(frame: T, poll_fn: *const u8, mobility: u8) -> *mut u8 {
    const {
        assert!(size_of::<T>() <= INLINE_WAIT_BYTES);
        assert!(align_of::<T>() <= 8);
    };
    unsafe extern "C-unwind" fn drop_frame<T>(frame: *mut u8) {
        unsafe { std::ptr::drop_in_place(frame.cast::<T>()) };
    }
    let drop_fn = if std::mem::needs_drop::<T>() {
        drop_frame::<T> as *const u8
    } else {
        std::ptr::null()
    };
    let handle = create_runtime_wait(std::ptr::null_mut(), poll_fn, drop_fn, mobility);
    unsafe {
        let state = AsyncHandle::of(handle);
        let storage = state.add(1).cast::<T>();
        storage.write(frame);
        (*state).frame = storage.cast();
    }
    handle
}

/// Consume a collected frame root lease. Poll/drop callbacks operate on its
/// data; root release follows frame cleanup, including unwind. Retained native
/// work must register an independent
/// completion token before polling; cleanup waits for its last buffer access.
///
/// # Safety
/// owner is one live __gc__async_frame_allocate result with all constructor inputs
/// installed. The callbacks match its exact frame layout and mobility proof.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__async_create_owned(
    owner: *mut u8,
    poll_fn: *const u8,
    drop_fn: *const u8,
    mobility: u8,
) -> *mut u8 {
    if owner.is_null() {
        crate::abi::invalid_metadata("null GC async frame transfer");
    }
    let slot = owner.cast::<root_slots::RootSlot>();
    let handle = AsyncHandle {
        frame: unsafe { root_slots::rooted(slot) },
        poll_fn,
        drop_fn,
        native_requests: Vec::new(),
        completed: false,
        cancel_by_drop: false,
        started: false,
        mobility,
    };
    unsafe { AsyncHandle::install(slot, handle) }
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_poll(handle: *mut u8, out: *mut u8) -> u8 {
    // A compiler-owned child that unwinds has no other owner left to destroy
    // it, so this entry consumes it, like __rt__async_cancel_poll. On normal
    // return the caller still owns the handle.
    let owner = unsafe { OwnedAsyncHandle::from_raw(handle) };
    let tag = poll_with_output_publication(handle, out, None);
    let _ = owner.into_raw();
    tag
}

/// Poll a compiler-owned child with an explicit output-initialization handoff.
/// On normal return the caller still owns the handle. On unwind this entry
/// destroys it, while `published` tells caller cleanup whether it owns a result.
///
/// # Safety
/// `published` points to a live, initially false, byte-sized bool, and `out`
/// can receive the child's result. Both remain valid through this call and its
/// unwind cleanup. The handle is uniquely owned and not concurrently polled.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __rt__async_poll_published(
    handle: *mut u8,
    out: *mut u8,
    published: *mut u8,
) -> u8 {
    if handle.is_null() || published.is_null() {
        crate::abi::invalid_metadata("invalid async output publication");
    }
    let owner = unsafe { OwnedAsyncHandle::from_raw(handle) };
    let published = unsafe { std::sync::atomic::AtomicBool::from_ptr(published.cast()) };
    let tag = poll_with_output_publication(handle, out, Some(published));
    let _ = owner.into_raw();
    tag
}

/// Scheduler-owned outputs must become traceable before terminal frame
/// destruction: cleanup callbacks may allocate or collect. Publication runs
/// directly after the raw poll, without acquiring locks or entering a safepoint.
pub(crate) fn poll_with_output_publication(
    handle: *mut u8,
    out: *mut u8,
    publication: Option<&std::sync::atomic::AtomicBool>,
) -> u8 {
    if handle.is_null() {
        return 1;
    }

    let handle = unsafe { &mut *AsyncHandle::of(handle) };
    if handle.completed {
        return 1;
    }

    for request in &handle.native_requests {
        request.register_waiter();
    }
    let cancelling = crate::executor::__rt__executor_is_current_task_cancelled();
    if cancelling {
        cancellation::request_all(&handle.native_requests);
    }
    // Do not call a continuation while a backend still has an address into its
    // frame. This also prevents publishing outputs before the last native write.
    if handle
        .native_requests
        .iter()
        .any(|request| !request.is_finished())
    {
        crate::executor::wait_for_native_request();
        return 0;
    }
    let tag = if cancelling && (handle.cancel_by_drop || !handle.started) {
        2
    } else if let Some(poll) = decode_poll(handle.poll_fn) {
        // Publish before foreign code can unwind through handle destruction.
        // Waiting on eager native work above must not enter a cold user body.
        handle.started = true;
        unsafe { poll(handle.frame, std::ptr::null_mut(), out) }
    } else {
        handle.started = true;
        1
    };
    if cancelling && tag != 0 && tag != 2 {
        crate::abi::invalid_metadata("ordinary result during async cancellation");
    }
    if tag == 1 {
        if let Some(publication) = publication {
            publication.store(true, std::sync::atomic::Ordering::Release);
        }
    }
    if tag != 0 {
        // Keep the collected frame rooted while its runtime cleanup runs.
        if let Some(drop) = take_frame_drop(handle) {
            unsafe { drop(handle.frame) };
        }
    }

    tag
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_destroy(handle: *mut u8) {
    if handle.is_null() {
        return;
    }

    // Own the handle and its GC frame through cleanup and native work.
    let _retire = RetireHandle(handle);
    let handle = unsafe { &mut *AsyncHandle::of(handle) };
    // Includes never-polled constructors with eagerly submitted native work,
    // and unwind after a backend poll. Keep frame bytes rooted here.
    cancellation::drain_all(&handle.native_requests);
    if !handle.completed {
        if let Some(drop) = take_frame_drop(handle) {
            unsafe { drop(handle.frame) };
        }
    }
}

/// Poll cancellation without consuming a pending child. A terminal return
/// consumes it; an unwind also consumes it, matching the compiler's cleanup
/// handoff. Pending keeps frame roots and native request records.
/// The unique owner serializes this with all ordinary polls and destruction.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_cancel_poll(handle: *mut u8) -> u8 {
    if handle.is_null() {
        return 2;
    }
    let _cancelled = ForcedCancellation::new();
    let owner = unsafe { OwnedAsyncHandle::from_raw(handle) };
    let state = unsafe { &*AsyncHandle::of(handle) };
    for request in &state.native_requests {
        request.register_waiter();
    }
    cancellation::request_all(&state.native_requests);
    if state.completed {
        return 2;
    }
    if state
        .native_requests
        .iter()
        .any(|request| !request.is_finished())
    {
        crate::executor::wait_for_native_request();
        return retain_pending(owner);
    }
    // Never enter unstarted user code. Eager native requests still have to
    // finish: the completion token is independent of this constructor's body.
    let pending = if state.started {
        poll_with_output_publication(handle, std::ptr::null_mut(), None) == 0
    } else {
        state
            .native_requests
            .iter()
            .any(|request| !request.is_finished())
    };
    if pending { retain_pending(owner) } else { 2 }
}

fn retain_pending(owner: OwnedAsyncHandle) -> u8 {
    let _ = owner.into_raw();
    0
}

/// Synchronous destruction fallback. Ordinary awaited cancellation uses
/// cancel_poll and can suspend. Destruction cannot release a borrowed buffer
/// early, so it waits for native acknowledgment without holding a runtime lock.
/// Backend acknowledgment must not require Taro execution.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_cancel(handle: *mut u8) {
    loop {
        if __rt__async_cancel_poll(handle) != 0 {
            return;
        }
        let state = unsafe { &*AsyncHandle::of(handle) };
        cancellation::drain_all(&state.native_requests);
        cancellation::wait_for_progress();
    }
}

/// Drive the checked cancellation path of a suspended compiler-generated frame.
/// This does not own/free the frame or release its incoming protection. The
/// owning handle retains those obligations until this callback finishes.
///
/// # Safety
/// frame is a live, rooted, suspended compiler frame and poll is its matching
/// generated poll thunk, with its owning task context when required by children.
/// No concurrent/reentrant poll may access it. Under the
/// scoped cancellation check the thunk must only execute cancellation cleanup,
/// return tag 2 and never write an ordinary result to the null output address.
/// Pending preserves the frame and retries cancellation until native work
/// acknowledges quiescence; it never authorizes releasing protected storage. Already-unwound/running or
/// never-started frames must not enter this operation.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __rt__async_cancel_frame(frame: *mut u8, poll: *const u8) {
    if frame.is_null() || poll.is_null() {
        crate::abi::invalid_metadata("null suspended frame cancellation");
    }
    let _cancelled = ForcedCancellation::new();
    let poll = decode_poll(poll).unwrap();
    loop {
        match unsafe { poll(frame, std::ptr::null_mut(), std::ptr::null_mut()) } {
            0 => cancellation::wait_for_progress(),
            2 => break,
            _ => {
                crate::abi::invalid_metadata("suspended frame cancellation did not finish cleanup")
            }
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_run_root(handle: *mut u8, out: *mut u8) {
    if handle.is_null() {
        return;
    }

    crate::executor::run_root(handle, out);
}

/// Drive a standalone program's async `main`; see `executor::run_main`.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__async_run_main(handle: *mut u8, out: *mut u8) {
    if handle.is_null() {
        return;
    }

    crate::executor::run_main(handle, out);
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
    handle: *mut u8,
    sync_id: usize,
    kind: u8,
    error: i32,
    armed: bool,
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

unsafe extern "C-unwind" fn sync_wait_poll(frame: *mut u8, _ctx: *mut u8, out: *mut u8) -> u8 {
    if frame.is_null() {
        return 1;
    }

    let wait = unsafe { &mut *(frame as *mut SyncWaitFrame) };

    if wait.error != 0 {
        if !out.is_null() {
            unsafe { (out as *mut i32).write(wait.error) };
        }
        return 1;
    }

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

unsafe extern "C-unwind" fn sync_wait_drop(frame: *mut u8) {
    if frame.is_null() {
        return;
    }

    drop(unsafe { Box::from_raw(frame as *mut SyncWaitFrame) });
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_yield_now() -> *mut u8 {
    create_inline_wait(
        0_u8,
        yield_now_poll as *const () as *const u8,
        TaskMobility::Movable as u8,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_sleep(secs: u64, nanos: u32) -> *mut u8 {
    let duration = StdDuration::new(secs, nanos);
    let deadline = Instant::now()
        .checked_add(duration)
        .unwrap_or_else(|| panic!("sleep duration overflow"));
    create_inline_wait(
        SleepFrame { deadline },
        sleep_poll as *const () as *const u8,
        TaskMobility::Movable as u8,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_wait_readable(source_id: usize) -> *mut u8 {
    create_inline_wait(
        IoWaitFrame {
            source_id,
            interest: 0,
            armed: false,
        },
        io_wait_poll as *const () as *const u8,
        TaskMobility::Movable as u8,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_wait_writable(source_id: usize) -> *mut u8 {
    create_inline_wait(
        IoWaitFrame {
            source_id,
            interest: 1,
            armed: false,
        },
        io_wait_poll as *const () as *const u8,
        TaskMobility::Movable as u8,
    )
}

fn create_sync_wait(handle: *mut u8, kind: u8) -> *mut u8 {
    let wait_kind = match kind {
        0 => WaitKind::ChannelSend,
        1 => WaitKind::ChannelRecv,
        2 => WaitKind::Mutex,
        3 => WaitKind::RwRead,
        4 => WaitKind::RwWrite,
        _ => panic!("invalid sync wait kind"),
    };
    let (sync_id, error, rooted_handle) = match crate::sync::wait_handle_id(handle, wait_kind) {
        Ok(id) => (id, 0, handle),
        Err(error) => (0, error, std::ptr::null_mut()),
    };
    let frame = Box::into_raw(Box::new(SyncWaitFrame {
        handle: rooted_handle,
        sync_id,
        kind,
        error,
        armed: false,
    }));
    create_runtime_wait(
        frame as *mut u8,
        sync_wait_poll as *const () as *const u8,
        sync_wait_drop as *const () as *const u8,
        TaskMobility::Movable as u8,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_channel_wait_send(handle: *mut u8) -> *mut u8 {
    create_sync_wait(handle, 0)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_channel_wait_recv(handle: *mut u8) -> *mut u8 {
    create_sync_wait(handle, 1)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_mutex_lock(handle: *mut u8) -> *mut u8 {
    create_sync_wait(handle, 2)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_rwlock_read(handle: *mut u8) -> *mut u8 {
    create_sync_wait(handle, 3)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_rwlock_write(handle: *mut u8) -> *mut u8 {
    create_sync_wait(handle, 4)
}

// --- Task group poll ---

#[repr(C)]
struct GroupNextFrame {
    group_id: u64,
}

/// Poll for the next completed result from a task group.
/// Only tag 1 initializes a group element; exhausted/failed groups return 3,
/// with no element to load or destroy.
unsafe extern "C-unwind" fn group_next_poll(frame: *mut u8, _ctx: *mut u8, out: *mut u8) -> u8 {
    if frame.is_null() {
        return 1;
    }

    let group_id = unsafe { (*(frame as *mut GroupNextFrame)).group_id };
    let status = crate::executor::__rt__task_group_poll_next(group_id, out);
    match status {
        0 => 0,
        1 => 1,
        crate::executor::GROUP_POLL_RETIRED => crate::panic_unwind::rethrow_panic_message(
            "task group used after its scope ended".to_string(),
        ),
        _ => 3, // group exhausted/failed without producing an element
    }
}

unsafe extern "C-unwind" fn group_next_drop(frame: *mut u8) {
    if frame.is_null() {
        return;
    }
    let _ = unsafe { Box::from_raw(frame as *mut GroupNextFrame) };
}

/// Create an async handle that polls for the next completed result from a task group.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_group_next(group_id: u64) -> *mut u8 {
    let frame = Box::into_raw(Box::new(GroupNextFrame { group_id }));
    create_runtime_wait(
        frame as *mut u8,
        group_next_poll as *const () as *const u8,
        group_next_drop as *const () as *const u8,
        TaskMobility::Movable as u8,
    )
}

#[cfg(test)]
mod ownership_tests {
    use super::*;
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };

    struct Counted(Arc<AtomicUsize>);
    impl Drop for Counted {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }
    unsafe extern "C-unwind" fn ready_counted(frame: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
        // The frame lives in the handle's slot, and stays readable while polled.
        assert_eq!(
            unsafe { &*frame.cast::<Counted>() }
                .0
                .load(Ordering::SeqCst),
            0
        );
        1
    }

    #[test]
    fn an_inline_wait_drops_its_frame_exactly_once() {
        // Abandoned before its first poll.
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = create_inline_wait(
            Counted(drops.clone()),
            ready_counted as *const u8,
            TaskMobility::Movable as u8,
        );
        assert_eq!(drops.load(Ordering::SeqCst), 0);
        __rt__async_destroy(handle);
        assert_eq!(drops.load(Ordering::SeqCst), 1);

        // Completed by a poll, then destroyed.
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = create_inline_wait(
            Counted(drops.clone()),
            ready_counted as *const u8,
            TaskMobility::Movable as u8,
        );
        assert_eq!(__rt__async_poll(handle, std::ptr::null_mut()), 1);
        __rt__async_destroy(handle);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn a_frame_without_drop_glue_registers_no_drop_callback() {
        let handle = __rt__async_yield_now();
        assert!(unsafe { (*AsyncHandle::of(handle)).drop_fn }.is_null());
        __rt__async_destroy(handle);
    }

    struct Frame {
        drops: Arc<AtomicUsize>,
        panics: bool,
        polls: usize,
    }
    unsafe extern "C-unwind" fn ready(_frame: *mut u8, _context: *mut u8, _output: *mut u8) -> u8 {
        1
    }
    unsafe extern "C-unwind" fn panic_poll(
        _frame: *mut u8,
        _context: *mut u8,
        _output: *mut u8,
    ) -> u8 {
        panic!("poll panic");
    }
    unsafe extern "C-unwind" fn pending_then_panic(
        frame: *mut u8,
        _context: *mut u8,
        _output: *mut u8,
    ) -> u8 {
        let frame = unsafe { &mut *frame.cast::<Frame>() };
        frame.polls += 1;
        if frame.polls == 1 {
            return 0;
        }
        panic!("poll panic");
    }
    unsafe extern "C-unwind" fn drop_frame(frame: *mut u8) {
        let frame = unsafe { Box::from_raw(frame.cast::<Frame>()) };
        frame.drops.fetch_add(1, Ordering::SeqCst);
        if frame.panics {
            panic!("frame cleanup panic");
        }
    }
    fn handle(drops: &Arc<AtomicUsize>, panics: bool, poll: *const u8) -> *mut u8 {
        __rt__async_create(
            Box::into_raw(Box::new(Frame {
                drops: drops.clone(),
                panics,
                polls: 0,
            }))
            .cast(),
            poll,
            drop_frame as *const () as *const u8,
            0,
        )
    }

    #[test]
    fn cancelling_an_unstarted_handle_never_polls_user_code() {
        let drops = Arc::new(AtomicUsize::new(0));
        // Polling would panic: cancellation must consume only constructor state.
        let handle = handle(&drops, false, panic_poll as *const () as *const u8);
        assert!(std::panic::catch_unwind(|| __rt__async_cancel(handle)).is_ok());
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(Arc::strong_count(&drops), 1);
    }

    #[test]
    fn missing_poll_still_drops_its_frame_once() {
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = handle(&drops, false, std::ptr::null());
        assert_eq!(__rt__async_poll(handle, std::ptr::null_mut()), 1);
        assert_eq!(__rt__async_poll(handle, std::ptr::null_mut()), 1);
        __rt__async_destroy(handle);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(Arc::strong_count(&drops), 1);
    }

    #[test]
    fn completion_cleanup_panic_cannot_reenter_frame_drop() {
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = handle(&drops, true, ready as *const () as *const u8);
        assert!(
            std::panic::catch_unwind(|| __rt__async_poll(handle, std::ptr::null_mut())).is_err()
        );
        // The unwinding poll consumed the handle.
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(Arc::strong_count(&drops), 1);
    }

    #[test]
    fn published_poll_reports_initialized_output_even_if_frame_cleanup_panics() {
        unsafe extern "C-unwind" fn output(_: *mut u8, _: *mut u8, out: *mut u8) -> u8 {
            unsafe { out.cast::<u64>().write(42) };
            1
        }
        for panics in [false, true] {
            let drops = Arc::new(AtomicUsize::new(0));
            let handle = handle(&drops, panics, output as *const () as *const u8);
            let published = std::sync::atomic::AtomicBool::new(false);
            let mut result = std::mem::MaybeUninit::<u64>::uninit();
            let polled = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
                __rt__async_poll_published(
                    handle,
                    result.as_mut_ptr().cast(),
                    published.as_ptr().cast(),
                )
            }));
            assert!(published.load(Ordering::Acquire));
            assert_eq!(unsafe { result.assume_init() }, 42);
            assert_eq!(polled.is_err(), panics);
            if !panics {
                __rt__async_destroy(handle);
            }
            assert_eq!(drops.load(Ordering::SeqCst), 1);
            assert_eq!(Arc::strong_count(&drops), 1);
        }
    }

    #[test]
    fn published_poll_does_not_claim_an_output_if_raw_poll_panics() {
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = handle(&drops, false, pending_then_panic as *const () as *const u8);
        let published = std::sync::atomic::AtomicBool::new(false);
        assert_eq!(
            unsafe {
                __rt__async_poll_published(handle, std::ptr::null_mut(), published.as_ptr().cast())
            },
            0
        );
        assert!(!published.load(Ordering::Acquire));
        assert!(
            std::panic::catch_unwind(|| unsafe {
                __rt__async_poll_published(handle, std::ptr::null_mut(), published.as_ptr().cast())
            })
            .is_err()
        );
        assert!(!published.load(Ordering::Acquire));
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(Arc::strong_count(&drops), 1);
    }

    #[test]
    fn cancellation_poll_panic_still_destroys_the_owned_handle() {
        let drops = Arc::new(AtomicUsize::new(0));
        let handle = handle(&drops, false, pending_then_panic as *const () as *const u8);
        assert_eq!(__rt__async_poll(handle, std::ptr::null_mut()), 0);
        assert!(std::panic::catch_unwind(|| __rt__async_cancel(handle)).is_err());
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(Arc::strong_count(&drops), 1);
    }

    #[test]
    fn cancellation_checks_cover_both_polling_and_cleanup_without_an_executor() {
        struct CancellationFrame {
            polls: usize,
            observed: Arc<AtomicUsize>,
        }
        unsafe extern "C-unwind" fn poll(frame: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
            let frame = unsafe { &mut *frame.cast::<CancellationFrame>() };
            frame.polls += 1;
            if frame.polls == 1 {
                return 0;
            }
            if crate::executor::__rt__executor_is_current_task_cancelled() {
                frame.observed.fetch_add(1, Ordering::SeqCst);
                2
            } else {
                1
            }
        }
        unsafe extern "C-unwind" fn drop_frame(frame: *mut u8) {
            let frame = unsafe { Box::from_raw(frame.cast::<CancellationFrame>()) };
            if crate::executor::__rt__executor_is_current_task_cancelled() {
                frame.observed.fetch_add(10, Ordering::SeqCst);
            }
        }
        assert!(crate::executor::current_task_token().is_none());
        for started in [false, true] {
            let observed = Arc::new(AtomicUsize::new(0));
            let frame = Box::into_raw(Box::new(CancellationFrame {
                polls: 0,
                observed: observed.clone(),
            }));
            let handle =
                __rt__async_create(frame.cast(), poll as *const u8, drop_frame as *const u8, 0);
            if started {
                assert_eq!(__rt__async_poll(handle, std::ptr::null_mut()), 0);
            }
            __rt__async_cancel(handle);
            assert_eq!(
                observed.load(Ordering::SeqCst),
                if started { 11 } else { 10 }
            );
            assert!(!crate::executor::__rt__executor_is_current_task_cancelled());
        }
    }

    #[test]
    fn forced_cancellation_is_task_specific_nested_and_unwind_safe() {
        let task = crate::executor::TaskIdentity::fixture(1, 17);
        let other_task = crate::executor::TaskIdentity::fixture(1, 18);
        let other_executor = crate::executor::TaskIdentity::fixture(2, 17);
        assert!(!forced_cancellation_for(None));
        assert!(
            std::panic::catch_unwind(|| {
                let _outer = ForcedCancellation::new();
                assert!(forced_cancellation_for(None));
                assert!(!forced_cancellation_for(Some(task)));
                {
                    // Simulate a nested cancellation poll under another context;
                    // matching is by identity, never a process-wide flag.
                    let _inner = ForcedCancellation::scoped(Some(task));
                    assert!(forced_cancellation_for(Some(task)));
                    assert!(!forced_cancellation_for(Some(other_task)));
                    assert!(!forced_cancellation_for(Some(other_executor)));
                }
                assert!(!forced_cancellation_for(Some(task)));
                panic!("cancellation poll unwind");
            })
            .is_err()
        );
        assert!(!forced_cancellation_for(None));
        assert!(!crate::executor::__rt__executor_is_current_task_cancelled());
    }

    #[test]
    fn suspended_frame_callback_has_scoped_cancellation_on_return_and_unwind() {
        unsafe extern "C-unwind" fn finish(
            frame: *mut u8,
            context: *mut u8,
            output: *mut u8,
        ) -> u8 {
            assert!(context.is_null() && output.is_null());
            let observed = unsafe { &*frame.cast::<AtomicUsize>() };
            if crate::executor::__rt__executor_is_current_task_cancelled() {
                observed.store(1, Ordering::SeqCst);
            }
            2
        }
        unsafe extern "C-unwind" fn fails(frame: *mut u8, context: *mut u8, output: *mut u8) -> u8 {
            unsafe { finish(frame, context, output) };
            panic!("suspended cleanup panic");
        }
        let mut observed = AtomicUsize::new(0);
        unsafe { __rt__async_cancel_frame((&raw mut observed).cast(), finish as *const u8) };
        assert_eq!(observed.load(Ordering::SeqCst), 1);
        observed.store(0, Ordering::SeqCst);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
                __rt__async_cancel_frame((&raw mut observed).cast(), fails as *const u8)
            }))
            .is_err()
        );
        assert_eq!(observed.load(Ordering::SeqCst), 1);
        assert!(!crate::executor::__rt__executor_is_current_task_cancelled());
    }

    #[test]
    fn ordinary_ready_during_suspended_cancellation_is_fatal() {
        const PROBE: &str = "TARO_TEST_PENDING_CANCEL_FRAME";
        if std::env::var_os(PROBE).is_none() {
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "task::ownership_tests::ordinary_ready_during_suspended_cancellation_is_fatal",
                    "--nocapture",
                ])
                .env(PROBE, "1")
                .output()
                .unwrap();
            assert!(!output.status.success());
            assert!(String::from_utf8_lossy(&output.stderr).contains("did not finish cleanup"));
            return;
        }
        unsafe extern "C-unwind" fn invalid_ready(_: *mut u8, _: *mut u8, _: *mut u8) -> u8 {
            1
        }
        let mut frame = 0u8;
        unsafe { __rt__async_cancel_frame(&raw mut frame, invalid_ready as *const u8) };
        panic!("unfinished cancellation returned");
    }
}
