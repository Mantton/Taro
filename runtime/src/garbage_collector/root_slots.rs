//! Lock-free root leases for short-lived collected objects.
//!
//! Every async call needs its frame rooted from before its inputs are captured
//! until after its cleanup and native acknowledgment. That is far too frequent
//! for the collector's mutex and root map, and a global lock would serialize
//! every worker. A lease is instead one slot in a table the collector scans.
//!
//! - Slots never move or leave the table, so a lease can be acquired on one
//!   worker and released on another. Each thread keeps its own free list and
//!   exchanges batches with a shared list, which bounds what one thread can hoard
//!   when tasks migrate in one direction.
//! - The collector reads `root` only while the world is stopped. A mutator can
//!   acquire only outside a safepoint, so it cannot race the scan, and a thread
//!   parked at a safepoint that releases a lease only clears an atomic: it
//!   no longer uses the object, so seeing either value is correct.
//! - Each slot has spare bytes, which let an async handle share its frame's
//!   lease rather than needing an allocation of its own, and hold the small
//!   native frame of a runtime waitable too.
use std::alloc::{Layout, alloc_zeroed, handle_alloc_error};
use std::cell::{Cell, UnsafeCell};
use std::mem::MaybeUninit;
use std::ptr::{self, NonNull};
use std::sync::Mutex;
use std::sync::atomic::{AtomicPtr, Ordering};

/// Bytes available to the lease's holder, aligned to eight.
pub(crate) const PAYLOAD_BYTES: usize = 120;
const CHUNK_SLOTS: usize = 256;
const BATCH: usize = 64;
const LOCAL_LIMIT: usize = BATCH * 2;

#[repr(C, align(64))]
pub(crate) struct RootSlot {
    root: AtomicPtr<u8>,
    // A free slot stores its free-list link here.
    payload: UnsafeCell<[MaybeUninit<u64>; PAYLOAD_BYTES / 8]>,
}
const _: () = assert!(size_of::<RootSlot>() == 128);
// Access is governed by the lease protocol above.
unsafe impl Sync for RootSlot {}

struct SharedSlots {
    free: *mut RootSlot,
    free_count: usize,
    chunks: Vec<*mut RootSlot>,
}
// The list and table hold stable, process-long allocations.
unsafe impl Send for SharedSlots {}

static SHARED: Mutex<SharedSlots> = Mutex::new(SharedSlots {
    free: ptr::null_mut(),
    free_count: 0,
    chunks: Vec::new(),
});

struct LocalSlots {
    free: Cell<*mut RootSlot>,
    free_count: Cell<usize>,
}
// Registered from the refill path so the hot path's thread-local has no
// destructor state to check. A slot released later, during another thread-local
// destructor, stays on the abandoned list: its root is already clear.
struct ReturnOnExit;
impl Drop for ReturnOnExit {
    fn drop(&mut self) {
        LOCAL.with(|local| {
            let count = local.free_count.replace(0);
            if count != 0 {
                donate(local.free.replace(ptr::null_mut()), count);
            }
        });
    }
}
thread_local! {
    static LOCAL: LocalSlots = const {
        LocalSlots {
            free: Cell::new(ptr::null_mut()),
            free_count: Cell::new(0),
        }
    };
    static RETURN_ON_EXIT: ReturnOnExit = const { ReturnOnExit };
}

unsafe fn next_free(slot: *mut RootSlot) -> *mut RootSlot {
    unsafe { payload(slot).cast::<*mut RootSlot>().read() }
}
unsafe fn set_next_free(slot: *mut RootSlot, next: *mut RootSlot) {
    unsafe { payload(slot).cast::<*mut RootSlot>().write(next) };
}

/// Splice a list of exactly `count` free slots onto the shared list.
fn donate(head: *mut RootSlot, count: usize) {
    let mut tail = head;
    for _ in 1..count {
        tail = unsafe { next_free(tail) };
    }
    let mut shared = SHARED.lock().unwrap_or_else(|e| e.into_inner());
    unsafe { set_next_free(tail, shared.free) };
    shared.free = head;
    shared.free_count += count;
}

#[cold]
#[inline(never)]
fn refill(local: &LocalSlots) -> *mut RootSlot {
    let _ = RETURN_ON_EXIT.try_with(|_| {});
    let mut shared = SHARED.lock().unwrap_or_else(|e| e.into_inner());
    if shared.free.is_null() {
        let layout = Layout::array::<RootSlot>(CHUNK_SLOTS).expect("root slot chunk layout");
        // Zeroed slots have a null root, which the collector skips.
        let chunk = unsafe { alloc_zeroed(layout) }.cast::<RootSlot>();
        if chunk.is_null() {
            handle_alloc_error(layout);
        }
        shared.chunks.push(chunk);
        for index in 0..CHUNK_SLOTS {
            let slot = unsafe { chunk.add(index) };
            unsafe { set_next_free(slot, shared.free) };
            shared.free = slot;
        }
        shared.free_count += CHUNK_SLOTS;
    }
    let take = shared.free_count.min(BATCH);
    let head = shared.free;
    let mut tail = head;
    for _ in 1..take {
        tail = unsafe { next_free(tail) };
    }
    shared.free = unsafe { next_free(tail) };
    shared.free_count -= take;
    drop(shared);
    // The caller takes the head; the rest become this thread's free list.
    local.free.set(unsafe { next_free(head) });
    local.free_count.set(take - 1);
    if take == 1 {
        local.free.set(ptr::null_mut());
    } else {
        unsafe { set_next_free(tail, ptr::null_mut()) };
    }
    head
}

/// Root `object` (or nothing, when null) until `release`.
#[inline]
pub(crate) fn acquire(object: *const u8) -> *mut RootSlot {
    let slot = LOCAL.with(|local| {
        let head = local.free.get();
        if head.is_null() {
            return refill(local);
        }
        local.free.set(unsafe { next_free(head) });
        local.free_count.set(local.free_count.get() - 1);
        head
    });
    unsafe { (*slot).root.store(object.cast_mut(), Ordering::Release) };
    slot
}

/// End a lease. The slot can be reused immediately.
///
/// # Safety
/// `slot` is a live `acquire` result whose payload holds nothing to drop. No
/// other reference to it survives this call. Any thread may release it.
#[inline]
pub(crate) unsafe fn release(slot: *mut RootSlot) {
    unsafe { (*slot).root.store(ptr::null_mut(), Ordering::Release) };
    LOCAL.with(|local| {
        unsafe { set_next_free(slot, local.free.get()) };
        local.free.set(slot);
        let count = local.free_count.get() + 1;
        if count <= LOCAL_LIMIT {
            local.free_count.set(count);
            return;
        }
        // Keep the newest slots, which are the likeliest to be in cache.
        let mut keep_tail = slot;
        for _ in 1..LOCAL_LIMIT - BATCH {
            keep_tail = unsafe { next_free(keep_tail) };
        }
        let donated = unsafe { next_free(keep_tail) };
        unsafe { set_next_free(keep_tail, ptr::null_mut()) };
        local.free_count.set(LOCAL_LIMIT - BATCH);
        donate(donated, count - (LOCAL_LIMIT - BATCH));
    });
}

/// The object this lease roots.
///
/// # Safety
/// `slot` is a live `acquire` result.
#[inline]
pub(crate) unsafe fn rooted(slot: *mut RootSlot) -> *mut u8 {
    unsafe { (*slot).root.load(Ordering::Acquire) }
}

/// The lease's spare storage. Its contents are the holder's until `release`.
///
/// # Safety
/// `slot` is a slot from `acquire`.
#[inline]
pub(crate) unsafe fn payload(slot: *mut RootSlot) -> *mut u8 {
    unsafe { UnsafeCell::raw_get(&raw const (*slot).payload).cast() }
}

/// Report every rooted object. Called by the collector with the world stopped.
pub(super) fn for_each_root(mut visit: impl FnMut(*const u8)) {
    let shared = SHARED.lock().unwrap_or_else(|e| e.into_inner());
    for &chunk in &shared.chunks {
        for index in 0..CHUNK_SLOTS {
            let root = unsafe { (*chunk.add(index)).root.load(Ordering::Acquire) };
            if !root.is_null() {
                visit(root.cast_const());
            }
        }
    }
}

/// A lease for a holder that needs nothing but the root itself.
pub(crate) struct RootLease(NonNull<RootSlot>);
// The slot is stable and any thread may end the lease.
unsafe impl Send for RootLease {}
impl RootLease {
    pub(crate) fn new(object: *const u8) -> Self {
        Self(unsafe { NonNull::new_unchecked(acquire(object)) })
    }
}
impl Drop for RootLease {
    fn drop(&mut self) {
        unsafe { release(self.0.as_ptr()) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn is_rooted(object: *const u8) -> bool {
        let mut found = false;
        for_each_root(|root| found |= root == object);
        found
    }

    #[test]
    fn a_lease_roots_its_object_only_until_release() {
        let object = Box::into_raw(Box::new(1u8)).cast_const();
        let slot = acquire(object);
        assert!(is_rooted(object));
        assert_eq!(unsafe { rooted(slot) }, object.cast_mut());
        unsafe { release(slot) };
        assert!(!is_rooted(object));
        drop(unsafe { Box::from_raw(object.cast_mut()) });
    }

    #[test]
    fn leases_cross_threads_and_their_slots_circulate() {
        // Every lease starts on one thread and ends on another, the worst case
        // for hoarding: without donation the acquiring thread allocates forever.
        const ROUNDS: usize = 40;
        const LEASES: usize = CHUNK_SLOTS * 3;
        let object = Box::into_raw(Box::new(2u8)) as usize;
        let chunks = || SHARED.lock().unwrap().chunks.len();
        let (to_releaser, from_acquirer) = std::sync::mpsc::channel::<Vec<usize>>();
        let (to_acquirer, from_releaser) = std::sync::mpsc::channel::<()>();
        let releaser = std::thread::spawn(move || {
            for batch in from_acquirer {
                for slot in batch {
                    unsafe { release(slot as *mut RootSlot) };
                }
                to_acquirer.send(()).unwrap();
            }
        });
        let mut after_first_round = 0;
        for round in 0..ROUNDS {
            let batch = (0..LEASES)
                .map(|_| acquire(object as *const u8) as usize)
                .collect();
            to_releaser.send(batch).unwrap();
            from_releaser.recv().unwrap();
            if round == 0 {
                after_first_round = chunks();
            }
        }
        drop(to_releaser);
        releaser.join().unwrap();
        // Parallel tests may also allocate, but nowhere near one chunk per round.
        assert!(chunks() < after_first_round + ROUNDS);
        assert!(!is_rooted(object as *const u8));
        drop(unsafe { Box::from_raw(object as *mut u8) });
    }

    #[test]
    fn finished_threads_return_their_free_slots() {
        // Each thread leaves with a free list. Lost lists would cost a chunk
        // every four threads; parallel tests can't account for that much.
        const THREADS: usize = 200;
        let chunks = || SHARED.lock().unwrap().chunks.len();
        let before = chunks();
        for _ in 0..THREADS {
            std::thread::spawn(|| {
                let slots: Vec<usize> = (0..BATCH).map(|_| acquire(ptr::null()) as usize).collect();
                for slot in slots {
                    unsafe { release(slot as *mut RootSlot) };
                }
            })
            .join()
            .unwrap();
        }
        assert!(chunks() < before + THREADS * BATCH / CHUNK_SLOTS / 2);
    }
}
