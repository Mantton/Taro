//! Descriptor leases shared by every copy of a resource handle.
//!
//! An operation acquires the descriptor for exactly its own native call and
//! releases it afterwards. `close` stops new acquisitions and closes the
//! descriptor once the last in-flight operation has released it, so a
//! concurrent close can never let an operation reach a descriptor number the
//! kernel has already handed to another open. Lease ids aren't reused, and async
//! I/O sources use their lease id as their source id.

use crate::hot_mutex::HotMutex;
use std::io::Write;
use std::sync::atomic::{AtomicI32, AtomicPtr, AtomicU64, Ordering};

#[cfg(unix)]
const EBADF: i32 = libc::EBADF;
#[cfg(not(unix))]
const EBADF: i32 = 9;
#[cfg(unix)]
const EBUSY: i32 = libc::EBUSY;
#[cfg(not(unix))]
const EBUSY: i32 = 16;

// Every socket call acquires and releases a lease, from whichever worker runs it,
// so these take one atomic each and no lock. A lease's id names its slot and that
// slot's generation, and the state word holds the same generation: an id that has
// outlived its lease can't match, and can't touch the slot's next one. Generations
// would take four billion reuses of one slot to come around.
const OPEN: u64 = 1 << 30;
const CLOSING: u64 = 1 << 31;
const ACTIVE: u64 = OPEN - 1;

struct Slot {
    // Generation in the high half, then these flags and the operation count.
    state: AtomicU64,
    fd: AtomicI32,
}

const CHUNK_SLOTS: usize = 1024;
const CHUNKS: usize = 16 * 1024;
static CHUNK_TABLE: [AtomicPtr<Slot>; CHUNKS] =
    [const { AtomicPtr::new(std::ptr::null_mut()) }; CHUNKS];

#[derive(Default)]
struct Slots {
    created: usize,
    free: Vec<u32>,
}
static SLOTS: HotMutex<Slots> = HotMutex::new(Slots {
    created: 0,
    free: Vec::new(),
});
static DEFERRED_CLOSE_ERRORS: AtomicU64 = AtomicU64::new(0);

fn slot_at(index: usize) -> Option<&'static Slot> {
    let chunk = CHUNK_TABLE
        .get(index / CHUNK_SLOTS)?
        .load(Ordering::Acquire);
    // SAFETY: chunks are initialized before publication and never freed.
    (!chunk.is_null()).then(|| unsafe { &*chunk.add(index % CHUNK_SLOTS) })
}

/// An id is never zero, which callers reserve to mean no lease.
fn lease_id(index: usize, generation: u64) -> u64 {
    (generation << 32) | (index as u64 + 1)
}

/// The slot and generation an id names. Zero and forged ids find nothing.
fn split(id: u64) -> Option<(&'static Slot, usize, u64)> {
    let index = (id as u32 as usize).checked_sub(1)?;
    Some((slot_at(index)?, index, id >> 32))
}

/// A slot only returns to the free list after its generation moves on.
fn retire(index: usize) {
    SLOTS
        .lock()
        .unwrap_or_else(|poison| poison.into_inner())
        .free
        .push(index as u32);
}

/// End the lease in `state`, which only its last user can be doing. Its slot
/// can be reused once this returns, so read the descriptor first.
fn end_lease(slot: &Slot, index: usize, state: u64) -> i32 {
    let fd = slot.fd.load(Ordering::Relaxed);
    let next = ((state >> 32) + 1) << 32;
    slot.state.store(next, Ordering::Release);
    retire(index);
    fd
}

pub(crate) fn stats() -> (usize, usize, u64) {
    let created = SLOTS
        .lock()
        .unwrap_or_else(|poison| poison.into_inner())
        .created;
    let (mut open, mut closing) = (0, 0);
    for index in 0..created {
        if let Some(slot) = slot_at(index) {
            let state = slot.state.load(Ordering::Acquire);
            open += usize::from(state & OPEN != 0);
            closing += usize::from(state & CLOSING != 0);
        }
    }
    (open, closing, DEFERRED_CLOSE_ERRORS.load(Ordering::Relaxed))
}

pub(crate) fn open(fd: i32) -> u64 {
    let index = {
        let mut slots = SLOTS.lock().unwrap_or_else(|poison| poison.into_inner());
        match slots.free.pop() {
            Some(index) => index as usize,
            None => {
                let index = slots.created;
                let table = CHUNK_TABLE
                    .get(index / CHUNK_SLOTS)
                    .expect("open descriptor lease limit exceeded");
                if table.load(Ordering::Relaxed).is_null() {
                    let chunk: Box<[Slot]> = (0..CHUNK_SLOTS)
                        .map(|_| Slot {
                            state: AtomicU64::new(0),
                            fd: AtomicI32::new(-1),
                        })
                        .collect();
                    table.store(Box::into_raw(chunk).cast::<Slot>(), Ordering::Release);
                }
                slots.created += 1;
                index
            }
        }
    };
    let slot = slot_at(index).expect("a free slot's chunk exists");
    slot.fd.store(fd, Ordering::Relaxed);
    let generation = slot.state.load(Ordering::Relaxed) >> 32;
    slot.state
        .store((generation << 32) | OPEN, Ordering::Release);
    lease_id(index, generation)
}

/// Borrow the descriptor for one native operation; `Err(EBADF)` once closed.
#[inline]
pub(crate) fn acquire(id: u64) -> Result<i32, i32> {
    let Some((slot, _, generation)) = split(id) else {
        return Err(EBADF);
    };
    let mut state = slot.state.load(Ordering::Relaxed);
    loop {
        if state >> 32 != generation || state & (OPEN | CLOSING) != OPEN {
            return Err(EBADF);
        }
        match slot.state.compare_exchange_weak(
            state,
            state + 1,
            Ordering::Acquire,
            Ordering::Relaxed,
        ) {
            Ok(_) => return Ok(slot.fd.load(Ordering::Relaxed)),
            Err(actual) => state = actual,
        }
    }
}

/// End an operation. The last operation after a close closes the descriptor
/// and returns that result (0 or -errno); otherwise 0.
#[inline]
pub(crate) fn release(id: u64) -> i32 {
    let Some((slot, index, generation)) = split(id) else {
        return 0;
    };
    let mut state = slot.state.load(Ordering::Relaxed);
    loop {
        if state >> 32 != generation || state & ACTIVE == 0 {
            return 0;
        }
        match slot.state.compare_exchange_weak(
            state,
            state - 1,
            Ordering::AcqRel,
            Ordering::Relaxed,
        ) {
            Ok(_) => break,
            Err(actual) => state = actual,
        }
    }
    state -= 1;
    if state & CLOSING == 0 || state & ACTIVE != 0 {
        return 0;
    }
    let result = close_fd(end_lease(slot, index, state));
    if result < 0 {
        // The initiating close already returned under the documented deferred
        // contract. Do not silently discard a later filesystem close failure.
        DEFERRED_CLOSE_ERRORS.fetch_add(1, Ordering::Relaxed);
        // A closed stderr must not turn resource cleanup into an FFI panic.
        let _ = writeln!(
            std::io::stderr().lock(),
            "runtime: deferred descriptor close failed: errno {}",
            -result
        );
    }
    result
}

/// Close the lease: 0 or -errno when the descriptor closes now, 0 when the
/// last in-flight operation will close it, -EBADF when already closed.
pub(crate) fn close(id: u64) -> i32 {
    let Some((slot, index, generation)) = split(id) else {
        return -EBADF;
    };
    let mut state = slot.state.load(Ordering::Relaxed);
    loop {
        if state >> 32 != generation || state & (OPEN | CLOSING) != OPEN {
            return -EBADF;
        }
        match slot.state.compare_exchange_weak(
            state,
            state | CLOSING,
            Ordering::AcqRel,
            Ordering::Relaxed,
        ) {
            Ok(_) => break,
            Err(actual) => state = actual,
        }
    }
    if state & ACTIVE != 0 {
        return 0;
    }
    // Closing stops new operations and none is active, so this is the only user.
    close_fd(end_lease(slot, index, state | CLOSING))
}

/// Transfer the descriptor out of the lease without closing it. Fails with
/// -EBADF once closed and -EBUSY while an operation holds it.
pub(crate) fn take(id: u64) -> i32 {
    let Some((slot, index, generation)) = split(id) else {
        return -EBADF;
    };
    let mut state = slot.state.load(Ordering::Relaxed);
    loop {
        if state >> 32 != generation || state & (OPEN | CLOSING) != OPEN {
            return -EBADF;
        }
        if state & ACTIVE != 0 {
            return -EBUSY;
        }
        // Closing claims the lease exactly as `close` does, then it ends here.
        match slot.state.compare_exchange_weak(
            state,
            state | CLOSING,
            Ordering::AcqRel,
            Ordering::Relaxed,
        ) {
            Ok(_) => return end_lease(slot, index, state | CLOSING),
            Err(actual) => state = actual,
        }
    }
}

#[cfg(unix)]
fn close_fd(fd: i32) -> i32 {
    if fd < 0 {
        return 0;
    }
    if unsafe { libc::close(fd) } == 0 {
        return 0;
    }
    let err = std::io::Error::last_os_error()
        .raw_os_error()
        .unwrap_or(libc::EIO);
    // The descriptor is released even when close reports EINTR.
    if err == libc::EINTR { 0 } else { -err }
}

#[cfg(not(unix))]
fn close_fd(_fd: i32) -> i32 {
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fd_lease_open(fd: i32) -> u64 {
    if fd < 0 { 0 } else { open(fd) }
}

/// The descriptor, or -errno when the lease is closed.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__fd_lease_acquire(id: u64) -> i32 {
    acquire(id).unwrap_or_else(|err| -err)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fd_lease_release(id: u64) -> i32 {
    release(id)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fd_lease_close(id: u64) -> i32 {
    close(id)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fd_lease_take(id: u64) -> i32 {
    take(id)
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn pipe() -> (i32, i32) {
        // Close-on-exec: other tests spawn children, and one that inherited
        // the read end would keep it open after the lease closes it.
        let (mut read, mut write) = (-1, -1);
        assert_eq!(crate::io_poller::__rt__async_io_pipe(&mut read, &mut write), 0);
        (read, write)
    }

    fn is_open(fd: i32) -> bool {
        (unsafe { libc::fcntl(fd, libc::F_GETFD) }) != -1
    }

    #[test]
    fn an_old_id_cant_reach_the_lease_that_reuses_its_slot() {
        let (read, write) = pipe();
        let old = open(read);
        assert_eq!(close(old), 0);
        // Parallel tests share the free list, so find a lease on the same slot.
        let mut kept = Vec::new();
        let reused = loop {
            let lease = open(write);
            if lease as u32 == old as u32 {
                break lease;
            }
            kept.push(lease);
        };
        assert_ne!(reused, old);
        assert_eq!(acquire(old), Err(EBADF));
        assert_eq!(release(old), 0);
        assert_eq!(close(old), -EBADF);
        assert_eq!(take(old), -EBADF);
        assert_eq!(acquire(reused), Ok(write));
        assert_eq!(release(reused), 0);
        for lease in kept {
            assert_eq!(take(lease), write);
        }
        assert_eq!(take(reused), write);
        unsafe { libc::close(write) };
    }

    #[test]
    fn ids_that_were_never_issued_find_nothing() {
        assert_eq!(acquire(0), Err(EBADF));
        assert_eq!(close(0), -EBADF);
        assert_eq!(acquire(u64::MAX), Err(EBADF));
        assert_eq!(take(u64::MAX), -EBADF);
        assert_eq!(release(u64::MAX), 0);
    }

    #[test]
    fn exactly_one_of_many_racing_closes_wins_and_the_descriptor_closes_once() {
        for _ in 0..200 {
            let (read, write) = pipe();
            let lease = open(read);
            let barrier = std::sync::Arc::new(std::sync::Barrier::new(4));
            let threads: Vec<_> = (0..4)
                .map(|worker| {
                    let barrier = barrier.clone();
                    std::thread::spawn(move || {
                        barrier.wait();
                        if worker == 0 {
                            i32::from(close(lease) == 0)
                        } else {
                            if acquire(lease).is_ok() {
                                release(lease);
                            }
                            0
                        }
                    })
                })
                .collect();
            let closes: i32 = threads.into_iter().map(|t| t.join().unwrap()).sum();
            assert_eq!(closes, 1);
            assert_eq!(close(lease), -EBADF);
            // Parallel tests may already reuse the number, but a pipe knows its
            // read end has gone. Rust test binaries ignore SIGPIPE.
            let wrote = unsafe { libc::write(write, [0u8].as_ptr().cast(), 1) };
            assert_eq!(wrote, -1, "the read end closed");
            unsafe { libc::close(write) };
        }
    }

    #[test]
    fn close_waits_for_the_last_in_flight_operation() {
        let (read, write) = pipe();
        let lease = open(read);
        assert_eq!(acquire(lease), Ok(read));
        assert_eq!(acquire(lease), Ok(read));
        assert_eq!(close(lease), 0);
        assert!(is_open(read), "an operation still holds the descriptor");
        assert_eq!(
            acquire(lease),
            Err(EBADF),
            "closed leases admit nothing new"
        );
        assert_eq!(release(lease), 0);
        assert!(is_open(read));
        assert_eq!(release(lease), 0);
        assert!(!is_open(read), "the last release closes the descriptor");
        assert_eq!(close(lease), -EBADF);
        unsafe { libc::close(write) };
    }

    #[test]
    fn deferred_close_errors_remain_visible_after_the_initiator_returns() {
        // Never invalidate a live descriptor behind a lease: another parallel
        // test could acquire that number before release closes it again.
        let invalid = i32::MAX;
        let before = stats().2;
        let lease = open(invalid);
        assert_eq!(acquire(lease), Ok(invalid));
        assert_eq!(close(lease), 0);
        assert!(stats().0 > 0 && stats().1 > 0);
        assert_eq!(release(lease), -libc::EBADF);
        assert!(stats().2 > before);
    }

    #[test]
    fn idle_close_is_immediate_and_take_transfers_without_closing() {
        let (read, write) = pipe();
        let closed = open(read);
        assert_eq!(close(closed), 0);
        assert!(!is_open(read));

        let moved = open(write);
        assert_eq!(acquire(moved), Ok(write));
        assert_eq!(take(moved), -EBUSY);
        assert_eq!(release(moved), 0);
        assert_eq!(take(moved), write);
        assert!(is_open(write), "take hands the descriptor over open");
        assert_eq!(acquire(moved), Err(EBADF));
        unsafe { libc::close(write) };
    }
}
