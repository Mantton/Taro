//! Stop-the-world, non-moving mark-and-sweep collector for Taro.
//!
//! # Thread Safety
//!
//! This collector uses a single global heap with stop-the-world collection
//! coordinated through per-thread safepoints. Each mutator publishes roots
//! from compiler PC maps before parking, all registered threads rendezvous
//! before collection, and the global heap remains protected by a mutex. This
//! keeps multithreaded mutation safe, but allocation and collection are still
//! globally serialized.
//!
//! # Overview
//!
//! This file implements a small, self-contained GC that is easy to reason about.
//! The pipeline is:
//!
//! 1) Allocation
//!    - Small allocations go to size-class spans (power-of-two sizes).
//!    - Large allocations get a dedicated span of pages.
//!    - A span is always either "scan" (contains pointers) or "noscan" (no pointers).
//!
//! 2) Root collection
//!    - Manual roots (gc_add_root) for embeddings/tests.
//!    - Static/global ranges (gc_register_static).
//!    - Compiler-produced stack maps, resolved and published by each mutator.
//!
//! 3) Mark
//!    - For each root pointer, find the owning span via the page map.
//!    - Mark the object slot as live.
//!    - If the span is "noscan", do not inspect object fields.
//!    - Otherwise, use GcDesc to trace pointer fields (including arrays).
//!
//! 4) Sweep
//!    - Free unmarked objects inside spans.
//!    - When a span becomes empty, return its pages to the segment.
//!
//! Key ideas:
//! - Segment: a large contiguous arena that owns the bytes and a page map.
//! - Page map: for any address, tells which span owns that page.
//! - Span: a contiguous run of pages reserved for a size class or a large object.
//! - Size class: power-of-two bucket used for small allocations.
//! - Scan/noscan lanes: separate span lists so the GC can skip scanning
//!   pointer-free objects entirely.

use std::cell::{RefCell, UnsafeCell};
use std::collections::{HashMap, VecDeque};
use std::ops::Range;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::time::{Duration, Instant};

// === Public GC surface ===

/// Describes a GC-managed type.
///
/// - size: size in bytes for a single element of this type.
/// - align: ABI alignment for a single element of this type.
/// - ptr_offsets: array of byte offsets for pointer fields within one element.
/// - ptr_count: number of pointer offsets in ptr_offsets.
///
/// For arrays/slices, the allocator provides the element desc and total size.
/// The GC will repeat the pointer offsets across the payload when needed.
#[repr(C)]
#[derive(Debug)]
pub struct GcDesc {
    pub size: usize,
    pub align: usize,
    pub ptr_offsets: *const usize,
    pub ptr_count: usize,
}

// GcDesc values are immutable and safe to share across threads.
unsafe impl Send for GcDesc {}
unsafe impl Sync for GcDesc {}

/// Runtime-only hook used to reclaim native state associated with a dead GC
/// allocation. Reclaimers never receive the allocation itself and must not
/// invoke language code.
pub(crate) type GcReclaimerFn = fn(usize);

#[derive(Clone, Copy)]
struct GcReclaimer {
    callback: GcReclaimerFn,
    data: usize,
}

#[derive(Clone, Copy)]
struct GcCleanup {
    owner: *const u8,
    handle: usize,
}

pub(crate) enum CleanupRegistration {
    Registered(usize),
    NotManaged,
    OwnerRetained,
}

#[derive(Default)]
struct CollectionWork {
    reclaimers: Vec<GcReclaimer>,
    cleanup_handles: Vec<usize>,
}

impl CollectionWork {
    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.reclaimers.is_empty() && self.cleanup_handles.is_empty()
    }
}

pub(crate) struct ThreadState {
    pub id: std::thread::ThreadId,
    /// Owned by this mutator and read by the collector only after the
    /// `at_safepoint` release/acquire handshake.
    published_roots: UnsafeCell<Vec<*const u8>>,
    pub at_safepoint: AtomicBool,
}
unsafe impl Send for ThreadState {}
unsafe impl Sync for ThreadState {}

static THREAD_REGISTRY: Mutex<Vec<Arc<ThreadState>>> = Mutex::new(Vec::new());
static THREAD_REGISTRY_EPOCH: AtomicUsize = AtomicUsize::new(0);
static THREAD_ATTACHING: AtomicUsize = AtomicUsize::new(0);
const GC_REQUESTED_FLAG: u8 = 1 << 0;
const GC_NEEDED_FLAG: u8 = 1 << 1;

/// Compiler-polled process state. A zero byte is the complete mutator fast path.
///
/// Collection requests and threshold notifications share one byte so generated
/// code needs one atomic load and one unlikely branch. Runtime slow paths use
/// read-modify-write operations to change their own bit without losing a
/// concurrent update to the other bit.
#[unsafe(export_name = "__gc__poll_flags")]
pub static GC_POLL_FLAGS: AtomicU8 = AtomicU8::new(0);

/// Whether allocation has passed the threshold at which a collection is due.
///
/// The counter and the threshold both live behind the GC mutex, but the answer
/// is read from every compiler-inserted safepoint — that is, from every loop
/// back-edge in the program. Taking the mutex there costs a lock round-trip per
/// iteration and, worse, serialises every Taro thread against a single global
/// lock even when no collection is anywhere in sight. Mirroring the answer into
/// an atomic keeps the poll's fast path to one load. It is refreshed under the
/// mutex wherever either input changes, before the allocation or collection
/// operation returns.
static GC_RESUME_COND: Condvar = Condvar::new();
static GC_RESUME_LOCK: Mutex<()> = Mutex::new(());
static GC_STRESS: OnceLock<bool> = OnceLock::new();

fn gc_stress_enabled() -> bool {
    *GC_STRESS.get_or_init(|| {
        std::env::var("TARO_GC_STRESS").ok().is_some_and(|value| {
            let value = value.trim();
            !value.is_empty() && value != "0" && !value.eq_ignore_ascii_case("false")
        })
    })
}
#[inline]
fn gc_requested(ordering: Ordering) -> bool {
    GC_POLL_FLAGS.load(ordering) & GC_REQUESTED_FLAG != 0
}

#[inline]
fn gc_needed(ordering: Ordering) -> bool {
    GC_POLL_FLAGS.load(ordering) & GC_NEEDED_FLAG != 0
}

fn set_gc_needed(needed: bool) {
    if needed || gc_stress_enabled() {
        GC_POLL_FLAGS.fetch_or(GC_NEEDED_FLAG, Ordering::Release);
    } else {
        GC_POLL_FLAGS.fetch_and(!GC_NEEDED_FLAG, Ordering::Release);
    }
}

struct CurrentThreadState {
    state: Arc<ThreadState>,
    attached: bool,
}

impl Drop for CurrentThreadState {
    fn drop(&mut self) {
        if self.attached {
            unregister_thread(&self.state);
        }
    }
}

fn register_thread_state(state: Arc<ThreadState>) -> Arc<ThreadState> {
    THREAD_ATTACHING.fetch_add(1, Ordering::AcqRel);

    {
        let mut reg = THREAD_REGISTRY.lock().unwrap();
        reg.retain(|existing| existing.id != state.id);
        reg.push(state.clone());
    }

    THREAD_REGISTRY_EPOCH.fetch_add(1, Ordering::Release);
    THREAD_ATTACHING.fetch_sub(1, Ordering::AcqRel);
    state
}

fn register_current_thread_state() -> Arc<ThreadState> {
    register_thread_state(Arc::new(ThreadState {
        id: std::thread::current().id(),
        published_roots: UnsafeCell::new(Vec::new()),
        at_safepoint: AtomicBool::new(false),
    }))
}

fn unregister_thread(state: &ThreadState) {
    // A collector may already hold this state in a registry snapshot. Publish
    // stable roots before removing the registry entry so that collector can
    // finish its wait, observe the epoch change, and retry the snapshot.
    if !state.at_safepoint.load(Ordering::Relaxed) {
        let roots = crate::stack_walk::capture_current_roots();
        unsafe { *state.published_roots.get() = roots };
        state.at_safepoint.store(true, Ordering::Release);
    }

    let mut reg = THREAD_REGISTRY.lock().unwrap();
    let len_before = reg.len();
    reg.retain(|registered| registered.id != state.id);
    if reg.len() != len_before {
        THREAD_REGISTRY_EPOCH.fetch_add(1, Ordering::Release);
    }
}

std::thread_local! {
    static CURRENT_THREAD_STATE: RefCell<Option<CurrentThreadState>> = const { RefCell::new(None) };
}

fn ensure_current_thread_state() -> Arc<ThreadState> {
    CURRENT_THREAD_STATE.with(|slot| {
        let mut slot = slot.borrow_mut();
        match slot.as_mut() {
            Some(current) => {
                if !current.attached {
                    // The thread-local state outlives explicit detach/reattach
                    // cycles (for example, the main test thread running
                    // multiple async roots). Reinsert the existing state into
                    // the global registry so later collections keep scanning
                    // this thread's published roots.
                    current.state = register_thread_state(current.state.clone());
                    current.attached = true;
                }
                current.state.clone()
            }
            None => {
                // First time this thread runs Taro code. The stack-overflow
                // handler is process-wide but its alternate stack is not, so
                // every such thread has to be guarded, and this is the one point
                // they all pass through.
                crate::stack_guard::guard_current_thread();
                let state = register_current_thread_state();
                *slot = Some(CurrentThreadState {
                    state: state.clone(),
                    attached: true,
                });
                state
            }
        }
    })
}

fn with_current_thread_state<R>(f: impl FnOnce(&ThreadState) -> R) -> R {
    let state = ensure_current_thread_state();
    f(&state)
}

fn set_current_thread_safepoint(at_safepoint: bool) {
    with_current_thread_state(|state| {
        state.at_safepoint.store(at_safepoint, Ordering::Release);
    });
}

fn publish_current_thread_roots() {
    with_current_thread_state(|state| {
        let roots = crate::stack_walk::capture_current_roots();
        // SAFETY: only the owning mutator writes this vector. A collector does
        // not read it until a release store publishes `at_safepoint`, or this
        // same thread has become the stop-the-world collector.
        unsafe { *state.published_roots.get() = roots };
    });
}

fn wait_for_gc_resume() {
    if gc_requested(Ordering::Acquire) {
        let mut guard = GC_RESUME_LOCK.lock().unwrap();
        while gc_requested(Ordering::Acquire) {
            guard = GC_RESUME_COND.wait(guard).unwrap();
        }
    }
}

/// Cancel any in-progress GC and wake all threads blocked in
/// `wait_for_gc_resume`. Called by the executor during `force_shutdown` so
/// that a worker-thread panic does not leave background workers deadlocked
/// indefinitely on the GC resume condvar.
pub(crate) fn cancel_pending_collection() {
    let _guard = GC_RESUME_LOCK.lock().unwrap();
    if gc_requested(Ordering::Acquire) {
        GC_POLL_FLAGS.fetch_and(!GC_REQUESTED_FLAG, Ordering::Release);
        GC_RESUME_COND.notify_all();
    }
}

pub(crate) fn ensure_thread_registered() {
    let should_park = CURRENT_THREAD_STATE.with(|slot| {
        let slot = slot.borrow();
        let current = slot.as_ref()?;
        if !current.attached {
            return None;
        }

        // The TLS slot owns this Arc for the lifetime of the attached thread,
        // so the poll can inspect it through the borrow without changing the
        // reference count on every safepoint.
        Some(gc_requested(Ordering::Acquire) && !current.state.at_safepoint.load(Ordering::Relaxed))
    });
    let should_park = should_park.unwrap_or_else(|| {
        // First use and explicit detach/reattach must keep going through the
        // existing registration path. In particular, registration's
        // THREAD_ATTACHING ordering coordinates with a collection already in
        // progress and must not be duplicated here.
        with_current_thread_state(|state| {
            gc_requested(Ordering::Acquire) && !state.at_safepoint.load(Ordering::Relaxed)
        })
    });
    if should_park {
        park_at_safepoint();
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __gc__thread_attach() {
    enter_safepoint();
}

/// Enter compiler-generated Taro code from a native/runtime entry point.
///
/// Entry shims pay registration once, before any managed roots can become
/// live. Compiler-inserted safepoints can then use the exported process flag as
/// their complete fast path and call `__gc__poll` only when work is pending.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__thread_enter_managed() {
    ensure_thread_registered();
    if gc_stress_enabled() {
        set_gc_needed(true);
    }
    leave_safepoint();
}

#[unsafe(no_mangle)]
pub extern "C" fn __gc__thread_detach() {
    CURRENT_THREAD_STATE.with(|slot| {
        let mut slot = slot.borrow_mut();
        if let Some(current) = slot.as_mut() {
            if current.attached {
                unregister_thread(&current.state);
                current.attached = false;
            }
        }
    });
}

pub(crate) fn enter_safepoint() {
    let already_parked =
        with_current_thread_state(|state| state.at_safepoint.load(Ordering::Relaxed));
    if already_parked {
        return;
    }
    publish_current_thread_roots();
    set_current_thread_safepoint(true);
}

pub(crate) fn leave_safepoint() {
    loop {
        // Publish that this thread intends to resume before checking the GC
        // request. If a collection is already pending, keep the published root
        // snapshot stable and wait. This ordering prevents a thread
        // from changing roots after the collector has observed it parked.
        set_current_thread_safepoint(false);
        if !gc_requested(Ordering::Acquire) {
            return;
        }
        set_current_thread_safepoint(true);
        wait_for_gc_resume();
    }
}

pub(crate) fn park_at_safepoint() {
    enter_safepoint();
    leave_safepoint();
}

/// Publish the current roots before entering a foreign call that may block
/// indefinitely.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__gc_enter_blocking() {
    enter_safepoint();
}

/// Wait for any active collection and resume Taro execution after a blocking
/// foreign call returns.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__gc_exit_blocking() {
    leave_safepoint();
}

fn snapshot_registered_threads() -> (usize, Vec<Arc<ThreadState>>) {
    let registry = THREAD_REGISTRY.lock().unwrap();
    let epoch = THREAD_REGISTRY_EPOCH.load(Ordering::Acquire);
    (epoch, registry.clone())
}

fn wait_for_registered_threads(snapshot: &[Arc<ThreadState>], current_id: std::thread::ThreadId) {
    // Registered threads cooperate with stop-the-world GC by polling,
    // allocating, entering a safepoint, or detaching before long blocking
    // native work. A registered thread that never reaches a safepoint can
    // stall collection indefinitely.
    for thread in snapshot {
        if thread.id == current_id {
            continue;
        }
        while !thread.at_safepoint.load(Ordering::Acquire) {
            std::hint::spin_loop();
            std::thread::yield_now();
        }
    }
}

fn threads_for_collection(current_id: std::thread::ThreadId) -> Vec<Arc<ThreadState>> {
    loop {
        while THREAD_ATTACHING.load(Ordering::Acquire) != 0 {
            std::hint::spin_loop();
            std::thread::yield_now();
        }

        let (epoch, snapshot) = snapshot_registered_threads();
        wait_for_registered_threads(&snapshot, current_id);

        if THREAD_ATTACHING.load(Ordering::Acquire) == 0
            && THREAD_REGISTRY_EPOCH.load(Ordering::Acquire) == epoch
        {
            return snapshot;
        }
    }
}

fn initiate_collection() {
    // Ensure only one thread acts as the collector
    if GC_POLL_FLAGS.fetch_or(GC_REQUESTED_FLAG, Ordering::AcqRel) & GC_REQUESTED_FLAG != 0 {
        park_at_safepoint();
        return;
    }
    let pause_started = Instant::now();

    let current_id = std::thread::current().id();
    // The initiating mutator is not parked (and therefore is not waited on),
    // but its generated callers are suspended inside this runtime call. Walk
    // them now while this thread still owns all of its register state.
    publish_current_thread_roots();
    let threads = threads_for_collection(current_id);

    // Now all other threads are parked. Discovery and heap reclamation happen
    // during the pause, but native resource reclaimers must wait until the
    // world is running again. Even runtime-only reclaimers may take subsystem
    // locks or wake tasks.
    let work = with_gc(|gc| gc.collect(&threads));
    let pause = pause_started.elapsed();
    with_gc(|gc| gc.record_pause(pause));

    // Wake up everyone. GC_REQUESTED_FLAG must be cleared *while holding*
    // GC_RESUME_LOCK so no thread can slip between seeing GC_REQUESTED==true
    // and calling cond.wait() without observing the notify. Clearing it before
    // acquiring the lock would open a lost-wakeup window that deadlocks the
    // thread indefinitely.
    {
        let _guard = GC_RESUME_LOCK.lock().unwrap();
        GC_POLL_FLAGS.fetch_and(!GC_REQUESTED_FLAG, Ordering::Release);
        GC_RESUME_COND.notify_all();
    }
    // Trace recording may lock and allocate, so keep it outside the
    // stop-the-world interval. The compact GC stats sample above is recorded
    // before resuming to preserve its collection identifier.
    crate::executor::record_gc_pause(pause);

    // A different mutator may request the next collection as soon as the
    // world resumes. Do not assert that the process-wide request bit remains
    // clear while the previous collection's reclaimers are running.
    for reclaimer in work.reclaimers {
        (reclaimer.callback)(reclaimer.data);
    }
    crate::cleanup::enqueue(work.cleanup_handles);
}

/// Allocate a GC-managed object with a payload of `size` bytes.
///
/// The descriptor controls pointer tracing and determines scan/noscan lane.
/// Returns null if size is 0 or desc is null.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__alloc(size: usize, desc: *const GcDesc) -> *mut u8 {
    ensure_thread_registered();
    if size == 0 || desc.is_null() {
        return std::ptr::null_mut();
    }
    let needs_gc = gc_needed(Ordering::Relaxed);
    if needs_gc {
        initiate_collection();
    }
    with_gc(|gc| gc.alloc(size, desc, false))
}

/// Allocate a GC-managed buffer for dynamic arrays/strings.
///
/// The descriptor is for a single element; total allocation is elem_size * cap.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__makebuf(desc: *const GcDesc, len: usize, cap: usize) -> *mut u8 {
    ensure_thread_registered();
    if cap < len {
        return std::ptr::null_mut();
    }
    let elem_size = unsafe { desc.as_ref() }.map(|d| d.size).unwrap_or(0);
    if elem_size == 0 {
        return std::ptr::null_mut();
    }
    let total = match elem_size.checked_mul(cap) {
        Some(n) => n,
        None => return std::ptr::null_mut(),
    };
    let scan_size = match elem_size.checked_mul(len) {
        Some(n) => n,
        None => return std::ptr::null_mut(),
    };
    if total == 0 {
        return std::ptr::null_mut();
    }
    let needs_gc = gc_needed(Ordering::Relaxed);
    if needs_gc {
        initiate_collection();
    }
    with_gc(|gc| gc.alloc_with_scan_size(total, scan_size, desc, true))
}

#[unsafe(no_mangle)]
pub extern "C" fn __gc__collect() {
    ensure_thread_registered();
    initiate_collection();
}

/// Poll for a pending collection at a compiler-inserted safepoint.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__poll() {
    ensure_thread_registered();
    let flags = GC_POLL_FLAGS.load(Ordering::Acquire);
    if flags & GC_REQUESTED_FLAG != 0 {
        park_at_safepoint();
    } else if flags & GC_NEEDED_FLAG != 0 {
        initiate_collection();
    }
}

/// Manually add a root pointer (useful for embeddings/tests).
#[unsafe(no_mangle)]
pub extern "C" fn __gc__add_root(ptr: *const u8) {
    if ptr.is_null() {
        return;
    }
    with_gc(|gc| gc.add_root(ptr));
}

/// Register a global/static memory range to be conservatively scanned.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__register_static(start: *const u8, byte_len: usize) {
    if start.is_null() || byte_len == 0 {
        return;
    }
    with_gc(|gc| gc.register_static_root(start, byte_len));
}

/// Update the initialized length of a GC-managed pointer-bearing buffer.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__set_buf_len(ptr: *mut u8, desc: *const GcDesc, len: usize) {
    if ptr.is_null() || desc.is_null() || !desc_has_pointers(desc) {
        return;
    }

    let elem_size = unsafe { desc.as_ref() }.map(|d| d.size).unwrap_or(0);
    if elem_size == 0 {
        return;
    }
    let Some(scan_size) = elem_size.checked_mul(len) else {
        return;
    };

    with_gc(|gc| gc.set_buffer_scan_size(ptr, scan_size));
}

/// Grow a GC-managed buffer to a new capacity.
///
/// Allocates a new buffer with the new capacity and copies existing data.
/// The old buffer will be collected when no longer referenced.
/// Returns the new buffer pointer, or null on failure.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__grow_buf(
    old_ptr: *mut u8,
    desc: *const GcDesc,
    old_len: usize,
    new_cap: usize,
) -> *mut u8 {
    ensure_thread_registered();
    if desc.is_null() || new_cap == 0 || old_len > new_cap {
        return std::ptr::null_mut();
    }

    let elem_size = unsafe { desc.as_ref() }.map(|d| d.size).unwrap_or(0);
    if elem_size == 0 {
        return std::ptr::null_mut();
    }

    let new_total = match elem_size.checked_mul(new_cap) {
        Some(n) => n,
        None => return std::ptr::null_mut(),
    };
    let scan_size = match elem_size.checked_mul(old_len) {
        Some(n) => n,
        None => return std::ptr::null_mut(),
    };

    let needs_gc = gc_needed(Ordering::Relaxed);
    if needs_gc {
        initiate_collection();
    }

    // Allocate new buffer
    let new_ptr = with_gc(|gc| gc.alloc_with_scan_size(new_total, scan_size, desc, true));
    if new_ptr.is_null() {
        return std::ptr::null_mut();
    }

    // Copy existing data if there is any
    if !old_ptr.is_null() && old_len > 0 {
        let Some(copy_bytes) = old_len.checked_mul(elem_size) else {
            return std::ptr::null_mut();
        };
        unsafe {
            std::ptr::copy_nonoverlapping(old_ptr, new_ptr, copy_bytes);
        }
    }

    new_ptr
}

// === Runtime GC implementation ===

// Allocation constants.
const PAGE_SIZE: usize = 8 * 1024;
const SEGMENT_SIZE: usize = 1 << 20; // 1 MiB
const SEGMENT_PAGES: usize = SEGMENT_SIZE / PAGE_SIZE;
const GC_MIN_TRIGGER: usize = SEGMENT_SIZE;
const SPAN_NONE: usize = usize::MAX;

// Contiguous run of free pages inside a segment.
struct PageRun {
    start: usize,
    len: usize,
}

// A segment is a large, page-aligned arena that owns the memory and page map.
// Spans are carved out of segments; the page_map lets us find the owning span
// for any interior pointer during marking.
struct Segment {
    // Backing storage for the segment (bytes are owned here).
    data: *mut u8,
    len: usize,
    #[cfg(test)]
    owns_memory: bool,
    // Page index -> span id for that page; SPAN_NONE means free/unassigned.
    page_map: Vec<usize>,
    // Bump pointer in pages for fresh allocation.
    next_page: usize,
    // Free page runs (when spans are returned).
    free_runs: Vec<PageRun>,
}

impl Segment {
    fn new(pages: usize) -> Self {
        // Allocate a page-aligned arena for the segment. Spans will carve pages
        // out of this arena; the segment owns the raw memory.
        let bytes = pages.saturating_mul(PAGE_SIZE);
        let layout = std::alloc::Layout::from_size_align(bytes, PAGE_SIZE).expect("segment layout");
        let data = unsafe { std::alloc::alloc_zeroed(layout) };
        if data.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        Self {
            data,
            len: bytes,
            #[cfg(test)]
            owns_memory: true,
            page_map: vec![SPAN_NONE; pages],
            next_page: 0,
            free_runs: Vec::new(),
        }
    }

    #[cfg(test)]
    fn test_fake(base: usize, len: usize) -> Self {
        Self {
            data: base as *mut u8,
            len,
            owns_memory: false,
            page_map: vec![SPAN_NONE; pages_for_size(len).max(1)],
            next_page: 0,
            free_runs: Vec::new(),
        }
    }

    fn base(&self) -> usize {
        // Base address used for page computations and range checks.
        self.data as usize
    }

    fn page_count(&self) -> usize {
        // Number of pages available in this segment.
        self.page_map.len()
    }

    // First-fit page allocation from free runs, then bump from next_page.
    fn alloc_pages(&mut self, pages: usize) -> Option<usize> {
        // Segments are the only source of pages; spans request pages from here.
        if pages == 0 {
            return None;
        }
        for i in 0..self.free_runs.len() {
            if self.free_runs[i].len >= pages {
                let start = self.free_runs[i].start;
                self.free_runs[i].start += pages;
                self.free_runs[i].len -= pages;
                if self.free_runs[i].len == 0 {
                    self.free_runs.swap_remove(i);
                }
                return Some(start);
            }
        }
        if self.next_page + pages <= self.page_count() {
            // If no free run fits, use the unallocated tail of the segment.
            let start = self.next_page;
            self.next_page += pages;
            return Some(start);
        }
        None
    }

    // Return pages to the segment and coalesce adjacent free runs.
    fn free_pages(&mut self, start: usize, pages: usize) {
        // Return a span's pages to the segment and coalesce adjacent runs.
        // Uses binary search insertion + local merge instead of full sort.
        if pages == 0 {
            return;
        }

        let end = start + pages;

        // Binary search to find insertion point (maintaining sorted order by start).
        let pos = self
            .free_runs
            .binary_search_by_key(&start, |r| r.start)
            .unwrap_or_else(|p| p);

        // Check if we can merge with the previous run.
        let merge_prev = pos > 0 && {
            let prev = &self.free_runs[pos - 1];
            prev.start + prev.len == start
        };

        // Check if we can merge with the next run.
        let merge_next = pos < self.free_runs.len() && self.free_runs[pos].start == end;

        match (merge_prev, merge_next) {
            (true, true) => {
                // Merge with both neighbors: extend prev to cover next, remove next.
                let next_end = self.free_runs[pos].start + self.free_runs[pos].len;
                self.free_runs[pos - 1].len = next_end - self.free_runs[pos - 1].start;
                self.free_runs.remove(pos);
            }
            (true, false) => {
                // Merge with previous only: extend prev.
                self.free_runs[pos - 1].len += pages;
            }
            (false, true) => {
                // Merge with next only: extend next backward.
                self.free_runs[pos].start = start;
                self.free_runs[pos].len += pages;
            }
            (false, false) => {
                // No merge possible: insert new run.
                self.free_runs.insert(pos, PageRun { start, len: pages });
            }
        }
    }

    // Record which span owns each page in this range.
    fn map_span(&mut self, span_id: usize, start_page: usize, pages: usize) {
        // Page map is used during marking to resolve interior pointers.
        for page in start_page..start_page.saturating_add(pages) {
            if let Some(entry) = self.page_map.get_mut(page) {
                *entry = span_id;
            }
        }
    }

    // Clear page ownership entries when a span is freed.
    fn unmap_span(&mut self, start_page: usize, pages: usize) {
        // Clearing the page map makes these pages appear free again.
        for page in start_page..start_page.saturating_add(pages) {
            if let Some(entry) = self.page_map.get_mut(page) {
                *entry = SPAN_NONE;
            }
        }
    }
}

impl Drop for Segment {
    fn drop(&mut self) {
        // Segments own their raw memory; free it on drop.
        #[cfg(test)]
        if !self.owns_memory {
            return;
        }
        if self.data.is_null() || self.len == 0 {
            return;
        }
        let layout =
            std::alloc::Layout::from_size_align(self.len, PAGE_SIZE).expect("segment layout");
        unsafe { std::alloc::dealloc(self.data, layout) };
        self.data = std::ptr::null_mut();
        self.len = 0;
    }
}

// A span is a contiguous range of pages reserved for either a single large
// object or a fixed-size class of small objects. Spans are marked scan/noscan
// so pointer-free allocations never get traced.
struct Span {
    // Base pointer to the span data in its segment.
    base: *mut u8,
    // Owning segment index.
    segment: usize,
    // Page range in the segment.
    start_page: usize,
    page_count: usize,
    // Size class index for small spans, None for large spans.
    class_index: Option<usize>,
    // Scan/noscan lane.
    has_pointers: bool,

    // Size of each object slot in this span.
    object_size: usize,
    // Number of slots in this span.
    object_count: usize,

    // Slot allocation and marking state. Stored as bitsets to reduce overhead.
    alloc_map: Vec<u64>,
    mark_map: Vec<u64>,
    // Bitset recording whether each slot should be treated as an array.
    array_map: Vec<u64>,

    // Per-slot metadata (only populated for scan spans).
    descs: Vec<*const GcDesc>,
    // Requested payload bytes for each slot.
    sizes: Vec<usize>,
    // Bytes the marker should trace. Array buffers may allocate more capacity
    // than their initialized length.
    scan_sizes: Vec<usize>,

    // Free list for small-object spans (indexes into slots).
    free_list: Vec<usize>,
    allocated: usize,

    // Indicates whether the span is currently in a class free-list.
    in_class_list: bool,
}

impl Span {
    // Allocate a span for a size class and prefill the free list.
    fn new_small(
        base: *mut u8,
        segment: usize,
        start_page: usize,
        page_count: usize,
        class_index: usize,
        class_size: usize,
        has_pointers: bool,
    ) -> Self {
        // A small span packs fixed-size slots for a single size class.
        let span_bytes = page_count.saturating_mul(PAGE_SIZE);
        let object_count = span_bytes / class_size;
        let bit_len = bitset_len(object_count);
        // Build a LIFO free list of slot indices for fast allocation.
        let mut free_list = Vec::with_capacity(object_count);
        for i in (0..object_count).rev() {
            free_list.push(i);
        }
        Self {
            base,
            segment,
            start_page,
            page_count,
            class_index: Some(class_index),
            has_pointers,
            object_size: class_size,
            object_count,
            alloc_map: vec![0; bit_len],
            mark_map: vec![0; bit_len],
            array_map: if has_pointers {
                vec![0; bit_len]
            } else {
                Vec::new()
            },
            descs: if has_pointers {
                vec![std::ptr::null(); object_count]
            } else {
                Vec::new()
            },
            sizes: if has_pointers {
                vec![0; object_count]
            } else {
                Vec::new()
            },
            scan_sizes: if has_pointers {
                vec![0; object_count]
            } else {
                Vec::new()
            },
            free_list,
            allocated: 0,
            in_class_list: false,
        }
    }

    // Large allocations get their own span; only one object lives here.
    fn new_large(
        base: *mut u8,
        segment: usize,
        start_page: usize,
        page_count: usize,
        payload_size: usize,
        scan_size: usize,
        desc: *const GcDesc,
        has_pointers: bool,
        is_array: bool,
    ) -> Self {
        // A large span holds exactly one object and uses whole pages.
        let span_bytes = page_count.saturating_mul(PAGE_SIZE);
        let bit_len = bitset_len(1);
        let mut alloc_map = vec![0; bit_len];
        let mark_map = vec![0; bit_len];
        bitset_set(&mut alloc_map, 0, true);
        let mut array_map = if has_pointers {
            vec![0; bit_len]
        } else {
            Vec::new()
        };
        if has_pointers && is_array {
            bitset_set(&mut array_map, 0, true);
        }
        Self {
            base,
            segment,
            start_page,
            page_count,
            class_index: None,
            has_pointers,
            object_size: span_bytes,
            object_count: 1,
            alloc_map,
            mark_map,
            array_map,
            descs: if has_pointers { vec![desc] } else { Vec::new() },
            sizes: if has_pointers {
                vec![payload_size]
            } else {
                Vec::new()
            },
            scan_sizes: if has_pointers {
                vec![scan_size.min(payload_size)]
            } else {
                Vec::new()
            },
            free_list: Vec::new(),
            allocated: 1,
            in_class_list: false,
        }
    }

    fn has_free(&self) -> bool {
        // Indicates whether there is at least one free slot.
        self.allocated < self.object_count
    }

    // Allocate one slot in a small-object span.
    fn alloc_small(
        &mut self,
        payload_size: usize,
        scan_size: usize,
        desc: *const GcDesc,
        is_array: bool,
    ) -> Option<*mut u8> {
        // Allocate from the free list and record per-slot metadata.
        debug_assert!(
            payload_size <= self.object_size,
            "payload {} exceeds span object size {}",
            payload_size,
            self.object_size
        );
        let index = self.free_list.pop()?;
        bitset_set(&mut self.alloc_map, index, true);
        bitset_set(&mut self.mark_map, index, false);
        if self.has_pointers {
            self.descs[index] = desc;
            self.sizes[index] = payload_size;
            self.scan_sizes[index] = scan_size.min(payload_size);
            bitset_set(&mut self.array_map, index, is_array);
        }
        self.allocated += 1;
        Some(unsafe { self.base.add(index * self.object_size) })
    }

    fn free_small(&mut self, index: usize) {
        // Clear metadata for the slot and push it back to the free list.
        bitset_set(&mut self.alloc_map, index, false);
        if self.has_pointers {
            self.descs[index] = std::ptr::null();
            self.sizes[index] = 0;
            self.scan_sizes[index] = 0;
            bitset_set(&mut self.array_map, index, false);
        }
        self.free_list.push(index);
        self.allocated = self.allocated.saturating_sub(1);
    }
}

const MAX_GC_PAUSE_SAMPLES: usize = 1024;

#[derive(Clone, Debug, Default)]
pub(crate) struct GcStatsSnapshot {
    pub collections: usize,
    pub total_allocations: usize,
    pub total_frees: usize,
    pub total_allocated_bytes: usize,
    pub total_freed_bytes: usize,
    pub live_objects: usize,
    pub live_bytes: usize,
    pub free_bytes: usize,
    pub segment_bytes: usize,
    pause_samples: Vec<(usize, u64)>,
}

impl GcStatsSnapshot {
    pub(crate) fn pause_nanos_since(&self, collection: usize) -> Vec<u64> {
        self.pause_samples
            .iter()
            .filter_map(|(sample_collection, nanos)| {
                (*sample_collection > collection).then_some(*nanos)
            })
            .collect()
    }
}

#[derive(Debug, Default)]
struct GcStats {
    collections: usize,
    total_allocations: usize,
    total_frees: usize,
    total_allocated_bytes: usize,
    total_freed_bytes: usize,
    live_objects: usize,
    live_bytes: usize,
    free_runs: usize,
    free_bytes: usize,
    last_freed_objects: usize,
    last_freed_bytes: usize,
    last_segment_count: usize,
    last_segment_bytes: usize,
    pause_samples: VecDeque<(usize, u64)>,
}

impl GcStats {
    fn record_alloc(&mut self, size: usize) {
        self.total_allocations += 1;
        self.total_allocated_bytes = self.total_allocated_bytes.saturating_add(size);
        self.live_objects += 1;
        self.live_bytes = self.live_bytes.saturating_add(size);
    }

    fn record_free(&mut self, size: usize) {
        self.total_frees += 1;
        self.total_freed_bytes = self.total_freed_bytes.saturating_add(size);
        self.live_objects = self.live_objects.saturating_sub(1);
        self.live_bytes = self.live_bytes.saturating_sub(size);
    }

    fn record_collection(
        &mut self,
        freed_objects: usize,
        freed_bytes: usize,
        free_runs: usize,
        free_bytes: usize,
        segment_count: usize,
        segment_bytes: usize,
    ) {
        self.collections += 1;
        self.last_freed_objects = freed_objects;
        self.last_freed_bytes = freed_bytes;
        self.free_runs = free_runs;
        self.free_bytes = free_bytes;
        self.last_segment_count = segment_count;
        self.last_segment_bytes = segment_bytes;
    }

    fn record_pause(&mut self, pause: Duration) {
        if self.pause_samples.len() == MAX_GC_PAUSE_SAMPLES {
            let _ = self.pause_samples.pop_front();
        }
        let nanos = pause.as_nanos().min(u64::MAX as u128) as u64;
        self.pause_samples.push_back((self.collections, nanos));
    }

    fn snapshot(&self) -> GcStatsSnapshot {
        GcStatsSnapshot {
            collections: self.collections,
            total_allocations: self.total_allocations,
            total_frees: self.total_frees,
            total_allocated_bytes: self.total_allocated_bytes,
            total_freed_bytes: self.total_freed_bytes,
            live_objects: self.live_objects,
            live_bytes: self.live_bytes,
            free_bytes: self.free_bytes,
            segment_bytes: self.last_segment_bytes,
            pause_samples: self.pause_samples.iter().copied().collect(),
        }
    }

    fn log(&self) {
        if std::env::var("TARO_GC_STATS").map_or(false, |val| val == "1") {
            eprintln!(
                "gc: collections={} live_objects={} live_bytes={} last_freed_objects={} last_freed_bytes={} free_runs={} free_bytes={} segments={} segment_bytes={} total_allocs={} total_frees={} total_alloc_bytes={} total_freed_bytes={}",
                self.collections,
                self.live_objects,
                self.live_bytes,
                self.last_freed_objects,
                self.last_freed_bytes,
                self.free_runs,
                self.free_bytes,
                self.last_segment_count,
                self.last_segment_bytes,
                self.total_allocations,
                self.total_frees,
                self.total_allocated_bytes,
                self.total_freed_bytes,
            );
        }
    }
}

#[derive(Debug, Default)]
struct SweepStats {
    objects: usize,
    bytes: usize,
}

// Top-level GC state. Spans are stored separately so the page map can store
// just a span id, and the class lists track spans with free slots.
pub(crate) struct Gc {
    segments: Vec<Segment>,
    // Maps arena index (address / SEGMENT_SIZE) to candidate segment indices.
    // Segments are page-aligned, not SEGMENT_SIZE-aligned, so multiple segments
    // can share an arena bucket and large segments can span multiple buckets.
    arena_map: HashMap<usize, Vec<usize>>,
    spans: Vec<Option<Span>>,
    // Free list of span IDs for reuse (prevents unbounded growth of spans vec).
    free_span_ids: Vec<usize>,
    size_classes: Vec<usize>,
    // Per size class: [scan spans, noscan spans].
    class_spans: Vec<[Vec<usize>; 2]>,
    static_roots: Vec<Range<*const u8>>,
    manual_roots: Vec<*const u8>,
    persistent_roots: HashMap<*const u8, usize>,
    reclaimers: HashMap<*const u8, GcReclaimer>,
    cleanups: HashMap<usize, GcCleanup>,
    cleanup_tokens_by_owner: HashMap<*const u8, Vec<usize>>,
    // Weak cells do not trace their targets. This side table lets the mark
    // phase clear cells whose canonical owner is about to be reclaimed.
    weak_cells_by_owner: HashMap<*const u8, Vec<usize>>,
    next_cleanup_token: usize,
    stats: GcStats,
    // Bytes allocated since the last collection (used to trigger GC).
    alloc_since_gc: usize,
    // Next allocation threshold that triggers a collection.
    gc_threshold_bytes: usize,
}

// GC is only accessed under a Mutex; raw pointers are fine.
unsafe impl Send for Gc {}
unsafe impl Sync for Gc {}

impl Gc {
    fn new() -> Self {
        // Initialize size classes, span lists, and the first segment.
        debug_assert!(SEGMENT_SIZE % PAGE_SIZE == 0);
        let size_classes = build_size_classes();
        let mut class_spans = Vec::with_capacity(size_classes.len());
        for _ in 0..size_classes.len() {
            class_spans.push([Vec::new(), Vec::new()]);
        }
        let segments = vec![Segment::new(SEGMENT_PAGES)];

        // Register the first segment in the arena map.
        let mut arena_map = HashMap::new();
        register_segment_arenas(&mut arena_map, &segments[0], 0);

        Self {
            segments,
            arena_map,
            spans: Vec::new(),
            free_span_ids: Vec::new(),
            size_classes,
            class_spans,
            static_roots: Vec::new(),
            manual_roots: Vec::new(),
            persistent_roots: HashMap::new(),
            reclaimers: HashMap::new(),
            cleanups: HashMap::new(),
            cleanup_tokens_by_owner: HashMap::new(),
            weak_cells_by_owner: HashMap::new(),
            next_cleanup_token: 2,
            stats: GcStats::default(),
            alloc_since_gc: 0,
            gc_threshold_bytes: GC_MIN_TRIGGER,
        }
    }

    fn add_root(&mut self, ptr: *const u8) {
        // Manual roots are consumed on the next collection.
        self.manual_roots.push(ptr);
    }

    fn register_static_root(&mut self, start: *const u8, byte_len: usize) {
        let Some(end_addr) = (start as usize).checked_add(byte_len) else {
            return;
        };
        let range = start..(end_addr as *const u8);
        if !self
            .static_roots
            .iter()
            .any(|existing| existing.start == range.start && existing.end == range.end)
        {
            self.static_roots.push(range);
        }
    }

    // Route small allocations to size-class spans; large allocations get a span.
    // payload_size is the requested size, alloc_size is rounded up for alignment.
    fn alloc(&mut self, size: usize, desc: *const GcDesc, is_array: bool) -> *mut u8 {
        self.alloc_with_scan_size(size, size, desc, is_array)
    }

    fn alloc_with_scan_size(
        &mut self,
        size: usize,
        scan_size: usize,
        desc: *const GcDesc,
        is_array: bool,
    ) -> *mut u8 {
        // Compute allocation size with alignment and choose the scan lane.
        let payload_size = size;
        let scan_size = scan_size.min(payload_size);
        let align = desc_alignment(desc).max(std::mem::size_of::<usize>());
        let alloc_size = align_up(payload_size, align);
        let has_pointers = desc_has_pointers(desc);

        // Small allocations go through size-class spans; large ones get whole pages.
        let (ptr, alloc_bytes) = if alloc_size > PAGE_SIZE {
            self.alloc_large(
                payload_size,
                scan_size,
                alloc_size,
                desc,
                has_pointers,
                is_array,
            )
        } else {
            self.alloc_small(
                payload_size,
                scan_size,
                alloc_size,
                desc,
                has_pointers,
                is_array,
            )
        };

        self.after_alloc(alloc_bytes);
        ptr
    }

    // Allocate from a span that has free slots for this size class.
    fn alloc_small(
        &mut self,
        payload_size: usize,
        scan_size: usize,
        alloc_size: usize,
        desc: *const GcDesc,
        has_pointers: bool,
        is_array: bool,
    ) -> (*mut u8, usize) {
        // Pick a size class and scan/noscan lane, then allocate from a span.
        let class_index = size_class_for(alloc_size, &self.size_classes);
        let class_size = self.size_classes[class_index];
        let lane = span_lane(has_pointers);
        let span_id = self.take_span_for_class(class_index, lane);
        let span = self.spans[span_id].as_mut().expect("span exists");
        let ptr = span
            .alloc_small(payload_size, scan_size, desc, is_array)
            .expect("span has free slot");
        if span.has_free() && !span.in_class_list {
            self.class_spans[class_index][lane].push(span_id);
            span.in_class_list = true;
        }
        (ptr, class_size)
    }

    // Large objects: allocate whole pages and track a single live object.
    fn alloc_large(
        &mut self,
        payload_size: usize,
        scan_size: usize,
        alloc_size: usize,
        desc: *const GcDesc,
        has_pointers: bool,
        is_array: bool,
    ) -> (*mut u8, usize) {
        // Large allocations use whole pages and get a dedicated span.
        let pages = pages_for_size(alloc_size);
        let (segment, start_page, base) = self.alloc_pages(pages);
        let span_id = self.alloc_span_id();
        self.segments[segment].map_span(span_id, start_page, pages);
        let span = Span::new_large(
            base,
            segment,
            start_page,
            pages,
            payload_size,
            scan_size,
            desc,
            has_pointers,
            is_array,
        );
        let total_bytes = pages.saturating_mul(PAGE_SIZE);
        self.spans[span_id] = Some(span);
        (base, total_bytes)
    }

    // Update stats after allocation.
    fn after_alloc(&mut self, alloc_bytes: usize) {
        // Update stats and allow safepoints to decide when to collect.
        self.stats.record_alloc(alloc_bytes);
        self.alloc_since_gc = self.alloc_since_gc.saturating_add(alloc_bytes);
        self.refresh_gc_needed();
    }

    /// Republishes whether a collection is due, for safepoints to read without
    /// taking the mutex this runs under.
    fn refresh_gc_needed(&self) {
        set_gc_needed(self.alloc_since_gc >= self.gc_threshold_bytes);
    }

    fn alloc_weak_cell(&mut self, target: *const u8) -> *mut u8 {
        let desc = crate::weak::cell_desc();
        let cell = self.alloc(desc.size, desc, false);
        unsafe { crate::weak::initialize_cell(cell, target) };

        // Interior pointers share the lifetime of their containing object, so
        // index the cell by the canonical allocation base while preserving the
        // original target address in the cell.
        if let Some(owner) = self.object_base(target) {
            self.weak_cells_by_owner
                .entry(owner)
                .or_default()
                .push(cell as usize);
        }
        cell
    }

    fn alloc_span_id(&mut self) -> usize {
        // Reuse freed span IDs to prevent unbounded growth of the spans vector.
        if let Some(id) = self.free_span_ids.pop() {
            debug_assert!(self.spans[id].is_none(), "reused span ID must be empty");
            return id;
        }
        self.spans.push(None);
        self.spans.len() - 1
    }

    fn free_span_id(&mut self, id: usize) {
        // Return the span ID to the free list for reuse.
        debug_assert!(self.spans[id].is_none(), "freed span ID must be empty");
        self.free_span_ids.push(id);
    }

    // Reuse a span with free slots or create a new one for this class.
    fn take_span_for_class(&mut self, class_index: usize, lane: usize) -> usize {
        // Pop spans from the per-class list until a live, reusable span is found.
        let list = &mut self.class_spans[class_index][lane];
        while let Some(span_id) = list.pop() {
            if let Some(span) = self.spans.get_mut(span_id).and_then(|s| s.as_mut()) {
                span.in_class_list = false;
                let span_matches_class = span.class_index == Some(class_index);
                let span_matches_lane = span_lane(span.has_pointers) == lane;
                if span_matches_class && span_matches_lane && span.has_free() {
                    return span_id;
                }
            }
        }
        self.new_small_span(class_index, lane)
    }

    // Carve a new span from the segment for a size class.
    fn new_small_span(&mut self, class_index: usize, lane: usize) -> usize {
        // Request a page from a segment and create a fresh span.
        let class_size = self.size_classes[class_index];
        let pages = 1;
        let (segment, start_page, base) = self.alloc_pages(pages);
        let span_id = self.alloc_span_id();
        self.segments[segment].map_span(span_id, start_page, pages);
        let has_pointers = lane == 0;
        let span = Span::new_small(
            base,
            segment,
            start_page,
            pages,
            class_index,
            class_size,
            has_pointers,
        );
        self.spans[span_id] = Some(span);
        span_id
    }

    // Find or create a segment that can satisfy this page request.
    fn alloc_pages(&mut self, pages: usize) -> (usize, usize, *mut u8) {
        // Segments are the only source of pages; spans are carved from segments.
        for (index, segment) in self.segments.iter_mut().enumerate() {
            if let Some(start_page) = segment.alloc_pages(pages) {
                let base = unsafe { segment.data.add(start_page * PAGE_SIZE) };
                return (index, start_page, base);
            }
        }
        let new_pages = pages.max(SEGMENT_PAGES);
        self.segments.push(Segment::new(new_pages));
        let index = self.segments.len() - 1;
        register_segment_arenas(&mut self.arena_map, &self.segments[index], index);
        let segment = &mut self.segments[index];
        let start_page = segment.alloc_pages(pages).expect("new segment has space");
        let base = unsafe { segment.data.add(start_page * PAGE_SIZE) };
        (index, start_page, base)
    }

    // Segment lookup via arena bucket candidates.
    fn segment_index_for_ptr(&self, ptr: *const u8) -> Option<usize> {
        let p = ptr as usize;
        let arena = p / SEGMENT_SIZE;
        let candidates = self.arena_map.get(&arena)?;
        for &index in candidates {
            // Verify the pointer is actually within this segment's bounds.
            let Some(segment) = self.segments.get(index) else {
                continue;
            };
            let base = segment.base();
            let Some(offset) = p.checked_sub(base) else {
                continue;
            };
            if offset < segment.len {
                return Some(index);
            }
        }
        None
    }

    pub(crate) fn add_persistent_root(&mut self, ptr: *const u8) {
        if !ptr.is_null() {
            let entry = self.persistent_roots.entry(ptr).or_insert(0);
            *entry = entry
                .checked_add(1)
                .expect("persistent root refcount overflow");
        }
    }

    pub(crate) fn remove_persistent_root(&mut self, ptr: *const u8) {
        if ptr.is_null() {
            return;
        }

        let mut remove = false;
        if let Some(count) = self.persistent_roots.get_mut(&ptr) {
            if *count == 1 {
                remove = true;
            } else {
                *count -= 1;
            }
        } else {
            debug_assert!(false, "persistent root removal without matching add");
            return;
        }

        if remove {
            self.persistent_roots.remove(&ptr);
        }
    }

    pub(crate) fn register_reclaimer(
        &mut self,
        ptr: *const u8,
        callback: GcReclaimerFn,
        data: usize,
    ) {
        if ptr.is_null() {
            return;
        }
        let previous = self.reclaimers.insert(ptr, GcReclaimer { callback, data });
        debug_assert!(previous.is_none(), "GC object reclaimer registered twice");
    }

    pub(crate) fn unregister_reclaimer(&mut self, ptr: *const u8) {
        if !ptr.is_null() {
            self.reclaimers.remove(&ptr);
        }
    }

    pub(crate) fn register_cleanup(
        &mut self,
        owner: *const u8,
        frame: *const u8,
        handle: *mut u8,
    ) -> CleanupRegistration {
        let Some(owner) = self.object_base(owner) else {
            return CleanupRegistration::NotManaged;
        };
        if frame.is_null() || self.object_directly_references(frame, owner) {
            return CleanupRegistration::OwnerRetained;
        }

        let token = self.next_cleanup_token();
        self.cleanups.insert(
            token,
            GcCleanup {
                owner,
                handle: handle as usize,
            },
        );
        self.cleanup_tokens_by_owner
            .entry(owner)
            .or_default()
            .push(token);
        CleanupRegistration::Registered(token)
    }

    pub(crate) fn cancel_cleanup(&mut self, token: usize) -> Option<usize> {
        let cleanup = self.cleanups.remove(&token)?;
        let mut remove_owner = false;
        if let Some(tokens) = self.cleanup_tokens_by_owner.get_mut(&cleanup.owner) {
            tokens.retain(|candidate| *candidate != token);
            remove_owner = tokens.is_empty();
        }
        if remove_owner {
            self.cleanup_tokens_by_owner.remove(&cleanup.owner);
        }
        Some(cleanup.handle)
    }

    fn next_cleanup_token(&mut self) -> usize {
        loop {
            let token = self.next_cleanup_token.max(2);
            self.next_cleanup_token = token.checked_add(1).unwrap_or(2);
            if !self.cleanups.contains_key(&token) {
                return token;
            }
        }
    }

    fn take_cleanup_handles(&mut self, owner: *const u8, output: &mut Vec<usize>) {
        let Some(tokens) = self.cleanup_tokens_by_owner.remove(&owner) else {
            return;
        };
        for token in tokens {
            if let Some(cleanup) = self.cleanups.remove(&token) {
                output.push(cleanup.handle);
            }
        }
    }

    fn object_directly_references(&self, object: *const u8, target: *const u8) -> bool {
        let Some((span_id, object_index)) = self.find_object(object) else {
            return false;
        };
        let Some(span) = self.spans.get(span_id).and_then(Option::as_ref) else {
            return false;
        };
        if !span.has_pointers || !bitset_get(&span.alloc_map, object_index) {
            return false;
        }
        let Some(desc) = (unsafe { span.descs[object_index].as_ref() }) else {
            return false;
        };
        let base = unsafe { span.base.add(object_index * span.object_size) };
        let limit = span.scan_sizes[object_index].min(span.sizes[object_index]);
        for index in 0..desc.ptr_count {
            let offset = unsafe { *desc.ptr_offsets.add(index) };
            if offset >= limit {
                continue;
            }
            let candidate =
                unsafe { std::ptr::read_unaligned(base.add(offset) as *const *const u8) };
            if self.object_base(candidate) == Some(target) {
                return true;
            }
        }
        false
    }

    fn set_buffer_scan_size(&mut self, ptr: *mut u8, scan_size: usize) {
        let Some((span_id, object_index)) = self.find_object(ptr.cast_const()) else {
            return;
        };
        let Some(span) = self.spans.get_mut(span_id).and_then(|s| s.as_mut()) else {
            return;
        };
        if !span.has_pointers
            || !bitset_get(&span.alloc_map, object_index)
            || !bitset_get(&span.array_map, object_index)
        {
            return;
        }
        if scan_size <= span.sizes[object_index] {
            span.scan_sizes[object_index] = scan_size;
        }
    }

    fn collect(&mut self, threads: &[Arc<ThreadState>]) -> CollectionWork {
        // Stop-the-world collection: gather roots, mark, then sweep.
        let mut manual_roots = std::mem::take(&mut self.manual_roots);
        let static_roots = std::mem::take(&mut self.static_roots);
        manual_roots.extend(self.persistent_roots.keys().copied());
        self.mark_roots(manual_roots.into_iter(), &static_roots, threads);
        self.static_roots = static_roots;
        self.process_weak_cells();
        let (freed, reclaimers, cleanup_handles) = self.sweep();
        let (free_runs, free_pages) = self.free_page_stats();
        let segment_count = self.segments.len();
        self.stats.record_collection(
            freed.objects,
            freed.bytes,
            free_runs,
            free_pages.saturating_mul(PAGE_SIZE),
            segment_count,
            segment_count.saturating_mul(SEGMENT_SIZE),
        );
        self.stats.log();
        self.alloc_since_gc = 0;
        self.gc_threshold_bytes = next_gc_threshold(self.stats.live_bytes);
        self.refresh_gc_needed();
        CollectionWork {
            reclaimers,
            cleanup_handles,
        }
    }

    fn record_pause(&mut self, pause: Duration) {
        self.stats.record_pause(pause);
    }

    fn mark_roots<I>(
        &mut self,
        manual_roots: I,
        static_roots: &[Range<*const u8>],
        threads: &[Arc<ThreadState>],
    ) where
        I: IntoIterator<Item = *const u8>,
    {
        // Pre-allocate the mark stack to avoid reallocations during tracing.
        // 1024 pointers handles most workloads; deep graphs will still grow.
        const INITIAL_STACK_CAPACITY: usize = 1024;
        let mut stack: Vec<*const u8> = Vec::with_capacity(INITIAL_STACK_CAPACITY);
        stack.extend(manual_roots);

        for range in static_roots {
            // Conservative scan over the static range, word by word.
            let mut p = range.start as usize;
            let end = range.end as usize;
            while p + std::mem::size_of::<usize>() <= end {
                let word = p as *const usize;
                let candidate = unsafe { std::ptr::read_unaligned(word) } as *const u8;
                stack.push(candidate);
                p += std::mem::size_of::<usize>();
            }
        }

        self.push_published_roots(&mut stack, threads);
        self.trace_stack(&mut stack);
    }

    fn process_weak_cells(&mut self) {
        // Mark bits are still available here. Drop unreachable cells from the
        // side table, retain live cells for live owners, and clear live cells
        // for dead owners before sweep makes either address reusable.
        let registrations = std::mem::take(&mut self.weak_cells_by_owner);
        for (owner, cells) in registrations {
            let owner_is_live = self.object_is_marked(owner);
            let mut retained = Vec::new();
            for cell in cells {
                let cell = cell as *mut u8;
                if !self.object_is_marked(cell.cast_const()) {
                    continue;
                }
                if owner_is_live {
                    retained.push(cell as usize);
                } else {
                    crate::weak::clear_cell(cell);
                }
            }
            if !retained.is_empty() {
                self.weak_cells_by_owner.insert(owner, retained);
            }
        }
    }

    fn trace_stack(&mut self, stack: &mut Vec<*const u8>) {
        // Iterative DFS to avoid recursion in the mark phase.
        while let Some(ptr) = stack.pop() {
            self.mark_ptr(ptr, stack);
        }
    }

    // Use the page map to resolve an interior pointer to its span + slot.
    fn mark_ptr(&mut self, ptr: *const u8, stack: &mut Vec<*const u8>) {
        // Resolve the pointer to a span slot and mark it live.
        if ptr.is_null() {
            return;
        }
        let (span_id, object_index) = match self.find_object(ptr) {
            Some(hit) => hit,
            None => return,
        };
        let Some(span) = self.spans.get_mut(span_id).and_then(|s| s.as_mut()) else {
            return;
        };
        if !bitset_get(&span.alloc_map, object_index) {
            return;
        }
        if bitset_get(&span.mark_map, object_index) {
            return;
        }
        bitset_set(&mut span.mark_map, object_index, true);
        if !span.has_pointers {
            // Noscan spans contain no pointers, so no further tracing.
            return;
        }
        let desc = unsafe { span.descs[object_index].as_ref() };
        let Some(desc) = desc else {
            return;
        };
        if desc.ptr_count == 0 {
            return;
        }

        let payload_size = span.sizes[object_index];
        let scan_size = span.scan_sizes[object_index].min(payload_size);
        let base = unsafe { span.base.add(object_index * span.object_size) };
        let elem_size = desc.size;
        let is_array = bitset_get(&span.array_map, object_index);

        if is_array && elem_size != 0 {
            // Arrays/slices: apply field offsets for each element.
            let count = scan_size / elem_size;
            for index in 0..count {
                let elem_base = unsafe { base.add(index * elem_size) };
                self.push_pointer_fields(elem_base, elem_size, desc, stack);
            }
        } else {
            // Single object: trace pointer fields once.
            self.push_pointer_fields(base, scan_size, desc, stack);
        }
    }

    fn push_pointer_fields(
        &self,
        base: *mut u8,
        limit: usize,
        desc: &GcDesc,
        stack: &mut Vec<*const u8>,
    ) {
        // Read each pointer field and push it onto the mark stack.
        for i in 0..desc.ptr_count {
            let off = unsafe { *desc.ptr_offsets.add(i) };
            if off < limit {
                let field_ptr = unsafe { base.add(off) };
                let val = unsafe { std::ptr::read_unaligned(field_ptr as *const *const u8) };
                stack.push(val);
            }
        }
    }

    fn push_published_roots(&self, stack: &mut Vec<*const u8>, threads: &[Arc<ThreadState>]) {
        for thread in threads {
            // The collector either observed this thread parked with Acquire,
            // or is reading its own buffer after synchronously publishing it.
            let roots = unsafe { &*thread.published_roots.get() };
            stack.extend(roots.iter().copied().filter(|root| !root.is_null()));
        }
    }

    // Sweep spans: free unmarked slots, and return empty spans to the segment.
    fn sweep(&mut self) -> (SweepStats, Vec<GcReclaimer>, Vec<usize>) {
        // Sweep spans: free unmarked slots, return empty spans to segments.
        let mut freed = SweepStats::default();
        let mut reclaimers = Vec::new();
        let mut cleanup_handles = Vec::new();
        for span_id in 0..self.spans.len() {
            let Some(mut span) = self.spans[span_id].take() else {
                continue;
            };

            // Large span: single slot at index 0.
            if span.class_index.is_none() {
                // If the lone object is unmarked, free the entire span.
                if bitset_get(&span.alloc_map, 0) && !bitset_get(&span.mark_map, 0) {
                    let total_bytes = span.page_count.saturating_mul(PAGE_SIZE);
                    if let Some(reclaimer) = self.reclaimers.remove(&(span.base as *const u8)) {
                        reclaimers.push(reclaimer);
                    }
                    self.take_cleanup_handles(span.base as *const u8, &mut cleanup_handles);
                    bitset_set(&mut span.alloc_map, 0, false);
                    if span.has_pointers && !span.descs.is_empty() {
                        span.descs[0] = std::ptr::null();
                        span.sizes[0] = 0;
                        span.scan_sizes[0] = 0;
                    }
                    span.allocated = 0;
                    self.stats.record_free(total_bytes);
                    freed.objects += 1;
                    freed.bytes = freed.bytes.saturating_add(total_bytes);
                    self.free_span_pages(&span);
                    self.free_span_id(span_id);
                    continue;
                }
                bitset_set(&mut span.mark_map, 0, false);
                self.spans[span_id] = Some(span);
                continue;
            }

            // Small span: sweep each slot.
            for index in 0..span.object_count {
                if !bitset_get(&span.alloc_map, index) {
                    continue;
                }
                if bitset_get(&span.mark_map, index) {
                    // Live object: clear mark bit for the next cycle.
                    bitset_set(&mut span.mark_map, index, false);
                    continue;
                }
                let object = unsafe { span.base.add(index * span.object_size) } as *const u8;
                if let Some(reclaimer) = self.reclaimers.remove(&object) {
                    reclaimers.push(reclaimer);
                }
                self.take_cleanup_handles(object, &mut cleanup_handles);
                span.free_small(index);
                self.stats.record_free(span.object_size);
                freed.objects += 1;
                freed.bytes = freed.bytes.saturating_add(span.object_size);
            }

            // If empty, return the span to the segment.
            if span.allocated == 0 {
                self.free_span_pages(&span);
                self.free_span_id(span_id);
                continue;
            }

            // If not full, track it in the class free list for reuse.
            if span.has_free() && !span.in_class_list {
                if let Some(class_index) = span.class_index {
                    let lane = span_lane(span.has_pointers);
                    self.class_spans[class_index][lane].push(span_id);
                    span.in_class_list = true;
                }
            }

            self.spans[span_id] = Some(span);
        }
        (freed, reclaimers, cleanup_handles)
    }

    // Return an entire span's pages to its owning segment.
    fn free_span_pages(&mut self, span: &Span) {
        // Release the span's pages back to its owning segment.
        let segment = &mut self.segments[span.segment];
        segment.unmap_span(span.start_page, span.page_count);
        segment.free_pages(span.start_page, span.page_count);
    }

    // Resolve a raw pointer to (span_id, object_index) if it lives in the heap.
    fn find_object(&self, ptr: *const u8) -> Option<(usize, usize)> {
        // Use the segment index and page map to resolve pointer -> span slot.
        let segment_index = self.segment_index_for_ptr(ptr)?;
        let segment = &self.segments[segment_index];
        let page = ((ptr as usize).saturating_sub(segment.base())) / PAGE_SIZE;
        let span_id = *segment.page_map.get(page)?;
        if span_id == SPAN_NONE {
            return None;
        }
        let span = self.spans.get(span_id)?.as_ref()?;
        let offset = (ptr as usize).saturating_sub(span.base as usize);
        let span_bytes = span.page_count.saturating_mul(PAGE_SIZE);
        if offset >= span_bytes {
            return None;
        }
        let object_index = if span.object_size == 0 {
            0
        } else {
            offset / span.object_size
        };
        if object_index >= span.object_count {
            return None;
        }
        Some((span_id, object_index))
    }

    fn object_base(&self, ptr: *const u8) -> Option<*const u8> {
        let (span_id, object_index) = self.find_object(ptr)?;
        let span = self.spans.get(span_id)?.as_ref()?;
        bitset_get(&span.alloc_map, object_index)
            .then(|| unsafe { span.base.add(object_index * span.object_size) as *const u8 })
    }

    fn object_is_marked(&self, ptr: *const u8) -> bool {
        let Some((span_id, object_index)) = self.find_object(ptr) else {
            return false;
        };
        let Some(span) = self.spans.get(span_id).and_then(Option::as_ref) else {
            return false;
        };
        bitset_get(&span.alloc_map, object_index) && bitset_get(&span.mark_map, object_index)
    }

    fn free_page_stats(&self) -> (usize, usize) {
        // Sum free pages/runs across all segments for logging.
        let mut runs: usize = 0;
        let mut pages: usize = 0;
        for segment in &self.segments {
            runs = runs.saturating_add(segment.free_runs.len());
            pages = pages.saturating_add(segment.free_runs.iter().map(|r| r.len).sum::<usize>());
            if segment.next_page < segment.page_count() {
                runs = runs.saturating_add(1);
                pages = pages.saturating_add(segment.page_count() - segment.next_page);
            }
        }
        (runs, pages)
    }
}

pub(crate) fn with_gc<R>(f: impl FnOnce(&mut Gc) -> R) -> R {
    // Single global GC instance protected by a mutex.
    static INSTANCE: OnceLock<Mutex<Gc>> = OnceLock::new();
    let gc = INSTANCE.get_or_init(|| Mutex::new(Gc::new()));
    let mut guard = gc.lock().expect("gc mutex");
    f(&mut guard)
}

pub(crate) fn create_weak_cell(target: *const u8) -> *mut u8 {
    ensure_thread_registered();
    let needs_gc = gc_needed(Ordering::Relaxed);
    if needs_gc {
        initiate_collection();
    }
    with_gc(|gc| gc.alloc_weak_cell(target))
}

pub(crate) fn stats_snapshot() -> GcStatsSnapshot {
    with_gc(|gc| {
        let mut snapshot = gc.stats.snapshot();
        let (_, free_pages) = gc.free_page_stats();
        snapshot.free_bytes = free_pages.saturating_mul(PAGE_SIZE);
        snapshot.segment_bytes = gc.segments.iter().map(|segment| segment.len).sum();
        snapshot
    })
}

// Simple power-of-two size classes up to a page.
fn build_size_classes() -> Vec<usize> {
    // Power-of-two size classes up to one page.
    let mut classes = Vec::new();
    let mut size = 8usize.max(std::mem::size_of::<usize>());
    while size < PAGE_SIZE {
        classes.push(size);
        size = size.saturating_mul(2);
    }
    classes.push(PAGE_SIZE);
    classes
}

fn size_class_for(size: usize, classes: &[usize]) -> usize {
    // O(1) lookup using bit manipulation.
    // Size classes are powers of two: 8, 16, 32, ... up to PAGE_SIZE.
    const MIN_CLASS: usize = 8;
    const MIN_CLASS_LOG2: u32 = 3; // 2^3 = 8

    if size <= MIN_CLASS {
        return 0;
    }

    // Round up to next power of two and compute log2.
    // For size=9, next_power_of_two=16, trailing_zeros=4, index=4-3=1.
    let rounded = size.next_power_of_two();
    let log2 = rounded.trailing_zeros();
    let index = (log2 - MIN_CLASS_LOG2) as usize;

    // Clamp to valid class range (last class is PAGE_SIZE).
    index.min(classes.len().saturating_sub(1))
}

fn pages_for_size(size: usize) -> usize {
    // Round up to the number of pages required for this allocation.
    let bytes = size.max(1);
    (bytes + PAGE_SIZE - 1) / PAGE_SIZE
}

fn desc_has_pointers(desc: *const GcDesc) -> bool {
    // Null desc means no pointers.
    unsafe { desc.as_ref().map_or(false, |d| d.ptr_count > 0) }
}

// Alignment comes from the type descriptor; default to 1 for unknown types.
fn desc_alignment(desc: *const GcDesc) -> usize {
    // Alignment is clamped to at least 1.
    unsafe { desc.as_ref().map_or(1, |d| d.align.max(1)) }
}

// Lane 0 is scan (has pointers), lane 1 is noscan.
fn span_lane(has_pointers: bool) -> usize {
    // Map the boolean to the lane index used by class_spans.
    if has_pointers { 0 } else { 1 }
}

// Number of u64 words needed to store `count` bits.
fn bitset_len(count: usize) -> usize {
    // 64 bits per word.
    (count + 63) / 64
}

// Read a bit from a u64-backed bitset.
fn bitset_get(bits: &[u64], index: usize) -> bool {
    // Out-of-range reads return false.
    let word = index / 64;
    let bit = index % 64;
    bits.get(word).map_or(false, |v| (v & (1u64 << bit)) != 0)
}

// Set or clear a bit in a u64-backed bitset.
fn bitset_set(bits: &mut [u64], index: usize, value: bool) {
    // Out-of-range writes are ignored.
    let word = index / 64;
    let bit = index % 64;
    if let Some(slot) = bits.get_mut(word) {
        let mask = 1u64 << bit;
        if value {
            *slot |= mask;
        } else {
            *slot &= !mask;
        }
    }
}

fn align_up(n: usize, align: usize) -> usize {
    // Align n upward to the next multiple of align.
    debug_assert!(align.is_power_of_two(), "alignment must be a power of two");
    (n + (align - 1)) & !(align - 1)
}

// Simple policy: grow the next trigger based on current live bytes,
// but never below a minimum threshold.
fn next_gc_threshold(live_bytes: usize) -> usize {
    // Use a simple growth policy to avoid collecting too frequently.
    let doubled = live_bytes.saturating_mul(2);
    if doubled < GC_MIN_TRIGGER {
        GC_MIN_TRIGGER
    } else {
        doubled
    }
}

// Register all arena indices that a segment spans in the arena map.
// A segment may span multiple arenas when it is created for a large allocation.
fn register_segment_arenas(
    arena_map: &mut HashMap<usize, Vec<usize>>,
    segment: &Segment,
    index: usize,
) {
    let base = segment.base();
    if segment.len == 0 {
        return;
    }
    let last_byte = base
        .checked_add(segment.len - 1)
        .expect("segment address range overflow");
    let first_arena = base / SEGMENT_SIZE;
    let last_arena = last_byte / SEGMENT_SIZE;
    for arena in first_arena..=last_arena {
        let candidates = arena_map.entry(arena).or_default();
        if !candidates.contains(&index) {
            candidates.push(index);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        __gc__collect, __gc__grow_buf, __gc__thread_attach, __gc__thread_detach,
        __gc__thread_enter_managed, __rt__gc_enter_blocking, __rt__gc_exit_blocking,
        CURRENT_THREAD_STATE, CleanupRegistration, Gc, GcDesc, GcStats, MAX_GC_PAUSE_SAMPLES,
        PAGE_SIZE, SEGMENT_SIZE, Segment, THREAD_REGISTRY, ensure_thread_registered,
        register_segment_arenas,
    };
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::mpsc;
    use std::time::Duration;

    static POINTER_OFFSETS: [usize; 1] = [0];

    fn bytes_desc(size: usize) -> GcDesc {
        GcDesc {
            size,
            align: 1,
            ptr_offsets: std::ptr::null(),
            ptr_count: 0,
        }
    }

    fn pointer_desc() -> GcDesc {
        GcDesc {
            size: std::mem::size_of::<*mut u8>(),
            align: std::mem::align_of::<*mut u8>(),
            ptr_offsets: POINTER_OFFSETS.as_ptr(),
            ptr_count: POINTER_OFFSETS.len(),
        }
    }

    fn count_finalization(data: usize) {
        let count = unsafe { &*(data as *const AtomicUsize) };
        count.fetch_add(1, Ordering::AcqRel);
    }

    #[test]
    fn segment_lookup_keeps_older_same_arena_candidate() {
        let mut gc = Gc::new();
        let arena_base = 42 * SEGMENT_SIZE;
        gc.segments = vec![
            Segment::test_fake(arena_base + PAGE_SIZE, PAGE_SIZE),
            Segment::test_fake(arena_base + (PAGE_SIZE * 2), PAGE_SIZE),
        ];
        gc.arena_map.clear();
        register_segment_arenas(&mut gc.arena_map, &gc.segments[0], 0);
        register_segment_arenas(&mut gc.arena_map, &gc.segments[1], 1);

        let first_ptr = gc.segments[0].data;
        let second_ptr = gc.segments[1].data;

        assert_eq!(gc.segment_index_for_ptr(first_ptr), Some(0));
        assert_eq!(gc.segment_index_for_ptr(second_ptr), Some(1));
    }

    #[test]
    fn segment_lookup_finds_large_segment_across_all_arenas() {
        let mut gc = Gc::new();
        let base = (77 * SEGMENT_SIZE) + SEGMENT_SIZE - PAGE_SIZE;
        gc.segments = vec![Segment::test_fake(base, SEGMENT_SIZE + PAGE_SIZE)];
        gc.arena_map.clear();
        register_segment_arenas(&mut gc.arena_map, &gc.segments[0], 0);

        let segment = &gc.segments[0];
        let first_ptr = segment.data;
        let last_ptr = segment
            .base()
            .checked_add(segment.len - 1)
            .expect("test segment address range") as *const u8;

        assert_eq!(gc.segment_index_for_ptr(first_ptr), Some(0));
        assert_eq!(gc.segment_index_for_ptr(last_ptr), Some(0));
    }

    #[test]
    fn persistent_roots_use_reference_counts() {
        let mut gc = Gc::new();
        let ptr = 0x1234usize as *const u8;

        gc.add_persistent_root(ptr);
        gc.add_persistent_root(ptr);
        assert_eq!(gc.persistent_roots.get(&ptr), Some(&2));

        gc.remove_persistent_root(ptr);
        assert_eq!(gc.persistent_roots.get(&ptr), Some(&1));

        gc.remove_persistent_root(ptr);
        assert!(!gc.persistent_roots.contains_key(&ptr));
    }

    #[test]
    fn reclaimers_are_deferred_and_returned_once_after_sweep() {
        let mut gc = Gc::new();
        let desc = bytes_desc(8);
        let count = AtomicUsize::new(0);
        let ptr = gc.alloc(8, &desc, false);
        gc.register_reclaimer(
            ptr,
            count_finalization,
            &count as *const AtomicUsize as usize,
        );

        gc.add_root(ptr);
        assert!(gc.collect(&[]).is_empty());

        let work = gc.collect(&[]);
        assert_eq!(work.reclaimers.len(), 1);
        assert!(work.cleanup_handles.is_empty());
        assert_eq!(count.load(Ordering::Acquire), 0);
        for reclaimer in work.reclaimers {
            (reclaimer.callback)(reclaimer.data);
        }
        assert_eq!(count.load(Ordering::Acquire), 1);
        assert!(gc.collect(&[]).is_empty());
    }

    #[test]
    fn gc_pause_samples_are_bounded_and_filter_by_collection() {
        let mut stats = GcStats::default();
        for collection in 1..=MAX_GC_PAUSE_SAMPLES + 1 {
            stats.collections = collection;
            stats.record_pause(Duration::from_nanos(collection as u64));
        }

        let snapshot = stats.snapshot();
        assert_eq!(snapshot.pause_samples.len(), MAX_GC_PAUSE_SAMPLES);
        assert_eq!(snapshot.pause_nanos_since(0).first(), Some(&2));
        assert_eq!(
            snapshot.pause_nanos_since(MAX_GC_PAUSE_SAMPLES),
            vec![(MAX_GC_PAUSE_SAMPLES + 1) as u64]
        );
    }

    #[test]
    fn unregistering_a_reclaimer_prevents_it_from_running() {
        let mut gc = Gc::new();
        let desc = bytes_desc(8);
        let count = AtomicUsize::new(0);
        let ptr = gc.alloc(8, &desc, false);
        gc.register_reclaimer(
            ptr,
            count_finalization,
            &count as *const AtomicUsize as usize,
        );
        gc.unregister_reclaimer(ptr);

        assert!(gc.collect(&[]).is_empty());
        assert_eq!(count.load(Ordering::Acquire), 0);
    }

    #[test]
    fn cleanup_handles_are_returned_once_after_the_owner_dies() {
        let mut gc = Gc::new();
        let desc = bytes_desc(8);
        let owner = gc.alloc(8, &desc, false);
        let frame = gc.alloc(8, &desc, false);
        let handle = 0x1234usize as *mut u8;

        let registration = gc.register_cleanup(owner, frame, handle);
        assert!(matches!(
            registration,
            CleanupRegistration::Registered(token) if token >= 2
        ));

        gc.add_root(owner);
        gc.add_root(frame);
        assert!(gc.collect(&[]).is_empty());

        // The async frame is independently rooted by its handle in production.
        // Once the owner dies, collection only transfers ownership of that handle.
        gc.add_root(frame);
        let work = gc.collect(&[]);
        assert!(work.reclaimers.is_empty());
        assert_eq!(work.cleanup_handles, vec![handle as usize]);

        gc.add_root(frame);
        assert!(gc.collect(&[]).is_empty());
    }

    #[test]
    fn cancelling_a_cleanup_prevents_it_from_being_queued() {
        let mut gc = Gc::new();
        let desc = bytes_desc(8);
        let owner = gc.alloc(8, &desc, false);
        let frame = gc.alloc(8, &desc, false);
        let handle = 0x5678usize as *mut u8;

        let CleanupRegistration::Registered(token) = gc.register_cleanup(owner, frame, handle)
        else {
            panic!("cleanup should register");
        };
        assert_eq!(gc.cancel_cleanup(token), Some(handle as usize));
        assert_eq!(gc.cancel_cleanup(token), None);

        gc.add_root(frame);
        assert!(gc.collect(&[]).is_empty());
    }

    #[test]
    fn cleanup_rejects_a_frame_that_directly_retains_its_owner() {
        let mut gc = Gc::new();
        let owner_desc = bytes_desc(8);
        let frame_desc = pointer_desc();
        let owner = gc.alloc(8, &owner_desc, false);
        let frame = gc.alloc(std::mem::size_of::<*mut u8>(), &frame_desc, false);
        unsafe { frame.cast::<*mut u8>().write(owner) };

        assert!(matches!(
            gc.register_cleanup(owner, frame, 0x9abcusize as *mut u8),
            CleanupRegistration::OwnerRetained
        ));
    }

    #[test]
    fn cleanup_rejects_an_owner_outside_the_managed_heap() {
        let mut gc = Gc::new();
        let desc = bytes_desc(8);
        let frame = gc.alloc(8, &desc, false);

        assert!(matches!(
            gc.register_cleanup(0x1234usize as *const u8, frame, 0x9abcusize as *mut u8),
            CleanupRegistration::NotManaged
        ));
    }

    #[test]
    fn weak_cell_clears_before_its_managed_target_is_swept() {
        let mut gc = Gc::new();
        let desc = bytes_desc(16);
        let owner = gc.alloc(16, &desc, false);
        let target = unsafe { owner.add(4) };
        let cell = gc.alloc_weak_cell(target);

        gc.add_root(owner);
        gc.add_root(cell);
        gc.collect(&[]);
        assert_eq!(crate::weak::load_cell(cell), target);
        assert_eq!(
            gc.weak_cells_by_owner
                .get(&(owner as *const u8))
                .map(Vec::len),
            Some(1)
        );

        gc.add_root(cell);
        gc.collect(&[]);
        assert!(crate::weak::load_cell(cell).is_null());
        assert!(gc.find_object(owner).is_none());
        assert!(gc.find_object(cell).is_some());
        assert!(gc.weak_cells_by_owner.is_empty());
    }

    #[test]
    fn unreachable_weak_cells_are_removed_from_the_side_table() {
        let mut gc = Gc::new();
        let desc = bytes_desc(8);
        let owner = gc.alloc(8, &desc, false);
        let cell = gc.alloc_weak_cell(owner);

        gc.add_root(owner);
        gc.collect(&[]);

        assert!(gc.find_object(owner).is_some());
        assert!(gc.object_base(cell).is_none());
        assert!(gc.weak_cells_by_owner.is_empty());
    }

    #[test]
    fn weak_cells_leave_unmanaged_targets_unchanged() {
        let mut gc = Gc::new();
        let target = 0x1234usize as *const u8;
        let cell = gc.alloc_weak_cell(target);

        assert!(gc.weak_cells_by_owner.is_empty());
        gc.add_root(cell);
        gc.collect(&[]);

        assert_eq!(crate::weak::load_cell(cell), target.cast_mut());
    }

    #[test]
    fn static_roots_keep_global_pointer_alive() {
        let mut gc = Gc::new();
        let leaf_desc = bytes_desc(8);
        let child = gc.alloc(8, &leaf_desc, false);
        let global_slot = child;

        gc.register_static_root(
            (&global_slot as *const *mut u8).cast::<u8>(),
            std::mem::size_of::<*mut u8>(),
        );
        gc.collect(&[]);

        assert!(gc.find_object(child).is_some());
    }

    #[test]
    fn buffer_scan_size_limits_traced_elements() {
        let mut gc = Gc::new();
        let leaf_desc = bytes_desc(8);
        let pointer_desc = pointer_desc();
        let elem_size = std::mem::size_of::<*mut u8>();
        let child = gc.alloc(8, &leaf_desc, false);
        let buffer = gc.alloc_with_scan_size(elem_size * 2, elem_size, &pointer_desc, true);

        unsafe {
            (buffer as *mut *mut u8).write(child);
        }

        gc.add_root(buffer);
        gc.collect(&[]);
        assert!(gc.find_object(child).is_some());

        gc.set_buffer_scan_size(buffer, 0);
        gc.add_root(buffer);
        gc.collect(&[]);
        assert!(gc.find_object(child).is_none());
    }

    #[test]
    fn grow_buf_rejects_invalid_lengths() {
        let desc = bytes_desc(2);

        let past_capacity = __gc__grow_buf(std::ptr::null_mut(), &desc, 2, 1);
        assert!(past_capacity.is_null());

        let overflow = __gc__grow_buf(std::ptr::null_mut(), &desc, usize::MAX, usize::MAX);
        assert!(overflow.is_null());

        // This test enters the runtime directly rather than through a generated
        // Taro entry shim, so it must also close that native thread boundary.
        __gc__thread_detach();
    }

    #[test]
    fn detached_threads_do_not_block_collection() {
        let (tx, rx) = mpsc::channel();
        let handle = std::thread::spawn(move || {
            __gc__thread_attach();
            __gc__thread_detach();
            tx.send(()).unwrap();
            std::thread::sleep(Duration::from_millis(100));
        });

        rx.recv_timeout(Duration::from_secs(1)).unwrap();
        __gc__collect();
        handle.join().unwrap();
        __gc__thread_detach();
    }

    #[test]
    fn ensure_thread_registered_preserves_lazy_registration_and_reattachment() {
        std::thread::spawn(|| {
            ensure_thread_registered();
            let thread_id = std::thread::current().id();
            assert!(CURRENT_THREAD_STATE.with(|slot| {
                slot.borrow()
                    .as_ref()
                    .is_some_and(|current| current.attached && current.state.id == thread_id)
            }));
            assert!(
                THREAD_REGISTRY
                    .lock()
                    .unwrap()
                    .iter()
                    .any(|state| state.id == thread_id)
            );

            __gc__thread_detach();
            assert!(CURRENT_THREAD_STATE.with(|slot| {
                slot.borrow().as_ref().is_some_and(|current| {
                    !current.attached && current.state.at_safepoint.load(Ordering::Acquire)
                })
            }));

            ensure_thread_registered();
            assert!(CURRENT_THREAD_STATE.with(|slot| {
                slot.borrow()
                    .as_ref()
                    .is_some_and(|current| current.attached && current.state.id == thread_id)
            }));
            assert!(
                THREAD_REGISTRY
                    .lock()
                    .unwrap()
                    .iter()
                    .any(|state| state.id == thread_id)
            );
        })
        .join()
        .unwrap();
    }

    #[test]
    fn managed_entry_registers_and_resumes_the_current_thread() {
        std::thread::spawn(|| {
            __gc__thread_attach();
            assert!(CURRENT_THREAD_STATE.with(|slot| {
                slot.borrow().as_ref().is_some_and(|current| {
                    current.attached && current.state.at_safepoint.load(Ordering::Acquire)
                })
            }));
            __gc__thread_enter_managed();
            assert!(CURRENT_THREAD_STATE.with(|slot| {
                slot.borrow().as_ref().is_some_and(|current| {
                    current.attached && !current.state.at_safepoint.load(Ordering::Acquire)
                })
            }));
            __gc__thread_detach();
        })
        .join()
        .unwrap();
    }

    #[test]
    fn blocking_threads_keep_roots_visible_without_delaying_collection() {
        let (ready_tx, ready_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let handle = std::thread::spawn(move || {
            __gc__thread_attach();
            __rt__gc_exit_blocking();
            __rt__gc_enter_blocking();
            ready_tx.send(()).unwrap();
            release_rx.recv().unwrap();
            __gc__thread_detach();
        });

        ready_rx.recv_timeout(Duration::from_secs(1)).unwrap();
        __gc__collect();
        release_tx.send(()).unwrap();
        handle.join().unwrap();
        __gc__thread_detach();
    }
}
