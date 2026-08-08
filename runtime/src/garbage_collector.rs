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
//!    - Typed static/global roots (gc_register_static).
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
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU8, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::time::{Duration, Instant};

use crate::gc_layout::{GcLayoutNode, TraceMode, trace_layout};
use memmap2::MmapMut;

// === Public GC surface ===

/// Describes a GC-managed type.
///
/// - size: size in bytes for a single element of this type.
/// - align: ABI alignment for a single element of this type.
/// - nodes: indexed, tag-aware pointer-layout graph.
/// - node_count: number of nodes in the graph; zero means noscan.
///
/// For arrays/slices, the allocator provides the element desc and total size.
/// The GC will repeat the pointer offsets across the payload when needed.
#[repr(C)]
#[derive(Debug)]
pub struct GcDesc {
    pub size: usize,
    pub align: usize,
    pub nodes: *const GcLayoutNode,
    pub node_count: usize,
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

#[derive(Clone, Copy)]
struct StaticRoot {
    start: *const u8,
    desc: *const GcDesc,
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
    /// Number of spans currently checked out to this mutator. A collector may
    /// begin heap root traversal only after parked threads publish zero here.
    owned_spans: AtomicUsize,
}
unsafe impl Send for ThreadState {}
unsafe impl Sync for ThreadState {}

static THREAD_REGISTRY: Mutex<Vec<Arc<ThreadState>>> = Mutex::new(Vec::new());
static THREAD_REGISTRY_EPOCH: AtomicUsize = AtomicUsize::new(0);
static THREAD_ATTACHING: AtomicUsize = AtomicUsize::new(0);
const GC_REQUESTED_FLAG: u8 = 1 << 0;
const GC_NEEDED_FLAG: u8 = 1 << 1;
const ALLOCATION_DEBT_QUANTUM: usize = 64 * 1024;
const MUTATOR_CACHE_SIZE_CLASSES: usize = 11;
const MUTATOR_CACHE_SLOTS: usize = MUTATOR_CACHE_SIZE_CLASSES * 2;

static PACING_HEAP_BYTES: AtomicUsize = AtomicUsize::new(0);
static PACING_HEAP_GOAL: AtomicUsize = AtomicUsize::new(GC_MIN_TRIGGER);
static PACING_ENABLED: AtomicBool = AtomicBool::new(true);

/// Compiler-polled process state. A zero byte is the complete mutator fast path.
///
/// Collection requests and threshold notifications share one byte so generated
/// code needs one atomic load and one unlikely branch. Runtime slow paths use
/// read-modify-write operations to change their own bit without losing a
/// concurrent update to the other bit.
#[unsafe(export_name = "__gc__poll_flags")]
pub static GC_POLL_FLAGS: AtomicU8 = AtomicU8::new(0);

#[derive(Clone, Copy)]
struct CachedSpan {
    span_id: usize,
    span: *const Span,
}

#[derive(Default)]
struct MutatorCache {
    spans: Vec<Option<CachedSpan>>,
    unpublished_debt: usize,
    pending_allocations: usize,
    pending_bytes: usize,
}

impl MutatorCache {
    fn new() -> Self {
        Self {
            spans: vec![None; MUTATOR_CACHE_SLOTS],
            ..Self::default()
        }
    }

    fn record_allocation(&mut self, bytes: usize) {
        self.pending_allocations = self.pending_allocations.saturating_add(1);
        self.pending_bytes = self.pending_bytes.saturating_add(bytes);
        self.unpublished_debt = self.unpublished_debt.saturating_add(bytes);
        if self.unpublished_debt >= ALLOCATION_DEBT_QUANTUM {
            let quanta = self.unpublished_debt / ALLOCATION_DEBT_QUANTUM;
            let published = quanta.saturating_mul(ALLOCATION_DEBT_QUANTUM);
            self.unpublished_debt -= published;
            publish_allocation_debt(published);
        }
    }

    fn take_accounting(&mut self) -> MutatorAccounting {
        publish_allocation_debt(std::mem::take(&mut self.unpublished_debt));
        MutatorAccounting {
            allocations: std::mem::take(&mut self.pending_allocations),
            bytes: std::mem::take(&mut self.pending_bytes),
        }
    }

    fn take_all(&mut self) -> MutatorCacheFlush {
        let spans = self.spans.iter_mut().filter_map(Option::take).collect();
        MutatorCacheFlush {
            spans,
            accounting: self.take_accounting(),
        }
    }
}

#[derive(Clone, Copy, Default)]
struct MutatorAccounting {
    allocations: usize,
    bytes: usize,
}

struct MutatorCacheFlush {
    spans: Vec<CachedSpan>,
    accounting: MutatorAccounting,
}

fn publish_allocation_debt(bytes: usize) {
    if bytes == 0 {
        return;
    }
    let previous = PACING_HEAP_BYTES
        .try_update(Ordering::AcqRel, Ordering::Acquire, |current| {
            Some(current.saturating_add(bytes))
        })
        .unwrap_or_else(|current| current);
    let current = previous.saturating_add(bytes);
    if PACING_ENABLED.load(Ordering::Relaxed) && current >= PACING_HEAP_GOAL.load(Ordering::Relaxed)
    {
        set_gc_needed(true);
    }
}

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct GcConfig {
    /// `None` is `TARO_GC_PERCENT=off`.
    percent: Option<u32>,
    /// `None` is an unlimited soft memory limit.
    memory_limit: Option<usize>,
}

impl Default for GcConfig {
    fn default() -> Self {
        Self {
            percent: Some(100),
            memory_limit: None,
        }
    }
}

impl GcConfig {
    fn from_env() -> Result<Self, String> {
        let percent = match std::env::var_os("TARO_GC_PERCENT") {
            None => Some(100),
            Some(raw) => {
                let raw = raw
                    .into_string()
                    .map_err(|_| "TARO_GC_PERCENT must contain valid Unicode".to_string())?;
                parse_gc_percent(&raw)?
            }
        };
        let memory_limit = match std::env::var_os("TARO_GC_MEMORY_LIMIT") {
            None => None,
            Some(raw) => {
                let raw = raw
                    .into_string()
                    .map_err(|_| "TARO_GC_MEMORY_LIMIT must contain valid Unicode".to_string())?;
                parse_gc_memory_limit(&raw)?
            }
        };
        Ok(Self {
            percent,
            memory_limit,
        })
    }
}

fn parse_gc_percent(raw: &str) -> Result<Option<u32>, String> {
    let value = raw.trim();
    if value.eq_ignore_ascii_case("off") {
        return Ok(None);
    }
    value
        .parse::<u32>()
        .ok()
        .filter(|percent| *percent <= 10_000)
        .map(Some)
        .ok_or_else(|| {
            format!("TARO_GC_PERCENT must be `off` or an integer from 0 to 10000; got `{raw}`")
        })
}

fn parse_gc_memory_limit(raw: &str) -> Result<Option<usize>, String> {
    let value = raw.trim();
    if value.eq_ignore_ascii_case("off") {
        return Ok(None);
    }
    let (digits, multiplier) = [
        ("KiB", 1_u128 << 10),
        ("MiB", 1_u128 << 20),
        ("GiB", 1_u128 << 30),
        ("TiB", 1_u128 << 40),
        ("B", 1_u128),
    ]
    .into_iter()
    .find_map(|(suffix, multiplier)| {
        value
            .strip_suffix(suffix)
            .map(|digits| (digits, multiplier))
    })
    .ok_or_else(|| {
        format!(
            "TARO_GC_MEMORY_LIMIT must be `off` or decimal bytes with B, KiB, MiB, GiB, or TiB; got `{raw}`"
        )
    })?;
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!(
            "TARO_GC_MEMORY_LIMIT has an invalid decimal value; got `{raw}`"
        ));
    }
    let bytes = digits
        .parse::<u128>()
        .ok()
        .and_then(|count| count.checked_mul(multiplier))
        .and_then(|bytes| usize::try_from(bytes).ok())
        .ok_or_else(|| format!("TARO_GC_MEMORY_LIMIT exceeds the platform limit; got `{raw}`"))?;
    Ok(Some(bytes))
}

fn gc_config() -> &'static GcConfig {
    static CONFIG: OnceLock<Result<GcConfig, String>> = OnceLock::new();
    match CONFIG.get_or_init(GcConfig::from_env) {
        Ok(config) => config,
        Err(error) => {
            eprintln!("runtime configuration error: {error}");
            std::process::exit(2);
        }
    }
}

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

#[inline]
fn allocation_requires_slow_path(flags: u8, stress: bool) -> bool {
    flags & GC_REQUESTED_FLAG != 0 || (flags & GC_NEEDED_FLAG != 0 && !stress)
}

struct CurrentThreadState {
    state: Arc<ThreadState>,
    attached: bool,
    cache: MutatorCache,
}

impl Drop for CurrentThreadState {
    fn drop(&mut self) {
        flush_mutator_cache_data(&self.state, self.cache.take_all());
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
        owned_spans: AtomicUsize::new(0),
    }))
}

fn unregister_thread(state: &ThreadState) {
    // Serialize the request check with registry snapshots. If no collection is
    // pending, removal itself guarantees that a later snapshot cannot include
    // this thread, so there is no stack to publish. If a collector already
    // requested the world, publish before removal so an existing snapshot can
    // finish its wait, observe the epoch change, and retry.
    let mut reg = THREAD_REGISTRY.lock().unwrap();
    if !state.at_safepoint.load(Ordering::Relaxed) {
        if gc_requested(Ordering::Acquire) {
            let roots = crate::stack_walk::capture_current_roots();
            unsafe { *state.published_roots.get() = roots };
        }
        state.at_safepoint.store(true, Ordering::Release);
    }

    let len_before = reg.len();
    reg.retain(|registered| registered.id != state.id);
    if reg.len() != len_before {
        THREAD_REGISTRY_EPOCH.fetch_add(1, Ordering::Release);
    }
}

std::thread_local! {
    static CURRENT_THREAD_STATE: RefCell<Option<CurrentThreadState>> = const { RefCell::new(None) };
    #[cfg(test)]
    static GC_MUTEX_ACQUISITIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn current_thread_gc_mutex_acquisitions() -> usize {
    GC_MUTEX_ACQUISITIONS.with(std::cell::Cell::get)
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
                    cache: MutatorCache::new(),
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

fn flush_mutator_cache_data(state: &ThreadState, flush: MutatorCacheFlush) {
    if flush.spans.is_empty() && flush.accounting.allocations == 0 && flush.accounting.bytes == 0 {
        return;
    }
    let returned = flush.spans.len();
    with_gc(|gc| {
        for cached in flush.spans {
            gc.return_checked_out_span(cached.span_id);
        }
        gc.record_cached_allocations(flush.accounting);
    });
    if returned != 0 {
        let previous = state.owned_spans.fetch_sub(returned, Ordering::Release);
        assert!(previous >= returned, "mutator span ownership underflow");
    }
}

fn flush_current_mutator_cache() {
    let flush = CURRENT_THREAD_STATE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let current = slot.as_mut()?;
        Some((current.state.clone(), current.cache.take_all()))
    });
    if let Some((state, flush)) = flush {
        flush_mutator_cache_data(&state, flush);
    }
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
    flush_current_mutator_cache();
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
    flush_current_mutator_cache();
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
        assert_eq!(
            thread.owned_spans.load(Ordering::Acquire),
            0,
            "parked mutator still owns allocation spans"
        );
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
    flush_current_mutator_cache();
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

/// Cooperate with an active collection and honor percentage pacing before an
/// allocation. Soft-limit checks live in the locked refill/growth operations
/// below so their capacity observation cannot race the actual heap mutation.
fn prepare_for_allocation() -> bool {
    let mut collected = false;
    if gc_requested(Ordering::Acquire) {
        park_at_safepoint();
        collected = true;
    }
    // Stress mode deliberately leaves GC_NEEDED set so every *generated poll*
    // collects. Runtime allocation must still make progress between polls;
    // otherwise a cache refill retries forever without allocating a slot.
    if gc_needed(Ordering::Relaxed) && !gc_stress_enabled() {
        initiate_collection();
        collected = true;
    }
    collected
}

fn small_class(alloc_size: usize) -> (usize, usize) {
    let class_size = alloc_size
        .max(std::mem::size_of::<usize>())
        .next_power_of_two()
        .min(PAGE_SIZE);
    let class_index = class_size.trailing_zeros() as usize - 3;
    debug_assert!(class_index < MUTATOR_CACHE_SIZE_CLASSES);
    (class_index, class_size)
}

fn try_cached_small_allocation(
    cache_slot: usize,
    class_size: usize,
    payload_size: usize,
    scan_size: usize,
    desc: *const GcDesc,
    is_array: bool,
) -> Option<*mut u8> {
    if allocation_requires_slow_path(GC_POLL_FLAGS.load(Ordering::Relaxed), gc_stress_enabled()) {
        return None;
    }
    CURRENT_THREAD_STATE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let current = slot.as_mut()?;
        if !current.attached {
            return None;
        }
        let cached = current.cache.spans.get(cache_slot)?.as_ref()?;
        // SAFETY: boxed span records are stable, `cached` proves this mutator
        // exclusively owns the span, and collection cannot start until this
        // thread flushes the cache and publishes its safepoint state.
        let span = unsafe { &*cached.span };
        let ptr = span.alloc_small(payload_size, scan_size, desc, is_array)?;
        current.cache.record_allocation(class_size);
        Some(ptr)
    })
}

fn refill_cached_span(
    cache_slot: usize,
    class_index: usize,
    lane: usize,
    mut attempted_soft_limit_collection: bool,
) {
    let (state, previous, accounting) = CURRENT_THREAD_STATE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let current = slot
            .as_mut()
            .expect("registered mutator has thread-local state");
        let previous = current.cache.spans[cache_slot].take();
        let accounting = current.cache.take_accounting();
        (current.state.clone(), previous, accounting)
    });

    with_gc(|gc| {
        if let Some(previous) = previous {
            gc.return_checked_out_span(previous.span_id);
        }
        gc.record_cached_allocations(accounting);
    });
    if previous.is_some() {
        let owned = state.owned_spans.fetch_sub(1, Ordering::Release);
        assert!(owned >= 1, "mutator span ownership underflow on refill");
    }

    let cached = loop {
        let result = with_gc(|gc| {
            if !attempted_soft_limit_collection
                && gc.checkout_would_cross_soft_limit(class_index, lane)
            {
                None
            } else {
                Some(gc.checkout_span_for_class(class_index, lane))
            }
        });
        if let Some(cached) = result {
            break cached;
        }
        // One collection includes sweep and scavenging. If live data still
        // forces growth, the next locked attempt is allowed to exceed the soft
        // limit and `alloc_pages` records that event instead of looping.
        initiate_collection();
        attempted_soft_limit_collection = true;
    };

    state.owned_spans.fetch_add(1, Ordering::Release);
    CURRENT_THREAD_STATE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let current = slot
            .as_mut()
            .expect("registered mutator disappeared during refill");
        assert!(current.cache.spans[cache_slot].is_none());
        current.cache.spans[cache_slot] = Some(cached);
    });
}

fn runtime_alloc_with_scan_size(
    size: usize,
    scan_size: usize,
    desc: *const GcDesc,
    is_array: bool,
) -> *mut u8 {
    let align = desc_alignment(desc).max(std::mem::size_of::<usize>());
    let alloc_size = align_up(size, align);
    if alloc_size > PAGE_SIZE {
        let mut attempted_soft_limit_collection = prepare_for_allocation();
        let pages = pages_for_size(alloc_size);
        loop {
            let allocation = with_gc(|gc| {
                if !attempted_soft_limit_collection
                    && gc.segment_growth_would_cross_soft_limit(pages)
                {
                    None
                } else {
                    Some(gc.alloc_with_scan_size(size, scan_size, desc, is_array))
                }
            });
            if let Some(allocation) = allocation {
                return allocation;
            }
            initiate_collection();
            attempted_soft_limit_collection = true;
        }
    }

    let (class_index, class_size) = small_class(alloc_size);
    let lane = span_lane(desc_has_pointers(desc));
    let cache_slot = class_index * 2 + lane;
    loop {
        if let Some(ptr) =
            try_cached_small_allocation(cache_slot, class_size, size, scan_size, desc, is_array)
        {
            return ptr;
        }
        let attempted_soft_limit_collection = prepare_for_allocation();
        refill_cached_span(
            cache_slot,
            class_index,
            lane,
            attempted_soft_limit_collection,
        );
    }
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
    runtime_alloc_with_scan_size(size, size, desc, false)
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
    // Scan the whole buffer rather than the initialised prefix. The prefix
    // would otherwise have to be republished on every push and pop, and doing
    // that means resolving the pointer to a span under the global GC lock —
    // a lock round-trip on the hottest operation a collection type has.
    // Unwritten slots are zero and vacated ones are cleared by the owner, so
    // scanning the whole allocation finds exactly the same pointers.
    let _ = scan_size;
    runtime_alloc_with_scan_size(total, total, desc, true)
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

/// Register an exact typed global/static root.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__register_static(start: *const u8, desc: *const GcDesc) {
    if start.is_null() || desc.is_null() {
        return;
    }
    with_gc(|gc| gc.register_static_root(start, desc));
}

/// Update the initialized length of a GC-managed pointer-bearing buffer.
#[unsafe(no_mangle)]
/// Publish how much of a managed buffer holds live elements.
///
/// Retained for the runtime ABI, but now a no-op: buffers are scanned to their
/// full capacity, so the collector never needs the live length. It used to take
/// the global GC lock to resolve `ptr` to a span, which put a lock round-trip on
/// every push and pop of any collection whose elements contain pointers.
///
/// The owner is responsible for clearing a slot it vacates, which is what keeps
/// scanning the whole allocation from retaining values that have been removed.
pub extern "C" fn __gc__set_buf_len(_ptr: *mut u8, _desc: *const GcDesc, _len: usize) {}

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

    // Allocate new buffer
    // As in `__gc__makebuf`: the whole allocation is scanned, so the live
    // length never has to be published back to the collector.
    let _ = scan_size;
    let new_ptr = runtime_alloc_with_scan_size(new_total, new_total, desc, true);
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

#[cfg(unix)]
fn os_page_size() -> usize {
    static OS_PAGE_SIZE: OnceLock<usize> = OnceLock::new();
    *OS_PAGE_SIZE.get_or_init(|| {
        let size = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        let size = usize::try_from(size)
            .ok()
            .filter(|size| size.is_power_of_two())
            .unwrap_or_else(|| panic!("failed to query a power-of-two OS page size"));
        assert!(size != 0, "OS page size must be non-zero");
        size
    })
}

#[cfg(not(unix))]
const fn os_page_size() -> usize {
    PAGE_SIZE
}

fn fully_free_os_page_range(
    data_base: usize,
    logical_start: usize,
    logical_pages: usize,
    native_page_size: usize,
) -> Option<std::ops::Range<usize>> {
    debug_assert!(native_page_size.is_power_of_two());
    let free_start = data_base.checked_add(logical_start.checked_mul(PAGE_SIZE)?)?;
    let free_end = free_start.checked_add(logical_pages.checked_mul(PAGE_SIZE)?)?;
    let start = align_up(free_start, native_page_size);
    let end = free_end & !(native_page_size - 1);
    (start < end).then_some(start..end)
}

// Contiguous run of free pages inside a segment.
struct PageRun {
    start: usize,
    len: usize,
}

// A segment is a large, page-aligned arena that owns the memory and page map.
// Spans are carved out of segments; the page_map lets us find the owning span
// for any interior pointer during marking.
struct Segment {
    // Anonymous mapping that owns the segment bytes. Test-only synthetic
    // segments have no mapping and are never dereferenced.
    mapping: Option<MmapMut>,
    // PAGE_SIZE-aligned usable start inside `mapping`.
    data: *mut u8,
    len: usize,
    // Page index -> span id for that page; SPAN_NONE means free/unassigned.
    page_map: Vec<usize>,
    // Bump pointer in pages for fresh allocation.
    next_page: usize,
    // Free page runs (when spans are returned).
    free_runs: Vec<PageRun>,
    // Native VM pages successfully advised with MADV_DONTNEED. One VM page may
    // cover several allocator pages (notably 16 KiB Darwin over 8 KiB spans),
    // so accounting and reuse invalidation must use this granularity.
    scavenged_os_pages: Vec<bool>,
    os_page_size: usize,
}

impl Segment {
    fn new(pages: usize) -> Self {
        // Over-map by one logical page so the usable subrange can retain the
        // allocator's stronger PAGE_SIZE alignment on platforms whose native
        // mapping alignment is smaller.
        let bytes = pages.saturating_mul(PAGE_SIZE);
        let mapping_len = bytes
            .checked_add(PAGE_SIZE)
            .expect("segment mapping size overflow");
        let mut mapping = MmapMut::map_anon(mapping_len)
            .unwrap_or_else(|error| panic!("failed to map GC segment: {error}"));
        let raw = mapping.as_mut_ptr() as usize;
        let data = align_up(raw, PAGE_SIZE) as *mut u8;
        let os_page_size = os_page_size();
        Self {
            mapping: Some(mapping),
            data,
            len: bytes,
            page_map: vec![SPAN_NONE; pages],
            next_page: 0,
            free_runs: Vec::new(),
            scavenged_os_pages: vec![false; mapping_len.div_ceil(os_page_size)],
            os_page_size,
        }
    }

    #[cfg(test)]
    fn test_fake(base: usize, len: usize) -> Self {
        Self {
            mapping: None,
            data: base as *mut u8,
            len,
            page_map: vec![SPAN_NONE; pages_for_size(len).max(1)],
            next_page: 0,
            free_runs: Vec::new(),
            scavenged_os_pages: Vec::new(),
            os_page_size: os_page_size(),
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
                self.clear_scavenged(start, pages);
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

    fn can_alloc_pages(&self, pages: usize) -> bool {
        pages != 0
            && (self.free_runs.iter().any(|run| run.len >= pages)
                || self.next_page.saturating_add(pages) <= self.page_count())
    }

    fn clear_scavenged(&mut self, start: usize, pages: usize) {
        let Some(mapping) = self.mapping.as_ref() else {
            return;
        };
        if pages == 0 {
            return;
        }
        let mapping_base = mapping.as_ptr() as usize;
        let allocation_start = self.base().saturating_add(start.saturating_mul(PAGE_SIZE));
        let allocation_end = allocation_start.saturating_add(pages.saturating_mul(PAGE_SIZE));
        let first = allocation_start.saturating_sub(mapping_base) / self.os_page_size;
        let end = allocation_end
            .saturating_sub(mapping_base)
            .div_ceil(self.os_page_size)
            .min(self.scavenged_os_pages.len());
        for scavenged in &mut self.scavenged_os_pages[first.min(end)..end] {
            *scavenged = false;
        }
    }

    #[cfg(unix)]
    fn scavenge_free_runs(&mut self) -> usize {
        use memmap2::UncheckedAdvice;

        let Some(mapping) = self.mapping.as_ref() else {
            return 0;
        };
        let mapping_base = mapping.as_ptr() as usize;
        let mut released = 0usize;
        for run in &self.free_runs {
            let Some(range) =
                fully_free_os_page_range(self.base(), run.start, run.len, self.os_page_size)
            else {
                continue;
            };
            let first = range.start.saturating_sub(mapping_base) / self.os_page_size;
            let end = range.end.saturating_sub(mapping_base) / self.os_page_size;
            let mut page = first;
            while page < end {
                while page < end && self.scavenged_os_pages[page] {
                    page += 1;
                }
                let start = page;
                while page < end && !self.scavenged_os_pages[page] {
                    page += 1;
                }
                if start == page {
                    continue;
                }
                let offset = start.saturating_mul(self.os_page_size);
                let len = (page - start).saturating_mul(self.os_page_size);
                // SAFETY: collection is stop-the-world, this run has no span
                // owner in the page map, and no allocation can hold a Rust
                // borrow into these free pages. DontNeed may replace their
                // contents with zero-fill pages, which is why memmap2 models
                // the operation as a conceptual write.
                if unsafe { mapping.unchecked_advise_range(UncheckedAdvice::DontNeed, offset, len) }
                    .is_ok()
                {
                    for scavenged in &mut self.scavenged_os_pages[start..page] {
                        *scavenged = true;
                    }
                    released = released.saturating_add(len);
                }
            }
        }
        released
    }

    #[cfg(not(unix))]
    fn scavenge_free_runs(&mut self) -> usize {
        0
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

    // Slot allocation and marking state. Allocation bits are release-published
    // and acquire-read; mark bits are collector-only during stop-the-world.
    alloc_map: Vec<AtomicU64>,
    mark_map: Vec<u64>,
    // Bitset recording whether each slot should be treated as an array.
    array_map: Vec<AtomicU64>,

    // Per-slot metadata (only populated for scan spans).
    descs: Vec<AtomicPtr<GcDesc>>,
    // Requested payload bytes for each slot.
    sizes: Vec<AtomicUsize>,
    // Bytes the marker should trace. Array buffers may allocate more capacity
    // than their initialized length.
    scan_sizes: Vec<AtomicUsize>,

    // A checked-out mutator exclusively owns this free list. The collector may
    // access it only after every cache is flushed by the safepoint handshake.
    free_list: UnsafeCell<Vec<usize>>,
    allocated: AtomicUsize,

    // Indicates whether the span is currently in a class free-list.
    in_class_list: bool,
    // Protected by the global GC mutex. A checked-out span is absent from its
    // class list and has exactly one mutator owner.
    checked_out: bool,
}

unsafe impl Send for Span {}
unsafe impl Sync for Span {}

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
            alloc_map: atomic_bitset(bit_len),
            mark_map: vec![0; bit_len],
            array_map: if has_pointers {
                atomic_bitset(bit_len)
            } else {
                Vec::new()
            },
            descs: if has_pointers {
                (0..object_count)
                    .map(|_| AtomicPtr::new(std::ptr::null_mut()))
                    .collect()
            } else {
                Vec::new()
            },
            sizes: if has_pointers {
                (0..object_count).map(|_| AtomicUsize::new(0)).collect()
            } else {
                Vec::new()
            },
            scan_sizes: if has_pointers {
                (0..object_count).map(|_| AtomicUsize::new(0)).collect()
            } else {
                Vec::new()
            },
            free_list: UnsafeCell::new(free_list),
            allocated: AtomicUsize::new(0),
            in_class_list: false,
            checked_out: false,
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
        let alloc_map = atomic_bitset(bit_len);
        let mark_map = vec![0; bit_len];
        let array_map = if has_pointers {
            atomic_bitset(bit_len)
        } else {
            Vec::new()
        };
        if has_pointers && is_array {
            atomic_bitset_set(&array_map, 0, true, Ordering::Relaxed);
        }
        let descs = if has_pointers {
            vec![AtomicPtr::new(desc.cast_mut())]
        } else {
            Vec::new()
        };
        let sizes = if has_pointers {
            vec![AtomicUsize::new(payload_size)]
        } else {
            Vec::new()
        };
        let scan_sizes = if has_pointers {
            vec![AtomicUsize::new(scan_size.min(payload_size))]
        } else {
            Vec::new()
        };
        atomic_bitset_set(&alloc_map, 0, true, Ordering::Release);
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
            descs,
            sizes,
            scan_sizes,
            free_list: UnsafeCell::new(Vec::new()),
            allocated: AtomicUsize::new(1),
            in_class_list: false,
            checked_out: false,
        }
    }

    fn has_free(&self) -> bool {
        // Indicates whether there is at least one free slot.
        self.allocated.load(Ordering::Relaxed) < self.object_count
    }

    // Allocate one slot in a small-object span.
    fn alloc_small(
        &self,
        payload_size: usize,
        scan_size: usize,
        desc: *const GcDesc,
        is_array: bool,
    ) -> Option<*mut u8> {
        // Zero the entire reusable slot before publishing its allocation bit
        // so a scanner can never observe stale pointer-shaped bytes.
        debug_assert!(
            payload_size <= self.object_size,
            "payload {} exceeds span object size {}",
            payload_size,
            self.object_size
        );
        // SAFETY: either the global allocator or the sole checked-out mutator
        // owns the span when this method is called.
        let index = unsafe { &mut *self.free_list.get() }.pop()?;
        let ptr = unsafe { self.base.add(index * self.object_size) };
        unsafe { std::ptr::write_bytes(ptr, 0, self.object_size) };
        if self.has_pointers {
            self.descs[index].store(desc.cast_mut(), Ordering::Relaxed);
            self.sizes[index].store(payload_size, Ordering::Relaxed);
            self.scan_sizes[index].store(scan_size.min(payload_size), Ordering::Relaxed);
            atomic_bitset_set(&self.array_map, index, is_array, Ordering::Relaxed);
        }
        atomic_bitset_set(&self.alloc_map, index, true, Ordering::Release);
        self.allocated.fetch_add(1, Ordering::Relaxed);
        Some(ptr)
    }

    fn free_small(&mut self, index: usize) {
        // Clear metadata for the slot and push it back to the free list.
        atomic_bitset_set(&self.alloc_map, index, false, Ordering::Release);
        if self.has_pointers {
            self.descs[index].store(std::ptr::null_mut(), Ordering::Relaxed);
            self.sizes[index].store(0, Ordering::Relaxed);
            self.scan_sizes[index].store(0, Ordering::Relaxed);
            atomic_bitset_set(&self.array_map, index, false, Ordering::Relaxed);
        }
        // SAFETY: sweep runs stop-the-world after checked-out spans return.
        unsafe { &mut *self.free_list.get() }.push(index);
        let allocated = self.allocated.load(Ordering::Relaxed);
        self.allocated
            .store(allocated.saturating_sub(1), Ordering::Relaxed);
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
    pub heap_goal: usize,
    pub configured_memory_limit: Option<usize>,
    pub cached_span_refills: usize,
    pub released_bytes: usize,
    pub scavenged_bytes: usize,
    pub soft_limit_exceedances: usize,
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
    heap_goal: usize,
    configured_memory_limit: Option<usize>,
    cached_span_refills: usize,
    released_bytes: usize,
    scavenged_bytes: usize,
    soft_limit_exceedances: usize,
    pause_samples: VecDeque<(usize, u64)>,
}

impl GcStats {
    fn record_alloc(&mut self, size: usize) {
        self.record_allocations(1, size);
    }

    fn record_allocations(&mut self, count: usize, bytes: usize) {
        self.total_allocations = self.total_allocations.saturating_add(count);
        self.total_allocated_bytes = self.total_allocated_bytes.saturating_add(bytes);
        self.live_objects = self.live_objects.saturating_add(count);
        self.live_bytes = self.live_bytes.saturating_add(bytes);
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
            heap_goal: self.heap_goal,
            configured_memory_limit: self.configured_memory_limit,
            cached_span_refills: self.cached_span_refills,
            released_bytes: self.released_bytes,
            scavenged_bytes: self.scavenged_bytes,
            soft_limit_exceedances: self.soft_limit_exceedances,
            pause_samples: self.pause_samples.iter().copied().collect(),
        }
    }

    fn log(&self) {
        if std::env::var("TARO_GC_STATS").map_or(false, |val| val == "1") {
            eprintln!(
                "gc: collections={} live_objects={} live_bytes={} heap_goal={} memory_limit={} last_freed_objects={} last_freed_bytes={} free_runs={} free_bytes={} segments={} segment_bytes={} cached_span_refills={} released_bytes={} scavenged_bytes={} soft_limit_exceedances={} total_allocs={} total_frees={} total_alloc_bytes={} total_freed_bytes={}",
                self.collections,
                self.live_objects,
                self.live_bytes,
                self.heap_goal,
                self.configured_memory_limit
                    .map_or_else(|| "off".to_string(), |value| value.to_string()),
                self.last_freed_objects,
                self.last_freed_bytes,
                self.free_runs,
                self.free_bytes,
                self.last_segment_count,
                self.last_segment_bytes,
                self.cached_span_refills,
                self.released_bytes,
                self.scavenged_bytes,
                self.soft_limit_exceedances,
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
    // Boxed records keep checked-out span addresses stable across vector
    // growth while the heap mutex is not held.
    spans: Vec<Option<Box<Span>>>,
    // Free list of span IDs for reuse (prevents unbounded growth of spans vec).
    free_span_ids: Vec<usize>,
    size_classes: Vec<usize>,
    // Per size class: [scan spans, noscan spans].
    class_spans: Vec<[Vec<usize>; 2]>,
    static_roots: Vec<StaticRoot>,
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
    config: GcConfig,
    // Absolute live-heap goal at which percentage pacing requests collection.
    heap_goal: usize,
    publishes_global_pacing: bool,
}

// GC is only accessed under a Mutex; raw pointers are fine.
unsafe impl Send for Gc {}
unsafe impl Sync for Gc {}

impl Gc {
    fn new() -> Self {
        Self::new_with_config(*gc_config())
    }

    fn new_runtime() -> Self {
        let mut gc = Self::new();
        gc.publishes_global_pacing = true;
        gc.publish_global_pacing_state();
        gc
    }

    fn new_with_config(config: GcConfig) -> Self {
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

        let heap_goal = next_heap_goal(0, config);
        let mut stats = GcStats {
            heap_goal,
            configured_memory_limit: config.memory_limit,
            ..GcStats::default()
        };
        stats.last_segment_count = segments.len();
        stats.last_segment_bytes = segments.iter().map(|segment| segment.len).sum();

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
            stats,
            config,
            heap_goal,
            publishes_global_pacing: false,
        }
    }

    fn add_root(&mut self, ptr: *const u8) {
        // Manual roots are consumed on the next collection.
        self.manual_roots.push(ptr);
    }

    fn register_static_root(&mut self, start: *const u8, desc: *const GcDesc) {
        if !self
            .static_roots
            .iter()
            .any(|existing| existing.start == start && existing.desc == desc)
        {
            self.static_roots.push(StaticRoot { start, desc });
        }
    }

    // Route small allocations to size-class spans; large allocations get a span.
    // payload_size is the requested size, alloc_size is rounded up for alignment.
    #[cfg_attr(not(test), allow(dead_code))]
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
        let total_bytes = pages.saturating_mul(PAGE_SIZE);
        // Swept and scavenged pages may both be reused. Explicit zeroing is
        // the correctness guarantee rather than an assumption about mapping
        // or kernel state.
        unsafe { std::ptr::write_bytes(base, 0, total_bytes) };
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
        self.spans[span_id] = Some(Box::new(span));
        (base, total_bytes)
    }

    // Update stats after allocation.
    fn after_alloc(&mut self, alloc_bytes: usize) {
        // Update stats and allow safepoints to decide when to collect.
        self.stats.record_alloc(alloc_bytes);
        if self.publishes_global_pacing {
            publish_allocation_debt(alloc_bytes);
        }
        self.refresh_gc_needed();
    }

    fn record_cached_allocations(&mut self, accounting: MutatorAccounting) {
        self.stats
            .record_allocations(accounting.allocations, accounting.bytes);
        self.refresh_gc_needed();
    }

    /// Republishes whether a collection is due, for safepoints to read without
    /// taking the mutex this runs under.
    fn refresh_gc_needed(&self) {
        if self.publishes_global_pacing {
            let percentage_due = self.config.percent.is_some()
                && PACING_HEAP_BYTES.load(Ordering::Acquire) >= self.heap_goal;
            set_gc_needed(percentage_due);
        }
    }

    fn publish_global_pacing_state(&self) {
        PACING_HEAP_BYTES.store(self.stats.live_bytes, Ordering::Release);
        PACING_HEAP_GOAL.store(self.heap_goal, Ordering::Release);
        PACING_ENABLED.store(self.config.percent.is_some(), Ordering::Release);
        self.refresh_gc_needed();
    }

    #[cfg_attr(not(test), allow(dead_code))]
    fn alloc_weak_cell(&mut self, target: *const u8) -> *mut u8 {
        let desc = crate::weak::cell_desc();
        let cell = self.alloc(desc.size, desc, false);
        unsafe { crate::weak::initialize_cell(cell, target) };
        self.register_weak_cell(cell, target);
        cell
    }

    fn register_weak_cell(&mut self, cell: *mut u8, target: *const u8) {
        // Interior pointers share the lifetime of their containing object, so
        // index the cell by the canonical allocation base while preserving the
        // original target address in the cell.
        if let Some(owner) = self.object_base(target) {
            self.weak_cells_by_owner
                .entry(owner)
                .or_default()
                .push(cell as usize);
        }
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
                if span_matches_class && span_matches_lane && !span.checked_out && span.has_free() {
                    return span_id;
                }
            }
        }
        self.new_small_span(class_index, lane)
    }

    fn checkout_span_for_class(&mut self, class_index: usize, lane: usize) -> CachedSpan {
        let span_id = self.take_span_for_class(class_index, lane);
        let span = self.spans[span_id]
            .as_mut()
            .expect("checked-out span exists");
        assert!(!span.checked_out, "span checked out twice");
        span.checked_out = true;
        self.stats.cached_span_refills = self.stats.cached_span_refills.saturating_add(1);
        CachedSpan {
            span_id,
            span: (&**span) as *const Span,
        }
    }

    fn return_checked_out_span(&mut self, span_id: usize) {
        let Some(span) = self.spans.get_mut(span_id).and_then(Option::as_mut) else {
            panic!("checked-out span disappeared before return");
        };
        assert!(span.checked_out, "returning span that is not checked out");
        span.checked_out = false;
        if span.has_free() && !span.in_class_list {
            let class_index = span.class_index.expect("cached span has a size class");
            let lane = span_lane(span.has_pointers);
            self.class_spans[class_index][lane].push(span_id);
            span.in_class_list = true;
        }
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
        self.spans[span_id] = Some(Box::new(span));
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
        let added_bytes = new_pages.saturating_mul(PAGE_SIZE);
        if self
            .config
            .memory_limit
            .is_some_and(|limit| self.segment_bytes().saturating_add(added_bytes) > limit)
        {
            self.stats.soft_limit_exceedances = self.stats.soft_limit_exceedances.saturating_add(1);
        }
        self.segments.push(Segment::new(new_pages));
        let index = self.segments.len() - 1;
        register_segment_arenas(&mut self.arena_map, &self.segments[index], index);
        let segment = &mut self.segments[index];
        let start_page = segment.alloc_pages(pages).expect("new segment has space");
        let base = unsafe { segment.data.add(start_page * PAGE_SIZE) };
        (index, start_page, base)
    }

    fn segment_bytes(&self) -> usize {
        self.segments.iter().map(|segment| segment.len).sum()
    }

    fn segment_growth_would_cross_soft_limit(&self, pages: usize) -> bool {
        let Some(limit) = self.config.memory_limit else {
            return false;
        };
        if self
            .segments
            .iter()
            .any(|segment| segment.can_alloc_pages(pages))
        {
            return false;
        }
        let growth = pages.max(SEGMENT_PAGES).saturating_mul(PAGE_SIZE);
        self.segment_bytes().saturating_add(growth) > limit
    }

    fn checkout_would_cross_soft_limit(&self, class_index: usize, lane: usize) -> bool {
        // Checked-out spans are exclusively owned by other mutators and cannot
        // satisfy this refill even when they still contain free slots.
        if self.spans.iter().flatten().any(|span| {
            span.class_index == Some(class_index)
                && span_lane(span.has_pointers) == lane
                && !span.checked_out
                && span.has_free()
        }) {
            return false;
        }
        self.segment_growth_would_cross_soft_limit(1)
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
        if !span.has_pointers
            || !atomic_bitset_get(&span.alloc_map, object_index, Ordering::Acquire)
        {
            return false;
        }
        let desc = span.descs[object_index].load(Ordering::Relaxed);
        let Some(desc) = (unsafe { desc.as_ref() }) else {
            return false;
        };
        let base = unsafe { span.base.add(object_index * span.object_size) };
        let limit = span.scan_sizes[object_index]
            .load(Ordering::Relaxed)
            .min(span.sizes[object_index].load(Ordering::Relaxed));
        let mut found = false;
        trace_desc_or_abort(desc, base, limit, TraceMode::Heap, |candidate| {
            if self.object_base(candidate) == Some(target) {
                found = true;
            }
        });
        found
    }

    fn collect(&mut self, threads: &[Arc<ThreadState>]) -> CollectionWork {
        // Stop-the-world collection: gather roots, mark, then sweep.
        assert!(
            self.spans.iter().flatten().all(|span| !span.checked_out),
            "collection began while a mutator owned an allocation span"
        );
        let mut manual_roots = std::mem::take(&mut self.manual_roots);
        let static_roots = std::mem::take(&mut self.static_roots);
        manual_roots.extend(self.persistent_roots.keys().copied());
        self.mark_roots(manual_roots.into_iter(), &static_roots, threads);
        self.static_roots = static_roots;
        self.process_weak_cells();
        let (freed, reclaimers, cleanup_handles) = self.sweep();
        let released_bytes = self.release_empty_segments();
        let scavenged_bytes = self.scavenge_free_pages();
        self.stats.released_bytes = self.stats.released_bytes.saturating_add(released_bytes);
        self.stats.scavenged_bytes = self.stats.scavenged_bytes.saturating_add(scavenged_bytes);
        let (free_runs, free_pages) = self.free_page_stats();
        let segment_count = self.segments.len();
        let segment_bytes = self.segment_bytes();
        self.stats.record_collection(
            freed.objects,
            freed.bytes,
            free_runs,
            free_pages.saturating_mul(PAGE_SIZE),
            segment_count,
            segment_bytes,
        );
        self.heap_goal = next_heap_goal(self.stats.live_bytes, self.config);
        self.stats.heap_goal = self.heap_goal;
        self.stats.configured_memory_limit = self.config.memory_limit;
        if self.publishes_global_pacing {
            self.publish_global_pacing_state();
        }
        self.stats.log();
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
        static_roots: &[StaticRoot],
        threads: &[Arc<ThreadState>],
    ) where
        I: IntoIterator<Item = *const u8>,
    {
        // Pre-allocate the mark stack to avoid reallocations during tracing.
        // 1024 pointers handles most workloads; deep graphs will still grow.
        const INITIAL_STACK_CAPACITY: usize = 1024;
        let mut stack: Vec<*const u8> = Vec::with_capacity(INITIAL_STACK_CAPACITY);
        stack.extend(manual_roots);

        for root in static_roots {
            let Some(desc) = (unsafe { root.desc.as_ref() }) else {
                continue;
            };
            trace_desc_or_abort(desc, root.start, desc.size, TraceMode::Heap, |candidate| {
                stack.push(candidate)
            });
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
        if !atomic_bitset_get(&span.alloc_map, object_index, Ordering::Acquire) {
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
        let desc = span.descs[object_index].load(Ordering::Relaxed);
        let desc = unsafe { desc.as_ref() };
        let Some(desc) = desc else {
            return;
        };
        if desc.node_count == 0 {
            return;
        }

        let payload_size = span.sizes[object_index].load(Ordering::Relaxed);
        let scan_size = span.scan_sizes[object_index]
            .load(Ordering::Relaxed)
            .min(payload_size);
        let base = unsafe { span.base.add(object_index * span.object_size) };
        let elem_size = desc.size;
        let is_array = atomic_bitset_get(&span.array_map, object_index, Ordering::Relaxed);

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
        trace_desc_or_abort(desc, base, limit, TraceMode::Heap, |candidate| {
            stack.push(candidate)
        });
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
                if atomic_bitset_get(&span.alloc_map, 0, Ordering::Acquire)
                    && !bitset_get(&span.mark_map, 0)
                {
                    let total_bytes = span.page_count.saturating_mul(PAGE_SIZE);
                    if let Some(reclaimer) = self.reclaimers.remove(&(span.base as *const u8)) {
                        reclaimers.push(reclaimer);
                    }
                    self.take_cleanup_handles(span.base as *const u8, &mut cleanup_handles);
                    atomic_bitset_set(&span.alloc_map, 0, false, Ordering::Release);
                    if span.has_pointers && !span.descs.is_empty() {
                        span.descs[0].store(std::ptr::null_mut(), Ordering::Relaxed);
                        span.sizes[0].store(0, Ordering::Relaxed);
                        span.scan_sizes[0].store(0, Ordering::Relaxed);
                    }
                    span.allocated.store(0, Ordering::Relaxed);
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
                if !atomic_bitset_get(&span.alloc_map, index, Ordering::Acquire) {
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
            if span.allocated.load(Ordering::Relaxed) == 0 {
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
        atomic_bitset_get(&span.alloc_map, object_index, Ordering::Acquire)
            .then(|| unsafe { span.base.add(object_index * span.object_size) as *const u8 })
    }

    fn object_is_marked(&self, ptr: *const u8) -> bool {
        let Some((span_id, object_index)) = self.find_object(ptr) else {
            return false;
        };
        let Some(span) = self.spans.get(span_id).and_then(Option::as_ref) else {
            return false;
        };
        atomic_bitset_get(&span.alloc_map, object_index, Ordering::Acquire)
            && bitset_get(&span.mark_map, object_index)
    }

    fn release_empty_segments(&mut self) -> usize {
        if self.segments.len() <= 1 {
            return 0;
        }
        let mut released = 0usize;
        let mut index = self.segments.len();
        while index != 0 && self.segments.len() > 1 {
            index -= 1;
            if self.segments[index]
                .page_map
                .iter()
                .any(|span_id| *span_id != SPAN_NONE)
            {
                continue;
            }
            released = released.saturating_add(self.segments[index].len);
            self.segments.remove(index);
            for span in self.spans.iter_mut().flatten() {
                if span.segment > index {
                    span.segment -= 1;
                }
            }
        }
        if released != 0 {
            self.rebuild_arena_map();
        }
        released
    }

    fn rebuild_arena_map(&mut self) {
        self.arena_map.clear();
        for (index, segment) in self.segments.iter().enumerate() {
            register_segment_arenas(&mut self.arena_map, segment, index);
        }
    }

    fn scavenge_free_pages(&mut self) -> usize {
        self.segments
            .iter_mut()
            .map(Segment::scavenge_free_runs)
            .fold(0usize, usize::saturating_add)
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
    let gc = INSTANCE.get_or_init(|| Mutex::new(Gc::new_runtime()));
    #[cfg(test)]
    GC_MUTEX_ACQUISITIONS.with(|count| count.set(count.get().saturating_add(1)));
    let mut guard = gc.lock().expect("gc mutex");
    f(&mut guard)
}

pub(crate) fn create_weak_cell(target: *const u8) -> *mut u8 {
    ensure_thread_registered();
    let desc = crate::weak::cell_desc();
    let cell = runtime_alloc_with_scan_size(desc.size, desc.size, desc, false);
    unsafe { crate::weak::initialize_cell(cell, target) };
    with_gc(|gc| gc.register_weak_cell(cell, target));
    cell
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
    unsafe { desc.as_ref().is_some_and(|d| d.node_count > 0) }
}

pub(crate) fn desc_nodes(desc: &GcDesc) -> &[GcLayoutNode] {
    if desc.node_count == 0 {
        return &[];
    }
    if desc.nodes.is_null() {
        eprintln!("fatal: GC descriptor {:p} has a null node table", desc);
        std::process::abort();
    }
    unsafe { std::slice::from_raw_parts(desc.nodes, desc.node_count) }
}

pub(crate) fn trace_desc_or_abort(
    desc: &GcDesc,
    base: *const u8,
    limit: usize,
    mode: TraceMode,
    emit: impl FnMut(*const u8),
) {
    if let Err(error) = unsafe { trace_layout(base, desc_nodes(desc), limit, mode, emit) } {
        eprintln!(
            "fatal: invalid live GC value for descriptor {:p} at {:p}: {error}",
            desc, base
        );
        std::process::abort();
    }
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

fn atomic_bitset(len: usize) -> Vec<AtomicU64> {
    (0..len).map(|_| AtomicU64::new(0)).collect()
}

fn atomic_bitset_get(bits: &[AtomicU64], index: usize, ordering: Ordering) -> bool {
    let word = index / 64;
    let bit = index % 64;
    bits.get(word)
        .is_some_and(|value| value.load(ordering) & (1_u64 << bit) != 0)
}

fn atomic_bitset_set(bits: &[AtomicU64], index: usize, value: bool, ordering: Ordering) {
    let word = index / 64;
    let bit = index % 64;
    let Some(slot) = bits.get(word) else {
        return;
    };
    let mask = 1_u64 << bit;
    if value {
        slot.fetch_or(mask, ordering);
    } else {
        slot.fetch_and(!mask, ordering);
    }
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

fn next_heap_goal(live_bytes: usize, config: GcConfig) -> usize {
    let Some(percent) = config.percent else {
        return usize::MAX;
    };
    let growth = (live_bytes as u128)
        .saturating_mul(u128::from(percent))
        .saturating_div(100)
        .min(usize::MAX as u128) as usize;
    let goal = GC_MIN_TRIGGER.max(live_bytes.saturating_add(growth));
    config.memory_limit.map_or(goal, |limit| {
        if live_bytes <= limit {
            // Equality must not republish an already-due goal before any new
            // allocation occurs. Exceed the limit by the smallest possible
            // amount; the next allocation then creates genuine pressure.
            goal.min(limit).max(live_bytes.saturating_add(1))
        } else {
            // A soft limit cannot be a useful percentage trigger once the
            // surviving heap has reached it. Back off above current live data
            // so the next allocation does not immediately request another
            // collection; future segment growth still performs its one
            // collect-and-scavenge pressure attempt.
            goal.max(live_bytes.saturating_add(GC_MIN_TRIGGER))
        }
    })
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
        __gc__alloc, __gc__collect, __gc__grow_buf, __gc__thread_attach, __gc__thread_detach,
        __gc__thread_enter_managed, __rt__gc_enter_blocking, __rt__gc_exit_blocking,
        CURRENT_THREAD_STATE, CleanupRegistration, GC_MIN_TRIGGER, GC_NEEDED_FLAG, GC_POLL_FLAGS,
        GC_REQUESTED_FLAG, Gc, GcConfig, GcDesc, GcStats, MAX_GC_PAUSE_SAMPLES, PAGE_SIZE,
        SEGMENT_SIZE, Segment, THREAD_REGISTRY, allocation_requires_slow_path, atomic_bitset_get,
        current_thread_gc_mutex_acquisitions, ensure_thread_registered, fully_free_os_page_range,
        next_heap_goal, os_page_size, parse_gc_memory_limit, parse_gc_percent,
        register_segment_arenas,
    };
    use crate::gc_layout::{GC_LAYOUT_POINTER, GcLayoutNode};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::mpsc;
    use std::time::Duration;

    static POINTER_NODES: [GcLayoutNode; 1] = [GcLayoutNode {
        offset: 0,
        stride: 0,
        first_child: 0,
        child_count: 0,
        kind: GC_LAYOUT_POINTER,
        width: 0,
        reserved: [0; 6],
    }];

    static BYTE_DESC: GcDesc = GcDesc {
        size: 16,
        align: 8,
        nodes: std::ptr::null(),
        node_count: 0,
    };

    fn bytes_desc(size: usize) -> GcDesc {
        GcDesc {
            size,
            align: 1,
            nodes: std::ptr::null(),
            node_count: 0,
        }
    }

    fn pointer_desc() -> GcDesc {
        GcDesc {
            size: std::mem::size_of::<*mut u8>(),
            align: std::mem::align_of::<*mut u8>(),
            nodes: POINTER_NODES.as_ptr(),
            node_count: POINTER_NODES.len(),
        }
    }

    fn count_finalization(data: usize) {
        let count = unsafe { &*(data as *const AtomicUsize) };
        count.fetch_add(1, Ordering::AcqRel);
    }

    #[test]
    fn gc_configuration_parses_documented_values() {
        assert_eq!(parse_gc_percent("off"), Ok(None));
        assert_eq!(parse_gc_percent("0"), Ok(Some(0)));
        assert_eq!(parse_gc_percent("10000"), Ok(Some(10_000)));
        assert!(parse_gc_percent("10001").is_err());
        assert!(parse_gc_percent("").is_err());

        assert_eq!(parse_gc_memory_limit("off"), Ok(None));
        assert_eq!(parse_gc_memory_limit("1B"), Ok(Some(1)));
        assert_eq!(parse_gc_memory_limit("2KiB"), Ok(Some(2 << 10)));
        assert_eq!(parse_gc_memory_limit("3MiB"), Ok(Some(3 << 20)));
        assert_eq!(parse_gc_memory_limit("4GiB"), Ok(Some(4 << 30)));
        if usize::BITS >= 64 {
            assert_eq!(parse_gc_memory_limit("5TiB"), Ok(Some(5 << 40)));
        }
        assert!(parse_gc_memory_limit("32").is_err());
        assert!(parse_gc_memory_limit("1MB").is_err());
        assert!(parse_gc_memory_limit("-1B").is_err());
    }

    #[test]
    fn stress_flag_slows_generated_polls_without_blocking_allocation() {
        assert!(!allocation_requires_slow_path(0, false));
        assert!(allocation_requires_slow_path(GC_NEEDED_FLAG, false));
        assert!(!allocation_requires_slow_path(GC_NEEDED_FLAG, true));
        assert!(allocation_requires_slow_path(GC_REQUESTED_FLAG, false));
        assert!(allocation_requires_slow_path(GC_REQUESTED_FLAG, true));
        assert!(allocation_requires_slow_path(
            GC_REQUESTED_FLAG | GC_NEEDED_FLAG,
            true
        ));
    }

    #[test]
    fn heap_goal_respects_percent_off_minimum_and_soft_limit() {
        assert_eq!(next_heap_goal(0, GcConfig::default()), GC_MIN_TRIGGER);
        assert_eq!(next_heap_goal(8 << 20, GcConfig::default()), 16 << 20);
        assert_eq!(
            next_heap_goal(
                8 << 20,
                GcConfig {
                    percent: Some(25),
                    memory_limit: Some(9 << 20),
                },
            ),
            9 << 20
        );
        assert_eq!(
            next_heap_goal(
                8 << 20,
                GcConfig {
                    percent: None,
                    memory_limit: Some(1),
                },
            ),
            usize::MAX
        );
        assert_eq!(
            next_heap_goal(
                12 << 20,
                GcConfig {
                    percent: Some(100),
                    memory_limit: Some(9 << 20),
                },
            ),
            24 << 20
        );
        assert_eq!(
            next_heap_goal(
                12 << 20,
                GcConfig {
                    percent: Some(0),
                    memory_limit: Some(9 << 20),
                },
            ),
            13 << 20
        );
        assert_eq!(
            next_heap_goal(
                9 << 20,
                GcConfig {
                    percent: Some(100),
                    memory_limit: Some(9 << 20),
                },
            ),
            (9 << 20) + 1
        );
    }

    #[test]
    fn warm_small_allocations_do_not_acquire_the_global_gc_mutex() {
        __gc__thread_enter_managed();
        let mut observed_uninterrupted_fast_path = false;
        // Runtime tests share the process-wide collector and run in parallel.
        // A collection requested by another test may legitimately flush this
        // thread's cache, so retry until the measured window contains no such
        // rendezvous; the assertion is specifically about an uninterrupted
        // warm path.
        for _ in 0..64 {
            __gc__collect();
            let first = __gc__alloc(BYTE_DESC.size, &BYTE_DESC);
            assert!(!first.is_null());
            let before = current_thread_gc_mutex_acquisitions();
            let mut uninterrupted = GC_POLL_FLAGS.load(Ordering::Acquire) == 0;
            for _ in 0..32 {
                uninterrupted &= GC_POLL_FLAGS.load(Ordering::Acquire) == 0;
                let allocation = __gc__alloc(BYTE_DESC.size, &BYTE_DESC);
                assert!(!allocation.is_null());
            }
            uninterrupted &= GC_POLL_FLAGS.load(Ordering::Acquire) == 0;
            if uninterrupted && current_thread_gc_mutex_acquisitions() == before {
                observed_uninterrupted_fast_path = true;
                break;
            }
        }
        assert!(observed_uninterrupted_fast_path);

        __rt__gc_enter_blocking();
        CURRENT_THREAD_STATE.with(|slot| {
            let slot = slot.borrow();
            let current = slot.as_ref().expect("registered mutator");
            assert!(current.cache.spans.iter().all(Option::is_none));
            assert_eq!(current.state.owned_spans.load(Ordering::Acquire), 0);
        });
        __rt__gc_exit_blocking();
        __gc__collect();
        __gc__thread_detach();
    }

    #[test]
    fn concurrent_cached_allocations_rendezvous_with_forced_gc() {
        const THREADS: usize = 4;
        const ALLOCATIONS: usize = 256;
        let barrier = std::sync::Arc::new(std::sync::Barrier::new(THREADS));
        std::thread::scope(|scope| {
            for thread_index in 0..THREADS {
                let barrier = barrier.clone();
                scope.spawn(move || {
                    __gc__thread_enter_managed();
                    barrier.wait();
                    for index in 0..ALLOCATIONS {
                        let allocation = __gc__alloc(BYTE_DESC.size, &BYTE_DESC);
                        assert!(!allocation.is_null());
                        unsafe {
                            allocation.write((thread_index ^ index) as u8);
                        }
                        if thread_index == 0 && index % 64 == 0 {
                            __gc__collect();
                        }
                    }
                    __gc__thread_detach();
                });
            }
        });
    }

    #[test]
    fn reused_small_slots_are_zero_before_publication() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        let desc = bytes_desc(16);
        let stale = gc.alloc(16, &desc, false);
        let keeper = gc.alloc(16, &desc, false);
        unsafe { std::ptr::write_bytes(stale, 0xa5, 16) };
        gc.add_root(keeper);
        assert!(gc.collect(&[]).is_empty());

        let reused = gc.alloc(16, &desc, false);
        assert_eq!(reused, stale);
        let bytes = unsafe { std::slice::from_raw_parts(reused, 16) };
        assert!(bytes.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn reused_large_pages_are_zero_before_publication() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        let size = PAGE_SIZE + 1;
        let desc = bytes_desc(size);
        let stale = gc.alloc(size, &desc, false);
        unsafe { std::ptr::write_bytes(stale, 0xa5, size) };
        assert!(gc.collect(&[]).is_empty());

        let reused = gc.alloc(size, &desc, false);
        assert_eq!(reused, stale);
        let bytes = unsafe { std::slice::from_raw_parts(reused, size) };
        assert!(bytes.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn sweep_releases_empty_segments_but_retains_one() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        let size = SEGMENT_SIZE + PAGE_SIZE;
        let desc = bytes_desc(size);
        let _ = gc.alloc(size, &desc, false);
        assert!(gc.segments.len() >= 2);

        assert!(gc.collect(&[]).is_empty());
        assert_eq!(gc.segments.len(), 1);
        assert!(gc.stats.released_bytes >= size);
    }

    #[cfg(unix)]
    #[test]
    fn partial_scavenging_is_accounted_once_and_cleared_on_reuse() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        let desc = bytes_desc(PAGE_SIZE);
        let pages_to_release = os_page_size().max(PAGE_SIZE) / PAGE_SIZE;
        let stale: Vec<_> = (0..pages_to_release)
            .map(|_| gc.alloc(PAGE_SIZE, &desc, false))
            .collect();
        let keeper = gc.alloc(PAGE_SIZE, &desc, false);
        unsafe { std::ptr::write_bytes(stale[0], 0xa5, PAGE_SIZE) };
        gc.add_root(keeper);

        assert!(gc.collect(&[]).is_empty());
        let expected = os_page_size().max(PAGE_SIZE);
        assert_eq!(gc.stats.scavenged_bytes, expected);
        gc.add_root(keeper);
        assert!(gc.collect(&[]).is_empty());
        assert_eq!(gc.stats.scavenged_bytes, expected);

        let reused = gc.alloc(PAGE_SIZE, &desc, false);
        assert!(stale.contains(&reused));
        let (segment, _) = gc.find_object(reused).expect("reused allocation");
        let span = gc.spans[segment].as_ref().expect("reused span");
        let segment = &gc.segments[span.segment];
        let mapping_base = segment.mapping.as_ref().unwrap().as_ptr() as usize;
        let os_page = (reused as usize - mapping_base) / segment.os_page_size;
        assert!(!segment.scavenged_os_pages[os_page]);
        let bytes = unsafe { std::slice::from_raw_parts(reused, PAGE_SIZE) };
        assert!(bytes.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn scavenging_uses_only_fully_free_native_pages() {
        let base = 0x1_0000;
        let native_page = 16 * 1024;

        assert_eq!(fully_free_os_page_range(base, 1, 1, native_page), None);
        assert_eq!(
            fully_free_os_page_range(base, 1, 3, native_page),
            Some(0x1_4000..0x1_8000)
        );
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
        let root_desc = pointer_desc();

        gc.register_static_root((&global_slot as *const *mut u8).cast::<u8>(), &root_desc);
        gc.collect(&[]);

        assert!(gc.find_object(child).is_some());
    }

    /// Whether `ptr` still names an allocated object.
    ///
    /// `find_object` only resolves an address to a span slot, and a swept slot
    /// keeps resolving while anything else in its span is alive — so liveness
    /// has to be read from the allocation bitmap.
    fn is_live(gc: &Gc, ptr: *const u8) -> bool {
        match gc.find_object(ptr) {
            Some((span_id, index)) => gc
                .spans
                .get(span_id)
                .and_then(|span| span.as_ref())
                .map(|span| atomic_bitset_get(&span.alloc_map, index, Ordering::Acquire))
                .unwrap_or(false),
            None => false,
        }
    }

    #[test]
    fn buffer_scan_size_limits_traced_elements() {
        // A buffer allocated with a scan size shorter than its payload traces
        // only that prefix. Nothing sets a scan size after the fact any more,
        // but the allocation-time limit is still how large objects are handled.
        let mut gc = Gc::new();
        let leaf_desc = bytes_desc(8);
        let pointer_desc = pointer_desc();
        let elem_size = std::mem::size_of::<*mut u8>();
        let inside = gc.alloc(8, &leaf_desc, false);
        let outside = gc.alloc(8, &leaf_desc, false);
        let buffer = gc.alloc_with_scan_size(elem_size * 2, elem_size, &pointer_desc, true);

        unsafe {
            (buffer as *mut *mut u8).write(inside);
            (buffer as *mut *mut u8).add(1).write(outside);
        }

        // Collected twice: an object allocated since the last cycle survives
        // its first one, so the second is what shows the scan limit.
        gc.add_root(buffer);
        gc.collect(&[]);
        gc.add_root(buffer);
        gc.collect(&[]);
        assert!(is_live(&gc, inside));
        assert!(!is_live(&gc, outside));
    }

    #[test]
    fn cleared_slot_stops_retaining_its_element() {
        // Managed buffers are scanned to their full capacity, so the owner
        // clears a slot it vacates. This is the invariant `List` relies on
        // instead of republishing its length to the collector on every pop.
        let mut gc = Gc::new();
        let leaf_desc = bytes_desc(8);
        let pointer_desc = pointer_desc();
        let elem_size = std::mem::size_of::<*mut u8>();
        let child = gc.alloc(8, &leaf_desc, false);
        let capacity = elem_size * 4;
        let buffer = gc.alloc_with_scan_size(capacity, capacity, &pointer_desc, true);

        // Written past the first slot, to show the whole capacity is traced.
        unsafe {
            (buffer as *mut *mut u8).add(2).write(child);
        }
        gc.add_root(buffer);
        gc.collect(&[]);
        gc.add_root(buffer);
        gc.collect(&[]);
        assert!(is_live(&gc, child));

        unsafe {
            (buffer as *mut *mut u8).add(2).write(std::ptr::null_mut());
        }
        gc.add_root(buffer);
        gc.collect(&[]);
        assert!(!is_live(&gc, child));
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
