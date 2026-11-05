//! Non-moving tracing collector and cooperative mutator coordination.
//! The GC metadata reader must install its stack-root reader before generated
//! code enters managed execution. Native-only test threads have no Taro roots.
//! User finalizer callbacks are not part of this pivot.

use std::cell::{Cell, RefCell, UnsafeCell};
use std::collections::{HashMap, VecDeque};
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU8, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, LazyLock, Mutex, OnceLock};
use std::time::{Duration, Instant};

use crate::gc_layout::{GcLayoutNode, TraceMode, trace_layout, trace_managed_edges};
use memmap2::MmapMut;

#[cfg(feature = "alloc-profile")]
mod alloc_profile;
mod parallel_mark;
pub(crate) mod root_slots;
mod size_classes;
use size_classes::CLASSES;

/// Pointers still to be marked.
type MarkStack = Vec<*const u8>;

// Keys are OS mapping buckets, so this index needs fast address hashing.
// Source-language dictionaries retain their keyed SipHash policy.
type ArenaMap = rustc_hash::FxHashMap<usize, Vec<usize>>;
// These keys are collector-owned allocation addresses, not caller-supplied
// dictionary keys. Sweeping touches them often.
type GcPointerMap<V> = rustc_hash::FxHashMap<*const u8, V>;

type RootReader = fn() -> Vec<*const u8>;
static ROOT_READER: OnceLock<RootReader> = OnceLock::new();

/// Install the reader matching the GC compiler metadata before managed entry.
/// Reinstallation with a different reader is a programming/ABI error.
pub(crate) fn install_root_reader(reader: RootReader) {
    if ROOT_READER.set(reader).is_err() {
        assert_eq!(
            *ROOT_READER.get().unwrap() as usize,
            reader as usize,
            "attempted to replace the GC root reader"
        );
    }
}

#[cfg(test)]
thread_local! {
    static TEST_ROOTS: RefCell<Vec<*const u8>> = const { RefCell::new(Vec::new()) };
}

fn capture_current_roots() -> Vec<*const u8> {
    let mut roots = ROOT_READER.get().map_or_else(Vec::new, |reader| reader());
    RUNTIME_ROOT.with(|head| {
        let mut frame = head.get();
        while let Some(root) = unsafe { frame.as_ref() } {
            // Storage may itself be a fresh heap object (an erased payload
            // whose nested payloads are being duplicated), so keep it live as
            // well as its fields. Stack addresses are ignored by the marker.
            roots.push(root.storage);
            let descriptor = unsafe { &*root.descriptor };
            if descriptor.node_count != 0 {
                let nodes =
                    unsafe { std::slice::from_raw_parts(descriptor.nodes, descriptor.node_count) };
                unsafe {
                    trace_layout(
                        root.storage,
                        nodes,
                        descriptor.size,
                        TraceMode::Stack,
                        |ptr| roots.push(ptr),
                    )
                }
                .expect("invalid runtime root descriptor");
            }
            frame = root.previous;
        }
    });
    #[cfg(test)]
    let roots = {
        let mut roots = roots;
        // A native mutator may unregister from its TLS destructor after the
        // test-only root vector has already been destroyed. Its scoped test
        // roots are gone then; attempting to re-enter destroyed TLS aborts.
        let _ = TEST_ROOTS.try_with(|extra| roots.extend(extra.borrow().iter().copied()));
        roots
    };
    roots
}

/// Runtime operations can allocate while working on typed stack temporaries
/// that have no compiler stack-map record. Link these roots without allocating
/// or locking. Collection reads them only on this mutator while publishing its
/// roots; the existing stop-the-world handshake then publishes that snapshot.
struct RuntimeRoot {
    previous: *const RuntimeRoot,
    storage: *const u8,
    descriptor: *const GcDesc,
}

thread_local! {
    static RUNTIME_ROOT: Cell<*const RuntimeRoot> = const { Cell::new(std::ptr::null()) };
}

impl Drop for RuntimeRoot {
    fn drop(&mut self) {
        RUNTIME_ROOT.with(|head| head.set(self.previous));
    }
}

/// # Safety
/// Storage contains one initialized value described by process-long immutable
/// metadata and remains valid throughout `operation`. The operation may mutate
/// it only to other valid values, including between nested collecting calls.
pub(crate) unsafe fn with_runtime_root<R>(
    storage: *const u8,
    descriptor: *const GcDesc,
    operation: impl FnOnce() -> R,
) -> R {
    let root = RuntimeRoot {
        previous: RUNTIME_ROOT.with(Cell::get),
        storage,
        descriptor,
    };
    RUNTIME_ROOT.with(|head| head.set(&root));
    let result = operation();
    drop(root);
    result
}

// === Public GC surface ===

/// Describes a GC-managed type.
///
/// - size: size in bytes for a single element of this type.
/// - align: ABI alignment for a single element of this type.
/// - nodes: indexed, tag-aware pointer-layout graph.
/// - node_count: number of nodes in the graph; zero means noscan.
///
/// Fixed arrays carry explicit repeat nodes. Managed sequence buffers compose
/// their element graph with a published initialized-prefix node.
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

/// A collected owner of one native bookkeeping pointer. It has no traced
/// edges; once unreachable, `release` frees the pointer after the world
/// restarts (G50). Open OS resources are never closed this way.
#[repr(C)]
struct GcNative {
    native: *mut u8,
}

static GC_NATIVE_DESC: GcDesc = GcDesc {
    size: std::mem::size_of::<GcNative>(),
    align: std::mem::align_of::<GcNative>(),
    nodes: std::ptr::null(),
    node_count: 0,
};

/// Allocate the collected owner of `native`, whose first word holds it.
pub(crate) fn gc_native_new(native: *mut u8, release: GcReclaimerFn) -> *mut u8 {
    let object = __gc__alloc(GC_NATIVE_DESC.size, &GC_NATIVE_DESC);
    unsafe { object.cast::<GcNative>().write(GcNative { native }) };
    // Registration cannot collect, so the new object needs no root here.
    with_gc(|gc| gc.register_reclaimer(object.cast_const(), release, native as usize));
    object
}

#[derive(Clone, Copy)]
struct GcReclaimer {
    callback: GcReclaimerFn,
    data: usize,
}

#[derive(Clone, Copy)]
struct StaticRoot {
    start: *const u8,
    desc: *const GcDesc,
}

#[derive(Default)]
struct CollectionWork {
    reclaimers: Vec<GcReclaimer>,
}

impl CollectionWork {
    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.reclaimers.is_empty()
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
    /// While parked in a generated blocking call: the calling Taro frame's
    /// stack pointer. The stack above it is frozen for the call, and the
    /// collector scans `[blocking_sp, stack_top)` conservatively instead of
    /// the thread walking its own stack on every call. Zero otherwise.
    blocking_sp: AtomicUsize,
    /// High end of this thread's stack, or zero when it is unknown.
    stack_top: usize,
}
unsafe impl Send for ThreadState {}
unsafe impl Sync for ThreadState {}

static THREAD_REGISTRY: Mutex<Vec<Arc<ThreadState>>> = Mutex::new(Vec::new());
static THREAD_REGISTRY_EPOCH: AtomicUsize = AtomicUsize::new(0);
static THREAD_ATTACHING: AtomicUsize = AtomicUsize::new(0);
const GC_REQUESTED_FLAG: u8 = 1 << 0;
const GC_NEEDED_FLAG: u8 = 1 << 1;
// Pair the collector's request publication with a mutator's resume
// publication. Release stores followed by Acquire loads permit both sides to
// miss each other's store (store buffering), including on ARM64.
const RENDEZVOUS_FENCE: Ordering = Ordering::SeqCst;
const ALLOCATION_DEBT_QUANTUM: usize = 64 * 1024;
const MUTATOR_CACHE_SIZE_CLASSES: usize = CLASSES.len();
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
    /// `TARO_GC_MARK_THREADS`, used for every collection. By default, `None`
    /// chooses from the heap's size and the threads the program runs on.
    mark_threads: Option<usize>,
}

impl Default for GcConfig {
    fn default() -> Self {
        Self {
            percent: Some(100),
            memory_limit: None,
            mark_threads: None,
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
        let mark_threads = match std::env::var_os("TARO_GC_MARK_THREADS") {
            None => None,
            Some(raw) => {
                let raw = raw
                    .into_string()
                    .map_err(|_| "TARO_GC_MARK_THREADS must contain valid Unicode".to_string())?;
                Some(parse_gc_mark_threads(&raw)?)
            }
        };
        Ok(Self {
            percent,
            memory_limit,
            mark_threads,
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

fn parse_gc_mark_threads(raw: &str) -> Result<usize, String> {
    raw.trim()
        .parse::<usize>()
        .ok()
        .filter(|threads| (1..=256).contains(threads))
        .ok_or_else(|| format!("TARO_GC_MARK_THREADS must be from 1 to 256; got `{raw}`"))
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

/// Fill pattern of freed cells while heap verification is enabled.
const GC_POISON_BYTE: u8 = 0xdb;

fn verify_poisoned_cell(cell: *const u8, size: usize) {
    let bytes = unsafe { std::slice::from_raw_parts(cell, size) };
    if let Some(offset) = bytes.iter().position(|byte| *byte != GC_POISON_BYTE) {
        eprintln!(
            "fatal: GC heap verification: freed cell {cell:p} was written at offset {offset} after it was freed"
        );
        std::process::abort();
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
pub(crate) fn collection_requested() -> bool {
    gc_requested(Ordering::Acquire)
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
        blocking_sp: AtomicUsize::new(0),
        stack_top: current_stack_top(),
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
            let roots = capture_current_roots();
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
                    // this thread's published roots. Detach left the state
                    // parked; a reattached thread is running again, exactly
                    // like a fresh registration, or collectors would treat it
                    // as stopped while it allocates and mutates.
                    current.state.at_safepoint.store(false, Ordering::Relaxed);
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
        let roots = capture_current_roots();
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
    #[cfg(not(test))]
    assert!(
        ROOT_READER.get().is_some(),
        "GC metadata root reader is not installed"
    );
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
        std::sync::atomic::fence(RENDEZVOUS_FENCE);
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

/// Run an idle runtime wait at a safepoint. A thread that has run managed code
/// stays registered with the collector, so waiting for work must not stall a
/// collection; the thread resumes only after any collection in progress ends.
/// Threads that never ran managed code are not registered and are left alone.
pub(crate) fn idle_wait<R>(wait: impl FnOnce() -> R) -> R {
    let resume = CURRENT_THREAD_STATE.with(|slot| {
        slot.borrow().as_ref().is_some_and(|current| {
            current.attached && !current.state.at_safepoint.load(Ordering::Relaxed)
        })
    });
    if resume {
        enter_safepoint();
    }
    let result = wait();
    if resume {
        leave_safepoint();
    }
    result
}

/// The roots of a thread's frames below a loop that polls tasks. Those frames stay
/// suspended for as long as the loop runs and the heap doesn't move, so these
/// roots hold whenever no poll is running. Unwinding for them on every idle wait
/// would cost more than the work between short waits.
pub(crate) struct OuterRoots(Vec<*const u8>);
impl OuterRoots {
    pub(crate) fn capture() -> Self {
        Self(capture_current_roots())
    }

    /// `idle_wait`, on the loop itself, with no poll running on this thread.
    pub(crate) fn idle_wait<R>(&self, wait: impl FnOnce() -> R) -> R {
        let resume = CURRENT_THREAD_STATE.with(|slot| {
            slot.borrow().as_ref().is_some_and(|current| {
                current.attached && !current.state.at_safepoint.load(Ordering::Relaxed)
            })
        });
        if resume {
            flush_current_mutator_cache();
            with_current_thread_state(|state| {
                // SAFETY: as in `publish_current_thread_roots`.
                let published = unsafe { &mut *state.published_roots.get() };
                published.clear();
                published.extend_from_slice(&self.0);
            });
            set_current_thread_safepoint(true);
        }
        let result = wait();
        if resume {
            leave_safepoint();
        }
        result
    }
}

/// Publish the current roots before entering a foreign call that may block
/// indefinitely.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__gc_enter_blocking() {
    enter_safepoint();
}

/// Park for a generated `extern "blocking"` call made by the frame whose stack
/// pointer is `sp`. Unlike `__rt__gc_enter_blocking` this does not walk the
/// stack: a collection that runs during the call scans the frozen stack above
/// `sp` conservatively, which the non-moving heap makes safe.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__gc_enter_blocking_at(sp: *const u8) {
    let parked = with_current_thread_state(|state| {
        if state.at_safepoint.load(Ordering::Relaxed) {
            return true;
        }
        if state.stack_top == 0 || (sp as usize) >= state.stack_top {
            return false;
        }
        flush_current_mutator_cache();
        // SAFETY: only the owning mutator writes this vector, before the
        // release store below publishes the safepoint.
        unsafe { (*state.published_roots.get()).clear() };
        state.blocking_sp.store(sp as usize, Ordering::Relaxed);
        state.at_safepoint.store(true, Ordering::Release);
        true
    });
    if !parked {
        enter_safepoint();
    }
}

/// Wait for any active collection and resume Taro execution after a blocking
/// foreign call returns.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__gc_exit_blocking() {
    leave_safepoint();
    // Only after resuming: a collection that observed this thread parked may
    // still be scanning its stack until the world restarts.
    with_current_thread_state(|state| state.blocking_sp.store(0, Ordering::Relaxed));
}

/// Enter Taro from a foreign caller through a compiler-generated callback
/// shim. A thread first seen here registers as a mutator; a thread that was
/// parked (idle after an earlier callback, or inside a blocking call that
/// called back) resumes. The returned token restores that state on exit: 0
/// when the thread was already running Taro, otherwise the parked stack
/// pointer with the low bit set.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__foreign_enter() -> usize {
    let first_entry = CURRENT_THREAD_STATE.with(|slot| {
        slot.borrow()
            .as_ref()
            .is_none_or(|current| !current.attached)
    });
    if first_entry {
        ensure_thread_registered();
        return 1;
    }
    let parked_sp = with_current_thread_state(|state| {
        state
            .at_safepoint
            .load(Ordering::Relaxed)
            .then(|| state.blocking_sp.load(Ordering::Relaxed))
    });
    let Some(sp) = parked_sp else {
        return 0;
    };
    leave_safepoint();
    // The callback runs below the parked frames; collections during it walk
    // the whole stack precisely, so the conservative range must not linger.
    with_current_thread_state(|state| state.blocking_sp.store(0, Ordering::Relaxed));
    sp | 1
}

/// Leave Taro back to the foreign caller of a callback shim, parking the
/// thread again unless it was running Taro code when the callback began. An
/// idle foreign thread has no Taro frames left, so it parks with no roots.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__foreign_exit(token: usize) {
    if token == 0 {
        return;
    }
    flush_current_mutator_cache();
    with_current_thread_state(|state| {
        // SAFETY: only the owning mutator writes this vector, before the
        // release store below publishes the safepoint.
        unsafe { (*state.published_roots.get()).clear() };
        state.blocking_sp.store(token & !1, Ordering::Relaxed);
        state.at_safepoint.store(true, Ordering::Release);
    });
}

#[cfg(target_os = "macos")]
fn current_stack_top() -> usize {
    unsafe { libc::pthread_get_stackaddr_np(libc::pthread_self()) as usize }
}

#[cfg(all(unix, not(target_os = "macos")))]
fn current_stack_top() -> usize {
    unsafe {
        let mut attr: libc::pthread_attr_t = std::mem::zeroed();
        if libc::pthread_getattr_np(libc::pthread_self(), &mut attr) != 0 {
            return 0;
        }
        let mut base = std::ptr::null_mut();
        let mut size = 0;
        let found = libc::pthread_attr_getstack(&attr, &mut base, &mut size) == 0;
        libc::pthread_attr_destroy(&mut attr);
        if found { base as usize + size } else { 0 }
    }
}

#[cfg(not(unix))]
fn current_stack_top() -> usize {
    0
}

/// Treat every aligned word of a parked thread's frozen stack range as a
/// candidate root; `mark_ptr` ignores words that are not live heap objects.
fn push_conservative_stack(stack: &mut Vec<*const u8>, sp: usize, top: usize) {
    let word = std::mem::size_of::<usize>();
    let mut address = sp.next_multiple_of(word);
    while address + word <= top {
        // SAFETY: the range lies on a registered thread's stack above the frame
        // that parked, which cannot change until that thread resumes.
        let value = unsafe { std::ptr::read(address as *const usize) };
        if value != 0 {
            stack.push(value as *const u8);
        }
        address += word;
    }
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

fn gc_trace_enabled() -> bool {
    static ENABLED: LazyLock<bool> =
        LazyLock::new(|| std::env::var_os("TARO_GC_TRACE").is_some_and(|value| value == "1"));
    *ENABLED
}

/// One `TARO_GC_TRACE=1` summary line per collection.
fn trace_collection(pause: Duration) {
    let stats = stats_snapshot();
    let before = stats.live_bytes.saturating_add(stats.last_freed_bytes);
    eprintln!(
        "gc {}: pause {:.3}ms, heap {} -> {} bytes (goal {}), freed {} objects, reserved {} bytes, total pause {:.3}ms",
        stats.collections,
        pause.as_secs_f64() * 1e3,
        before,
        stats.live_bytes,
        stats.heap_goal,
        stats.last_freed_objects,
        stats.segment_bytes,
        stats.total_pause_ns as f64 / 1e6,
    );
}

fn initiate_collection() {
    flush_current_mutator_cache();
    // Ensure only one thread acts as the collector
    if GC_POLL_FLAGS.fetch_or(GC_REQUESTED_FLAG, Ordering::AcqRel) & GC_REQUESTED_FLAG != 0 {
        park_at_safepoint();
        return;
    }
    std::sync::atomic::fence(RENDEZVOUS_FENCE);
    let pause_started = Instant::now();

    let current_id = std::thread::current().id();
    // The initiating mutator is not parked (and therefore is not waited on),
    // but its generated callers are suspended inside this runtime call. Walk
    // them now while this thread still owns all of its register state.
    publish_current_thread_roots();
    let threads = threads_for_collection(current_id);
    let rendezvous = pause_started.elapsed();

    // Now all other threads are parked. Discovery and heap reclamation happen
    // during the pause, but native resource reclaimers must wait until the
    // world is running again. Even runtime-only reclaimers may take subsystem
    // locks or wake tasks.
    let work = with_gc(|gc| {
        add_elapsed(&mut gc.stats.phases.rendezvous_ns, rendezvous);
        gc.collect(&threads)
    });
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
    // Trace output locks stderr, so keep it outside the stop-the-world
    // interval. Concurrent collections may interleave their lines.
    if gc_trace_enabled() {
        trace_collection(pause);
    }

    // A different mutator may request the next collection as soon as the
    // world resumes. Do not assert that the process-wide request bit remains
    // clear while the previous collection's reclaimers are running.
    for reclaimer in work.reclaimers {
        (reclaimer.callback)(reclaimer.data);
    }
    // A recovered out-of-memory panic spent the reserve; restore it once a
    // collection has made room.
    install_emergency_reserve();
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
    // Stress mode deliberately leaves GC_NEEDED set so every generated poll
    // collects; `runtime_alloc` already collected once for this allocation,
    // and collecting again here would make a cache refill retry forever.
    if gc_needed(Ordering::Relaxed) && !gc_stress_enabled() {
        initiate_collection();
        collected = true;
    }
    collected
}

#[inline]
fn small_class(alloc_size: usize, alignment: usize) -> (usize, usize) {
    let index = size_classes::class_for(alloc_size, alignment);
    (index, CLASSES[index].size)
}

fn try_cached_small_allocation<const ZEROED: usize>(
    cache_slot: usize,
    class_size: usize,
    payload_size: usize,
    desc: *const GcDesc,
) -> Option<*mut u8> {
    let flags = GC_POLL_FLAGS.load(Ordering::Acquire);
    if flags != 0 && allocation_requires_slow_path(flags, gc_stress_enabled()) {
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
        let ptr = span.alloc_small::<ZEROED>(payload_size, desc)?;
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

    let mut attempted_out_of_memory_collection = false;
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
        match result {
            Some(Some(cached)) => break cached,
            Some(None) if attempted_out_of_memory_collection => raise_out_of_memory(),
            Some(None) => attempted_out_of_memory_collection = true,
            None => {}
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

/// Released just before reporting heap exhaustion so the panic report and
/// unwinding can still allocate native memory.
static EMERGENCY_RESERVE: AtomicPtr<u8> = AtomicPtr::new(std::ptr::null_mut());
const EMERGENCY_RESERVE_BYTES: usize = 64 << 10;

fn emergency_reserve_layout() -> std::alloc::Layout {
    std::alloc::Layout::from_size_align(EMERGENCY_RESERVE_BYTES, 16).expect("valid reserve layout")
}

fn install_emergency_reserve() {
    if !EMERGENCY_RESERVE.load(Ordering::Acquire).is_null() {
        return;
    }
    let block = unsafe { std::alloc::alloc(emergency_reserve_layout()) };
    if !block.is_null()
        && EMERGENCY_RESERVE
            .compare_exchange(
                std::ptr::null_mut(),
                block,
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .is_err()
    {
        unsafe { std::alloc::dealloc(block, emergency_reserve_layout()) };
    }
}

fn release_emergency_reserve() {
    let block = EMERGENCY_RESERVE.swap(std::ptr::null_mut(), Ordering::AcqRel);
    if !block.is_null() {
        unsafe { std::alloc::dealloc(block, emergency_reserve_layout()) };
    }
}

/// Reports heap exhaustion as a Taro panic. Callers hold no GC lock or
/// thread-state borrow; a panic that cannot be raised aborts with a report.
#[cold]
fn raise_out_of_memory() -> ! {
    release_emergency_reserve();
    raise_allocation_panic("out of memory")
}

#[cold]
fn raise_allocation_panic(message: &'static str) -> ! {
    crate::panic_unwind::__rt__panic_unwind(crate::panic_unwind::RtString {
        ptr: message.as_ptr(),
        len: message.len(),
    })
}

/// Rounds a request up to its descriptor alignment, rejecting sizes that no
/// allocation can satisfy before any heap state changes.
fn checked_alloc_size(size: usize, desc: *const GcDesc) -> usize {
    let align = desc_alignment(desc).max(std::mem::size_of::<usize>());
    match size.checked_add(align - 1) {
        Some(padded) if size <= isize::MAX as usize && padded <= isize::MAX as usize => {
            padded & !(align - 1)
        }
        _ => raise_allocation_panic("allocation size overflow"),
    }
}

fn runtime_alloc<const ZEROED: usize>(size: usize, desc: *const GcDesc) -> *mut u8 {
    #[cfg(feature = "alloc-profile")]
    alloc_profile::record_managed(size, desc);
    let alloc_size = checked_alloc_size(size, desc);
    if gc_stress_enabled() {
        // Stress collects once before every allocation, which then proceeds
        // without re-entering collection so it always makes progress.
        ensure_thread_registered();
        initiate_collection();
    }
    if alloc_size > PAGE_SIZE {
        ensure_thread_registered();
        let mut attempted_soft_limit_collection = prepare_for_allocation();
        let mut attempted_out_of_memory_collection = false;
        let pages = pages_for_size(alloc_size);
        loop {
            let allocation = with_gc(|gc| {
                if !attempted_soft_limit_collection
                    && gc.segment_growth_would_cross_soft_limit(pages)
                {
                    None
                } else {
                    Some(gc.try_alloc::<ZEROED>(size, desc))
                }
            });
            match allocation {
                Some(Some(allocation)) => return allocation,
                Some(None) if attempted_out_of_memory_collection => raise_out_of_memory(),
                Some(None) => attempted_out_of_memory_collection = true,
                None => {}
            }
            initiate_collection();
            attempted_soft_limit_collection = true;
        }
    }

    let (class_index, class_size) = small_class(
        alloc_size,
        desc_alignment(desc).max(std::mem::size_of::<usize>()),
    );
    let lane = span_lane(desc_has_pointers(desc));
    let cache_slot = class_index * 2 + lane;
    loop {
        if let Some(ptr) = try_cached_small_allocation::<ZEROED>(cache_slot, class_size, size, desc)
        {
            return ptr;
        }
        // The cache probe already checks attached TLS and collection requests.
        // Registration is needed only on a miss, including first use and
        // detach/reattach, so warm object allocation takes one TLS borrow.
        ensure_thread_registered();
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
pub extern "C-unwind" fn __gc__alloc(size: usize, desc: *const GcDesc) -> *mut u8 {
    if size == 0 || desc.is_null() {
        ensure_thread_registered();
        return std::ptr::null_mut();
    }
    runtime_alloc::<{ usize::MAX }>(size, desc)
}

/// Allocate storage whose descriptor reads only a zeroed prefix until its
/// owner explicitly publishes fully initialized values.
/// # Safety
/// The descriptor must not read bytes beyond `ZEROED` before those bytes have
/// been initialized. No source-language zero-initialization is provided there.
/// This is used only by the sequence header's initialized-prefix contract.
pub(crate) unsafe fn alloc_with_zeroed_prefix<const ZEROED: usize>(
    size: usize,
    desc: *const GcDesc,
) -> *mut u8 {
    debug_assert!(ZEROED <= size && !desc.is_null());
    runtime_alloc::<ZEROED>(size, desc)
}

#[unsafe(no_mangle)]
pub extern "C" fn __gc__collect() {
    ensure_thread_registered();
    initiate_collection();
}

/// `std::runtime::collect()`: run a full collection now. Generated callers
/// record a stack map for the call, so this thread's roots are exact.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__gc_collect() {
    __gc__collect();
}

/// Field order matches `std::runtime::GcStats`.
#[repr(C)]
pub struct GcStatsRecord {
    pub collections: u64,
    pub heap_bytes: u64,
    pub reserved_bytes: u64,
    pub heap_goal_bytes: u64,
    pub allocated_bytes: u64,
    pub freed_bytes: u64,
    pub total_pause_nanos: u64,
    pub last_pause_nanos: u64,
}

/// `std::runtime::gcStats()`. The calling thread's allocation cache is
/// flushed first so its own allocations are counted; other threads' caches
/// are counted when they flush.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__gc_stats(out: *mut GcStatsRecord) {
    if out.is_null() {
        return;
    }
    flush_current_mutator_cache();
    let snapshot = stats_snapshot();
    let record = GcStatsRecord {
        collections: snapshot.collections as u64,
        heap_bytes: snapshot.live_bytes as u64,
        reserved_bytes: snapshot.segment_bytes as u64,
        heap_goal_bytes: snapshot.heap_goal as u64,
        allocated_bytes: snapshot.total_allocated_bytes as u64,
        freed_bytes: snapshot.total_freed_bytes as u64,
        total_pause_nanos: snapshot.total_pause_ns,
        last_pause_nanos: snapshot.pause_samples.last().map_or(0, |(_, nanos)| *nanos),
    };
    unsafe { out.write(record) };
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

/// Register an exact typed global/static root.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__register_static(start: *const u8, desc: *const GcDesc) {
    if start.is_null() || desc.is_null() {
        return;
    }
    with_gc(|gc| gc.register_static_root(start, desc));
}

// === Runtime GC implementation ===

// Allocation constants.
const PAGE_SIZE: usize = 8 * 1024;
const SEGMENT_SIZE: usize = 1 << 20; // 1 MiB
const SEGMENT_PAGES: usize = SEGMENT_SIZE / PAGE_SIZE;
// Small live heaps still need enough allocation headroom to amortize native
// root discovery and collection. Keep this independent of the segment size.
const GC_MIN_TRIGGER: usize = 4 << 20;
// A collection stops every mutator, so a busy process whose heap target is small
// can spend much of its time stopped. While collections take more than 1 part in
// GC_LARGER_HEAP_RATIO of the time, the target doubles, up to GC_MAX_HEAP_SCALE
// times its usual size. It halves again below 1 part in GC_SMALLER_HEAP_RATIO.
const GC_LARGER_HEAP_RATIO: u32 = 50;
const GC_SMALLER_HEAP_RATIO: u32 = 200;
const GC_MAX_HEAP_SCALE: usize = 16;
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
    // Native VM pages successfully advised as disposable. One VM page may
    // cover several allocator pages (notably 16 KiB Darwin over 8 KiB spans),
    // so accounting and reuse invalidation must use this granularity.
    scavenged_os_pages: Vec<bool>,
    os_page_size: usize,
}

impl Segment {
    /// Maps a segment, or returns `None` when the OS refuses the mapping or
    /// its page tables, which the caller reports as running out of memory.
    fn try_new(pages: usize) -> Option<Self> {
        // Over-map by one logical page so the usable subrange can retain the
        // allocator's stronger PAGE_SIZE alignment on platforms whose native
        // mapping alignment is smaller.
        let bytes = pages.checked_mul(PAGE_SIZE)?;
        let mapping_len = bytes.checked_add(PAGE_SIZE)?;
        let mut mapping = MmapMut::map_anon(mapping_len).ok()?;
        let raw = mapping.as_mut_ptr() as usize;
        let data = align_up(raw, PAGE_SIZE) as *mut u8;
        let os_page_size = os_page_size();
        let mut page_map = Vec::new();
        page_map.try_reserve_exact(pages).ok()?;
        page_map.resize(pages, SPAN_NONE);
        let os_pages = mapping_len.div_ceil(os_page_size);
        let mut scavenged_os_pages = Vec::new();
        scavenged_os_pages.try_reserve_exact(os_pages).ok()?;
        scavenged_os_pages.resize(os_pages, false);
        Some(Self {
            mapping: Some(mapping),
            data,
            len: bytes,
            page_map,
            next_page: 0,
            free_runs: Vec::new(),
            scavenged_os_pages,
            os_page_size,
        })
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
                    self.free_runs.remove(i);
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
        #[cfg(target_vendor = "apple")]
        {
            // Pair Darwin's FREE_REUSABLE with FREE_REUSE before publishing
            // allocations. Only touch still-scavenged native pages: an 8 KiB
            // allocation may already occupy the other half of a 16 KiB page.
            let mut page = first.min(end);
            while page < end {
                if !self.scavenged_os_pages[page] {
                    page += 1;
                    continue;
                }
                let begin = page;
                while page < end && self.scavenged_os_pages[page] {
                    page += 1;
                }
                // SAFETY: these pages have no live allocations or borrows.
                // Reuse updates OS accounting; explicit allocation zeroing
                // still guarantees initialization even if this advice fails.
                let _ = unsafe {
                    mapping.unchecked_advise_range(
                        memmap2::UncheckedAdvice::FreeReuse,
                        begin * self.os_page_size,
                        (page - begin) * self.os_page_size,
                    )
                };
            }
        }
        for scavenged in &mut self.scavenged_os_pages[first.min(end)..end] {
            *scavenged = false;
        }
    }

    #[cfg(unix)]
    fn scavenge_free_runs(&mut self, retain_bytes: &mut usize) -> usize {
        use memmap2::UncheckedAdvice;

        // Darwin's DONTNEED does not discard dirty anonymous pages. Use the
        // same reusable/reuse pair as Go's runtime/mem_darwin.go; Linux keeps
        // its immediate-discard advice. Neither path changes the warm budget.
        #[cfg(target_vendor = "apple")]
        let advice = UncheckedAdvice::FreeReusable;
        #[cfg(not(target_vendor = "apple"))]
        let advice = UncheckedAdvice::DontNeed;

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
                // Retain the first reusable pages in allocation order. The
                // budget is shared across segments and counts only resident
                // free pages, never pages already returned to the OS.
                let retained = (page - start).min(*retain_bytes / self.os_page_size);
                *retain_bytes -= retained * self.os_page_size;
                let start = start + retained;
                if start == page {
                    continue;
                }
                let offset = start.saturating_mul(self.os_page_size);
                let len = (page - start).saturating_mul(self.os_page_size);
                // SAFETY: collection is stop-the-world, this run has no span
                // owner in the page map, and no allocation can hold a Rust
                // borrow into these free pages. The OS may replace their
                // contents with zero-fill pages, which is why memmap2 models
                // the operation as a conceptual write.
                if unsafe { mapping.unchecked_advise_range(advice, offset, len) }.is_ok() {
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
    fn scavenge_free_runs(&mut self, _retain_bytes: &mut usize) -> usize {
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
    // and acquire-read; mark bits are only for the threads marking during
    // stop-the-world, and those need nothing more of them than to be atomic.
    alloc_map: Vec<AtomicU64>,
    mark_map: Vec<AtomicU64>,

    // Per-slot metadata (only populated for scan spans).
    descs: Vec<AtomicPtr<GcDesc>>,
    // Requested payload bytes for each slot.
    sizes: Vec<AtomicUsize>,

    // Clear allocation bits are the free slots, and every one before this word's
    // start is taken: only sweep clears bits, and it resets this too. A checked-out
    // mutator exclusively owns this. The collector may access it only after every
    // cache is flushed by the safepoint handshake.
    free_search_word: UnsafeCell<usize>,
    /// Heap verification: every free slot holds `GC_POISON_BYTE`, checked
    /// when the slot is reused.
    poisoned: bool,
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
            mark_map: atomic_bitset(bit_len),
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
            free_search_word: UnsafeCell::new(0),
            allocated: AtomicUsize::new(0),
            in_class_list: false,
            checked_out: false,
            poisoned: false,
        }
    }

    // Large allocations get their own span; only one object lives here.
    fn new_large(
        base: *mut u8,
        segment: usize,
        start_page: usize,
        page_count: usize,
        payload_size: usize,
        desc: *const GcDesc,
        has_pointers: bool,
    ) -> Self {
        // A large span holds exactly one object and uses whole pages.
        let span_bytes = page_count.saturating_mul(PAGE_SIZE);
        let bit_len = bitset_len(1);
        let alloc_map = atomic_bitset(bit_len);
        let mark_map = atomic_bitset(bit_len);
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
            descs,
            sizes,
            free_search_word: UnsafeCell::new(0),
            allocated: AtomicUsize::new(1),
            in_class_list: false,
            checked_out: false,
            poisoned: false,
        }
    }

    fn has_free(&self) -> bool {
        // Indicates whether there is at least one free slot.
        self.allocated.load(Ordering::Relaxed) < self.object_count
    }

    // Allocate one slot in a small-object span.
    fn alloc_small<const ZEROED: usize>(
        &self,
        payload_size: usize,
        desc: *const GcDesc,
    ) -> Option<*mut u8> {
        // Clear the scanner-visible storage before publishing the allocation bit.
        // Ordinary objects clear the whole slot. Sequence buffers clear their
        // header: its zero initialized count keeps spare capacity untraced.
        debug_assert!(
            payload_size <= self.object_size,
            "payload {} exceeds span object size {}",
            payload_size,
            self.object_size
        );
        // SAFETY: either the global allocator or the sole checked-out mutator
        // owns the span when this method is called.
        let index = self.next_free_slot()?;
        let ptr = unsafe { self.base.add(index * self.object_size) };
        if self.poisoned {
            verify_poisoned_cell(ptr, self.object_size);
        }
        unsafe { clear_cell(ptr, ZEROED.min(self.object_size)) };
        if self.has_pointers {
            self.descs[index].store(desc.cast_mut(), Ordering::Relaxed);
            self.sizes[index].store(payload_size, Ordering::Relaxed);
        }
        // Like `allocated` below: only the span's one owner sets these bits, and
        // sweep clears them after owners park, so setting needs no locked update.
        let word = &self.alloc_map[index / 64];
        word.store(
            word.load(Ordering::Relaxed) | (1_u64 << (index % 64)),
            Ordering::Release,
        );
        // Allocation has one span owner; sweep writes this count only after
        // owners park and return their caches. Readers still use atomic loads,
        // but updating the owner's count needs no locked read-modify-write.
        let allocated = self.allocated.load(Ordering::Relaxed);
        self.allocated.store(allocated + 1, Ordering::Relaxed);
        Some(ptr)
    }

    // The lowest free slot, which the caller goes on to take.
    #[inline]
    fn next_free_slot(&self) -> Option<usize> {
        // SAFETY: as for `alloc_small`, this thread owns the span.
        let search = unsafe { &mut *self.free_search_word.get() };
        while let Some(word) = self.alloc_map.get(*search) {
            let taken = word.load(Ordering::Relaxed);
            if taken != u64::MAX {
                let index = *search * 64 + (!taken).trailing_zeros() as usize;
                // Past the last slot, a final word's clear bits are not slots.
                return (index < self.object_count).then_some(index);
            }
            *search += 1;
        }
        None
    }

    /// Free every unmarked slot and clear the marks, returning how many were freed.
    /// This is one step per bitmap word, however many objects the words cover.
    /// Metadata of a free slot is never read, and allocation replaces it.
    fn sweep_slots(&mut self) -> usize {
        let mut freed = 0;
        for (word, (allocated, marks)) in self
            .alloc_map
            .iter_mut()
            .zip(self.mark_map.iter_mut())
            .enumerate()
        {
            let live = *marks.get_mut();
            let mut dead = *allocated.get_mut() & !live;
            freed += dead.count_ones() as usize;
            if self.poisoned {
                while dead != 0 {
                    let index = word * 64 + dead.trailing_zeros() as usize;
                    let cell = unsafe { self.base.add(index * self.object_size) };
                    unsafe { std::ptr::write_bytes(cell, GC_POISON_BYTE, self.object_size) };
                    dead &= dead - 1;
                }
            }
            // Every marked slot was allocated when it was marked.
            *allocated.get_mut() = live;
            *marks.get_mut() = 0;
        }
        *self.free_search_word.get_mut() = 0;
        *self.allocated.get_mut() -= freed;
        freed
    }

    /// Make a span that nothing in it survived in usable again, as if newly created.
    fn reset_empty(&mut self) {
        for word in &mut self.alloc_map {
            *word.get_mut() = 0;
        }
        *self.free_search_word.get_mut() = 0;
        *self.allocated.get_mut() = 0;
    }
}

const MAX_GC_PAUSE_SAMPLES: usize = 1024;

/// Cumulative wall time in disjoint collection phases. Rendezvous includes the
/// initiating thread's root publication and waiting for other threads; their
/// overlapping publication work must not be added to it again.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct GcPhaseTimes {
    pub rendezvous_ns: u64,
    pub mark_ns: u64,
    pub weak_ns: u64,
    pub sweep_ns: u64,
    pub scavenge_ns: u64,
}

fn add_elapsed(total: &mut u64, elapsed: Duration) {
    *total = total.saturating_add(elapsed.as_nanos().min(u64::MAX as u128) as u64);
}

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
    pub phases: GcPhaseTimes,
    pub total_pause_ns: u64,
    pub last_freed_objects: usize,
    pub last_freed_bytes: usize,
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
    phases: GcPhaseTimes,
    total_pause_ns: u64,
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
        self.record_frees(1, size);
    }

    fn record_frees(&mut self, count: usize, bytes: usize) {
        self.total_frees = self.total_frees.saturating_add(count);
        self.total_freed_bytes = self.total_freed_bytes.saturating_add(bytes);
        self.live_objects = self.live_objects.saturating_sub(count);
        self.live_bytes = self.live_bytes.saturating_sub(bytes);
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
        add_elapsed(&mut self.total_pause_ns, pause);
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
            phases: self.phases,
            total_pause_ns: self.total_pause_ns,
            last_freed_objects: self.last_freed_objects,
            last_freed_bytes: self.last_freed_bytes,
            pause_samples: self.pause_samples.iter().copied().collect(),
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
    // Earlier segments that failed a fixed-size request cannot fit it again
    // until pages are freed. Track the first possible segment for 1..8 pages;
    // larger requests retain the ordinary first-fit scan.
    page_search_starts: [usize; 9],
    // Maps arena index (address / SEGMENT_SIZE) to candidate segment indices.
    // Segments are page-aligned, not SEGMENT_SIZE-aligned, so multiple segments
    // can share an arena bucket and large segments can span multiple buckets.
    arena_map: ArenaMap,
    // Boxed records keep checked-out span addresses stable across vector
    // growth while the heap mutex is not held.
    spans: Vec<Option<Box<Span>>>,
    // Free list of span IDs for reuse (prevents unbounded growth of spans vec).
    free_span_ids: Vec<usize>,
    // Per size class: [scan spans, noscan spans].
    class_spans: Vec<[Vec<usize>; 2]>,
    // Per size class: [scan, noscan] spans taken for allocation since the last
    // collection, which is how many empty ones that collection keeps for reuse.
    span_demand: Vec<[usize; 2]>,
    // Pages of the empty spans the last sweep kept, which stay resident.
    kept_empty_span_bytes: usize,
    last_marked_objects: usize,
    static_roots: Vec<StaticRoot>,
    #[cfg(test)]
    manual_roots: Vec<*const u8>,
    persistent_roots: GcPointerMap<usize>,
    // Scanned whole at every sweep and never looked up by owner.
    reclaimers: Vec<(*const u8, GcReclaimer)>,
    // Weak cells do not trace their targets. This side table lets the mark
    // phase clear cells whose canonical owner is about to be reclaimed.
    weak_cells_by_owner: HashMap<*const u8, Vec<usize>>,
    stats: GcStats,
    config: GcConfig,
    // Absolute live-heap goal at which percentage pacing requests collection.
    heap_goal: usize,
    publishes_global_pacing: bool,
    // Whether the heap target may follow the time collections take. An explicit
    // `TARO_GC_PERCENT` asks for that percentage and no other.
    scales_heap_goal: bool,
    heap_goal_scale: usize,
    last_collection_end: Option<Instant>,
    /// `TARO_GC_STRESS` heap verification: poison freed cells and check
    /// that no live managed edge reaches freed storage (G54).
    verify: bool,
}

// GC is only accessed under a Mutex; raw pointers are fine.
unsafe impl Send for Gc {}
unsafe impl Sync for Gc {}

impl Gc {
    fn new() -> Self {
        let mut gc = Self::new_with_config(*gc_config());
        gc.verify = gc_stress_enabled();
        gc
    }

    fn new_runtime() -> Self {
        install_emergency_reserve();
        let mut gc = Self::new();
        gc.publishes_global_pacing = true;
        gc.scales_heap_goal = std::env::var_os("TARO_GC_PERCENT").is_none();
        gc.publish_global_pacing_state();
        gc
    }

    fn new_with_config(config: GcConfig) -> Self {
        // Initialize size classes, span lists, and the first segment.
        debug_assert!(SEGMENT_SIZE % PAGE_SIZE == 0);
        let mut class_spans = Vec::with_capacity(CLASSES.len());
        for _ in 0..CLASSES.len() {
            class_spans.push([Vec::new(), Vec::new()]);
        }
        let segments = vec![Segment::try_new(SEGMENT_PAGES).unwrap_or_else(|| {
            eprintln!("fatal: out of memory mapping the initial GC segment");
            std::process::abort();
        })];

        // Register the first segment in the arena map.
        let mut arena_map = ArenaMap::default();
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
            page_search_starts: [0; 9],
            arena_map,
            spans: Vec::new(),
            free_span_ids: Vec::new(),
            class_spans,
            span_demand: vec![[0; 2]; CLASSES.len()],
            kept_empty_span_bytes: 0,
            last_marked_objects: 0,
            static_roots: Vec::new(),
            #[cfg(test)]
            manual_roots: Vec::new(),
            persistent_roots: GcPointerMap::default(),
            reclaimers: Vec::new(),
            weak_cells_by_owner: HashMap::new(),
            stats,
            config,
            heap_goal,
            publishes_global_pacing: false,
            scales_heap_goal: false,
            heap_goal_scale: 1,
            last_collection_end: None,
            verify: false,
        }
    }

    #[cfg(test)]
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
    #[cfg(test)]
    fn alloc(&mut self, size: usize, desc: *const GcDesc) -> *mut u8 {
        self.try_alloc::<{ usize::MAX }>(size, desc)
            .expect("GC heap out of memory")
    }

    /// Returns `None` only when the heap cannot grow; `size` must not exceed
    /// `isize::MAX` (`runtime_alloc` rejects larger requests first).
    fn try_alloc<const ZEROED: usize>(
        &mut self,
        size: usize,
        desc: *const GcDesc,
    ) -> Option<*mut u8> {
        // Compute allocation size with alignment and choose the scan lane.
        let payload_size = size;
        let align = desc_alignment(desc).max(std::mem::size_of::<usize>());
        let alloc_size = align_up(payload_size, align);
        let has_pointers = desc_has_pointers(desc);

        // Small allocations go through size-class spans; large ones get whole pages.
        let (ptr, alloc_bytes) = if alloc_size > PAGE_SIZE {
            self.alloc_large::<ZEROED>(payload_size, alloc_size, desc, has_pointers)?
        } else {
            self.alloc_small::<ZEROED>(payload_size, alloc_size, desc, has_pointers)?
        };

        self.after_alloc(alloc_bytes);
        Some(ptr)
    }

    // Allocate from a span that has free slots for this size class.
    fn alloc_small<const ZEROED: usize>(
        &mut self,
        payload_size: usize,
        alloc_size: usize,
        desc: *const GcDesc,
        has_pointers: bool,
    ) -> Option<(*mut u8, usize)> {
        // Pick a size class and scan/noscan lane, then allocate from a span.
        let (class_index, class_size) = small_class(
            alloc_size,
            desc_alignment(desc).max(std::mem::size_of::<usize>()),
        );
        let lane = span_lane(has_pointers);
        let span_id = self.take_span_for_class(class_index, lane)?;
        let span = self.spans[span_id].as_mut().expect("span exists");
        let ptr = span
            .alloc_small::<ZEROED>(payload_size, desc)
            .expect("span has free slot");
        if span.has_free() && !span.in_class_list {
            self.class_spans[class_index][lane].push(span_id);
            span.in_class_list = true;
        }
        Some((ptr, class_size))
    }

    // Large objects: allocate whole pages and track a single live object.
    fn alloc_large<const ZEROED: usize>(
        &mut self,
        payload_size: usize,
        alloc_size: usize,
        desc: *const GcDesc,
        has_pointers: bool,
    ) -> Option<(*mut u8, usize)> {
        // Large allocations use whole pages and get a dedicated span.
        let pages = pages_for_size(alloc_size);
        let (segment, start_page, base) = self.alloc_pages(pages)?;
        let total_bytes = pages.saturating_mul(PAGE_SIZE);
        // Swept and scavenged pages may both be reused. Explicit zeroing is
        // the correctness guarantee rather than an assumption about mapping
        // or kernel state. Sequence buffers clear only their initialized header.
        unsafe { std::ptr::write_bytes(base, 0, ZEROED.min(total_bytes)) };
        let span_id = self.alloc_span_id();
        self.segments[segment].map_span(span_id, start_page, pages);
        let span = Span::new_large(
            base,
            segment,
            start_page,
            pages,
            payload_size,
            desc,
            has_pointers,
        );
        self.spans[span_id] = Some(Box::new(span));
        Some((base, total_bytes))
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

    #[cfg(test)]
    fn alloc_weak_cell(&mut self, target: *const u8) -> *mut u8 {
        let desc = crate::gc_weak::cell_desc();
        let cell = self.alloc(desc.size, desc);
        unsafe { crate::gc_weak::initialize_cell(cell, target) };
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
    fn take_span_for_class(&mut self, class_index: usize, lane: usize) -> Option<usize> {
        self.span_demand[class_index][lane] += 1;
        // Pop spans from the per-class list until a live, reusable span is found.
        let list = &mut self.class_spans[class_index][lane];
        while let Some(span_id) = list.pop() {
            if let Some(span) = self.spans.get_mut(span_id).and_then(|s| s.as_mut()) {
                span.in_class_list = false;
                let span_matches_class = span.class_index == Some(class_index);
                let span_matches_lane = span_lane(span.has_pointers) == lane;
                if span_matches_class && span_matches_lane && !span.checked_out && span.has_free() {
                    return Some(span_id);
                }
            }
        }
        self.new_small_span(class_index, lane)
    }

    fn checkout_span_for_class(&mut self, class_index: usize, lane: usize) -> Option<CachedSpan> {
        let span_id = self.take_span_for_class(class_index, lane)?;
        let span = self.spans[span_id]
            .as_mut()
            .expect("checked-out span exists");
        assert!(!span.checked_out, "span checked out twice");
        span.checked_out = true;
        self.stats.cached_span_refills = self.stats.cached_span_refills.saturating_add(1);
        Some(CachedSpan {
            span_id,
            span: (&**span) as *const Span,
        })
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
    fn new_small_span(&mut self, class_index: usize, lane: usize) -> Option<usize> {
        // Some dense classes use multiple pages to avoid stranding a large
        // fraction of each span's tail. Every page maps to this same span.
        let class_size = CLASSES[class_index].size;
        let pages = CLASSES[class_index].pages;
        let (segment, start_page, base) = self.alloc_pages(pages)?;
        let span_id = self.alloc_span_id();
        self.segments[segment].map_span(span_id, start_page, pages);
        let has_pointers = lane == 0;
        let mut span = Span::new_small(
            base,
            segment,
            start_page,
            pages,
            class_index,
            class_size,
            has_pointers,
        );
        if self.verify {
            unsafe { std::ptr::write_bytes(base, GC_POISON_BYTE, pages * PAGE_SIZE) };
            span.poisoned = true;
        }
        self.spans[span_id] = Some(Box::new(span));
        Some(span_id)
    }

    // Find or create a segment that can satisfy this page request.
    fn alloc_pages(&mut self, pages: usize) -> Option<(usize, usize, *mut u8)> {
        // Segments are the only source of pages; spans are carved from segments.
        let start = self.page_search_starts.get(pages).copied().unwrap_or(0);
        for (index, segment) in self.segments.iter_mut().enumerate().skip(start) {
            if let Some(start_page) = segment.alloc_pages(pages) {
                if let Some(hint) = self.page_search_starts.get_mut(pages) {
                    *hint = index;
                }
                let base = unsafe { segment.data.add(start_page * PAGE_SIZE) };
                return Some((index, start_page, base));
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
        let segment = Segment::try_new(new_pages)?;
        self.segments.push(segment);
        let index = self.segments.len() - 1;
        if let Some(hint) = self.page_search_starts.get_mut(pages) {
            *hint = index;
        }
        register_segment_arenas(&mut self.arena_map, &self.segments[index], index);
        let segment = &mut self.segments[index];
        let start_page = segment.alloc_pages(pages).expect("new segment has space");
        let base = unsafe { segment.data.add(start_page * PAGE_SIZE) };
        Some((index, start_page, base))
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
        // Without a configured limit there is no growth decision to make.
        // Avoid scanning every span on each mutator-cache refill in that case.
        if self.config.memory_limit.is_none() {
            return false;
        }
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
        self.segment_growth_would_cross_soft_limit(CLASSES[class_index].pages)
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
        debug_assert!(
            !self.reclaimers.iter().any(|(owner, _)| *owner == ptr),
            "GC object reclaimer registered twice"
        );
        self.reclaimers.push((ptr, GcReclaimer { callback, data }));
    }

    fn collect(&mut self, threads: &[Arc<ThreadState>]) -> CollectionWork {
        // Stop-the-world collection: gather roots, mark, then sweep.
        let collection_started = Instant::now();
        assert!(
            self.spans.iter().flatten().all(|span| !span.checked_out),
            "collection began while a mutator owned an allocation span"
        );
        let phase_started = Instant::now();
        #[cfg(test)]
        let mut roots = std::mem::take(&mut self.manual_roots);
        #[cfg(not(test))]
        let mut roots = Vec::new();
        let static_roots = std::mem::take(&mut self.static_roots);
        roots.extend(self.persistent_roots.keys().copied());
        root_slots::for_each_root(|root| roots.push(root));
        self.mark_roots(roots.into_iter(), &static_roots, threads);
        if self.verify {
            self.verify_marked_edges(&static_roots);
        }
        self.static_roots = static_roots;
        add_elapsed(&mut self.stats.phases.mark_ns, phase_started.elapsed());
        let phase_started = Instant::now();
        self.process_weak_cells();
        add_elapsed(&mut self.stats.phases.weak_ns, phase_started.elapsed());
        let phase_started = Instant::now();
        let (freed, reclaimers) = self.sweep();
        add_elapsed(&mut self.stats.phases.sweep_ns, phase_started.elapsed());
        self.update_heap_goal_scale(collection_started.elapsed(), Instant::now());
        let phase_started = Instant::now();
        let released_bytes = self.release_empty_segments();
        let scavenged_bytes = self.scavenge_free_pages();
        add_elapsed(&mut self.stats.phases.scavenge_ns, phase_started.elapsed());
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
        self.heap_goal =
            scaled_heap_goal(self.stats.live_bytes, self.config, self.heap_goal_scale);
        self.stats.heap_goal = self.heap_goal;
        self.stats.configured_memory_limit = self.config.memory_limit;
        if self.publishes_global_pacing {
            self.publish_global_pacing_state();
        }
        self.refresh_gc_needed();
        CollectionWork { reclaimers }
    }

    fn update_heap_goal_scale(&mut self, collecting: Duration, now: Instant) {
        if !self.scales_heap_goal {
            return;
        }
        if let Some(previous) = self.last_collection_end {
            let interval = now.saturating_duration_since(previous);
            if collecting * GC_LARGER_HEAP_RATIO > interval {
                self.heap_goal_scale = (self.heap_goal_scale * 2).min(GC_MAX_HEAP_SCALE);
            } else if collecting * GC_SMALLER_HEAP_RATIO < interval {
                self.heap_goal_scale = (self.heap_goal_scale / 2).max(1);
            }
        }
        self.last_collection_end = Some(now);
    }

    fn record_pause(&mut self, pause: Duration) {
        self.stats.record_pause(pause);
    }

    fn mark_roots<I>(&mut self, roots: I, static_roots: &[StaticRoot], threads: &[Arc<ThreadState>])
    where
        I: IntoIterator<Item = *const u8>,
    {
        // Pre-allocate the mark stack to avoid reallocations during tracing.
        // 1024 pointers handles most workloads; deep graphs will still grow.
        const INITIAL_STACK_CAPACITY: usize = 1024;
        let mut stack: MarkStack = Vec::with_capacity(INITIAL_STACK_CAPACITY);
        stack.extend(roots);

        for root in static_roots {
            let Some(desc) = (unsafe { root.desc.as_ref() }) else {
                continue;
            };
            trace_desc_or_abort(desc, root.start, desc.size, TraceMode::Heap, |candidate| {
                stack.push(candidate)
            });
        }

        self.push_published_roots(&mut stack, threads);
        let mark_threads = self.config.mark_threads.unwrap_or_else(|| {
            parallel_mark::thread_count(self.last_marked_objects, threads.len())
        });
        self.last_marked_objects = if mark_threads > 1 {
            parallel_mark::mark(self, stack, mark_threads)
                .unwrap_or_else(|mut stack| self.trace_stack(&mut stack))
        } else {
            self.trace_stack(&mut stack)
        };
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
                    crate::gc_weak::clear_cell(cell);
                }
            }
            if !retained.is_empty() {
                self.weak_cells_by_owner.insert(owner, retained);
            }
        }
    }

    /// Mark everything reachable from `stack`, returning how many objects that was.
    fn trace_stack(&self, stack: &mut MarkStack) -> usize {
        // Iterative DFS to avoid recursion in the mark phase.
        // Large pointer-free buffers often have many interior edges (string
        // slices, for example). Once marked they cannot reveal more children.
        // The range is local to this stopped-world walk: sweep may reclaim or
        // reuse its address before the next collection.
        let mut marked = 0;
        let mut marked_leaf = 0..0;
        while let Some(ptr) = stack.pop() {
            if marked_leaf.contains(&(ptr as usize)) {
                continue;
            }
            marked += usize::from(self.mark_ptr::<false>(ptr, stack, &mut marked_leaf));
        }
        marked
    }

    // Use the page map to resolve an interior pointer to its span + slot. Returns
    // whether this call was the one to mark the object. `SHARED` says whether other
    // threads are marking too; if not, setting a mark bit needs no atomic update.
    #[inline]
    fn mark_ptr<const SHARED: bool>(
        &self,
        ptr: *const u8,
        stack: &mut MarkStack,
        marked_leaf: &mut std::ops::Range<usize>,
    ) -> bool {
        // Resolve the pointer to a span slot and mark it live.
        if ptr.is_null() {
            return false;
        }
        let (span_id, object_index) = match self.find_object(ptr) {
            Some(hit) => hit,
            None => return false,
        };
        let Some(span) = self.spans.get(span_id).and_then(|s| s.as_ref()) else {
            return false;
        };
        if !atomic_bitset_get(&span.alloc_map, object_index, Ordering::Acquire) {
            return false;
        }
        let word = &span.mark_map[object_index / 64];
        let mask = 1_u64 << (object_index % 64);
        let marks = word.load(Ordering::Relaxed);
        let was_marked = if marks & mask != 0 {
            true
        } else if SHARED {
            word.fetch_or(mask, Ordering::Relaxed) & mask != 0
        } else {
            word.store(marks | mask, Ordering::Relaxed);
            false
        };
        if !span.has_pointers {
            // A large span owns exactly one allocation, including its rounded
            // tail. Small spans contain independent cells and cannot be cached
            // as a whole. Mark bits remain set throughout this walk.
            if span.class_index.is_none() {
                let start = span.base as usize;
                if let Some(end) = start.checked_add(span.object_size) {
                    *marked_leaf = start..end;
                }
            }
            return !was_marked;
        }
        if was_marked {
            return false;
        }
        let desc = span.descs[object_index].load(Ordering::Relaxed);
        let desc = unsafe { desc.as_ref() };
        let Some(desc) = desc else {
            return true;
        };
        if desc.node_count == 0 {
            return true;
        }

        let payload_size = span.sizes[object_index].load(Ordering::Relaxed);
        let base = unsafe { span.base.add(object_index * span.object_size) };
        self.push_pointer_fields(base, payload_size, desc, stack, marked_leaf);
        true
    }

    fn push_pointer_fields(
        &self,
        base: *mut u8,
        limit: usize,
        desc: &GcDesc,
        stack: &mut Vec<*const u8>,
        marked_leaf: &std::ops::Range<usize>,
    ) {
        trace_desc_or_abort(desc, base, limit, TraceMode::Heap, |candidate| {
            if !marked_leaf.contains(&(candidate as usize)) {
                stack.push(candidate);
            }
        });
    }

    fn push_published_roots(&self, stack: &mut Vec<*const u8>, threads: &[Arc<ThreadState>]) {
        for thread in threads {
            // The collector either observed this thread parked with Acquire,
            // or is reading its own buffer after synchronously publishing it.
            let roots = unsafe { &*thread.published_roots.get() };
            stack.extend(roots.iter().copied().filter(|root| !root.is_null()));
            let sp = thread.blocking_sp.load(Ordering::Relaxed);
            if sp != 0 {
                push_conservative_stack(stack, sp, thread.stack_top);
            }
        }
    }

    // Sweep spans: free unmarked slots, and return empty spans to the segment.
    fn sweep(&mut self) -> (SweepStats, Vec<GcReclaimer>) {
        // Sweep spans: free unmarked slots, return empty spans to segments.
        let mut freed = SweepStats::default();
        let mut reclaimers = Vec::new();
        // Only registered owners need native cleanup. Inspect that sparse set
        // while every span's mark bits are intact, before sweeping clears or
        // releases any of them. Callbacks still run after the world restarts.
        let mut registered = std::mem::take(&mut self.reclaimers);
        registered.retain(|(owner, reclaimer)| {
            if self.object_is_marked(*owner) {
                true
            } else {
                reclaimers.push(*reclaimer);
                false
            }
        });
        self.reclaimers = registered;
        self.kept_empty_span_bytes = 0;
        for span_id in 0..self.spans.len() {
            let Some(mut span) = self.spans[span_id].take() else {
                continue;
            };

            // Large span: single slot at index 0.
            if span.class_index.is_none() {
                // If the lone object is unmarked, free the entire span.
                if atomic_bitset_get(&span.alloc_map, 0, Ordering::Acquire)
                    && !atomic_bitset_get(&span.mark_map, 0, Ordering::Relaxed)
                {
                    let total_bytes = span.page_count.saturating_mul(PAGE_SIZE);
                    atomic_bitset_set(&span.alloc_map, 0, false, Ordering::Release);
                    if span.has_pointers && !span.descs.is_empty() {
                        span.descs[0].store(std::ptr::null_mut(), Ordering::Relaxed);
                        span.sizes[0].store(0, Ordering::Relaxed);
                    }
                    span.allocated.store(0, Ordering::Relaxed);
                    self.poison_dead_span(&span);
                    self.stats.record_free(total_bytes);
                    freed.objects += 1;
                    freed.bytes = freed.bytes.saturating_add(total_bytes);
                    self.free_span_pages(&span);
                    self.free_span_id(span_id);
                    continue;
                }
                *span.mark_map[0].get_mut() = 0;
                self.spans[span_id] = Some(span);
                continue;
            }

            // Weak cells have already been processed, native cleanup extracted, and
            // all mutator caches returned before marking, so nothing still needs
            // what an entirely dead span held.
            if span
                .mark_map
                .iter()
                .all(|word| word.load(Ordering::Relaxed) == 0)
            {
                let objects = span.allocated.load(Ordering::Relaxed);
                let bytes = objects.saturating_mul(span.object_size);
                self.poison_dead_span(&span);
                self.stats.record_frees(objects, bytes);
                freed.objects += objects;
                freed.bytes = freed.bytes.saturating_add(bytes);
                let class_index = span.class_index.expect("small span has a size class");
                let demand = &mut self.span_demand[class_index][span_lane(span.has_pointers)];
                let span_bytes = span.page_count.saturating_mul(PAGE_SIZE);
                // Building a span costs more than resetting one. Allocation at the
                // same rate wants about as many again, so keep that many, within
                // the warm memory scavenging would otherwise have kept. Under a
                // memory limit, free pages must stay available to every class.
                if *demand == 0
                    || self.config.memory_limit.is_some()
                    || self.kept_empty_span_bytes + span_bytes
                        > GC_MIN_TRIGGER * self.heap_goal_scale
                {
                    self.free_span_pages(&span);
                    self.free_span_id(span_id);
                    continue;
                }
                *demand -= 1;
                span.reset_empty();
                span.poisoned |= self.verify;
                self.kept_empty_span_bytes += span_bytes;
            } else {
                let slots = span.sweep_slots();
                let bytes = slots.saturating_mul(span.object_size);
                self.stats.record_frees(slots, bytes);
                freed.objects += slots;
                freed.bytes = freed.bytes.saturating_add(bytes);
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
        self.span_demand.fill([0; 2]);
        (freed, reclaimers)
    }

    /// Poison a dead span's pages until they are reused or scavenged, so a
    /// missed root reads a recognizable pattern rather than stale values.
    fn poison_dead_span(&self, span: &Span) {
        if self.verify {
            let bytes = span.page_count.saturating_mul(PAGE_SIZE);
            unsafe { std::ptr::write_bytes(span.base, GC_POISON_BYTE, bytes) };
        }
    }

    /// Whether `ptr` lands in heap pages that hold no allocated object.
    fn points_to_freed_storage(&self, ptr: *const u8) -> bool {
        let Some(segment_index) = self.segment_index_for_ptr(ptr) else {
            return false;
        };
        let segment = &self.segments[segment_index];
        let page = (ptr as usize).saturating_sub(segment.base()) / PAGE_SIZE;
        let Some(&span_id) = segment.page_map.get(page) else {
            return false;
        };
        if span_id == SPAN_NONE {
            return true;
        }
        match self.find_object(ptr) {
            Some((span_id, index)) => self.spans[span_id]
                .as_ref()
                .is_some_and(|span| !atomic_bitset_get(&span.alloc_map, index, Ordering::Acquire)),
            // Slack past a small span's last slot is never an object.
            None => true,
        }
    }

    /// After marking, check every managed edge of static roots and marked
    /// objects. An edge into freed storage means an earlier collection
    /// missed a root or a traced field. Raw pointers are exempt: unsafe code
    /// may keep them dangling or one past their object.
    fn verify_marked_edges(&self, static_roots: &[StaticRoot]) {
        let check = |owner: *const u8, desc: *const GcDesc, candidate: *const u8| {
            if self.points_to_freed_storage(candidate) {
                eprintln!(
                    "fatal: GC heap verification: {owner:p} (descriptor {desc:p}) references freed storage {candidate:p}"
                );
                std::process::abort();
            }
        };
        let trace = |owner: *const u8, base: *const u8, limit: usize, desc: &GcDesc| {
            let nodes = desc_nodes(desc);
            if let Err(error) =
                unsafe { trace_managed_edges(base, nodes, limit, |c| check(owner, desc, c)) }
            {
                eprintln!(
                    "fatal: invalid live GC value for descriptor {desc:p} at {base:p}: {error}"
                );
                std::process::abort();
            }
        };
        for root in static_roots {
            if let Some(desc) = unsafe { root.desc.as_ref() } {
                trace(root.start, root.start, desc.size, desc);
            }
        }
        for span in self.spans.iter().flatten() {
            if !span.has_pointers {
                continue;
            }
            for index in 0..span.object_count {
                if !atomic_bitset_get(&span.alloc_map, index, Ordering::Acquire)
                    || !atomic_bitset_get(&span.mark_map, index, Ordering::Relaxed)
                {
                    continue;
                }
                let desc = span.descs[index].load(Ordering::Relaxed);
                let Some(desc) = (unsafe { desc.as_ref() }) else {
                    continue;
                };
                if desc.node_count == 0 {
                    continue;
                }
                let base = unsafe { span.base.add(index * span.object_size) };
                let payload = span.sizes[index].load(Ordering::Relaxed);
                trace(base, base, payload, desc);
            }
        }
    }

    // Return an entire span's pages to its owning segment.
    fn free_span_pages(&mut self, span: &Span) {
        // Release the span's pages back to its owning segment.
        let segment = &mut self.segments[span.segment];
        segment.unmap_span(span.start_page, span.page_count);
        segment.free_pages(span.start_page, span.page_count);
        self.page_search_starts.fill(0);
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
            && atomic_bitset_get(&span.mark_map, object_index, Ordering::Relaxed)
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
            self.page_search_starts.fill(0);
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
        // Avoid faulting the same pages back in during the next allocation
        // cycle. Bound warm free storage by both the next cycle's headroom
        // and the minimum heap goal, independent of the heap's historical peak. A
        // configured memory limit further reduces this budget; at pressure
        // we scavenge every eligible page as before. Empty segments are still
        // released before this step. Allocation clears all scanner-visible data.
        let mut retain_bytes =
            scaled_heap_goal(self.stats.live_bytes, self.config, self.heap_goal_scale)
                .saturating_sub(self.stats.live_bytes)
                .min(GC_MIN_TRIGGER * self.heap_goal_scale)
                .saturating_sub(self.kept_empty_span_bytes);
        if let Some(limit) = self.config.memory_limit {
            retain_bytes = retain_bytes.min(limit.saturating_sub(self.segment_bytes()));
        }
        self.segments
            .iter_mut()
            .map(|segment| segment.scavenge_free_runs(&mut retain_bytes))
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
    let desc = crate::gc_weak::cell_desc();
    let cell = runtime_alloc::<{ usize::MAX }>(desc.size, desc);
    unsafe { crate::gc_weak::initialize_cell(cell, target) };
    with_gc(|gc| gc.register_weak_cell(cell, target));
    cell
}

/// Internal candidate test hooks exercise the compiler's actual poll slow path
/// without relying on allocation volume or pacing timing.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__test_request_collection() -> usize {
    let before = stats_snapshot().collections;
    GC_POLL_FLAGS.fetch_or(GC_NEEDED_FLAG, Ordering::Release);
    before
}

#[unsafe(no_mangle)]
pub extern "C" fn __gc__test_collection_count() -> usize {
    stats_snapshot().collections
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

/// Zero a small cell with inline stores. Most allocations are a few words, for
/// which a call into `memset` is a measurable part of allocating. The stores are
/// deliberately branchy rather than a loop, which the compiler would turn back
/// into that call.
///
/// # Safety
/// `cell` is valid for `size` bytes and aligned to a word.
#[inline(always)]
unsafe fn clear_cell(cell: *mut u8, size: usize) {
    const INLINE_LIMIT: usize = 256;
    const WORD: usize = size_of::<u64>();
    if size >= INLINE_LIMIT || !size.is_multiple_of(WORD) {
        unsafe { std::ptr::write_bytes(cell, 0, size) };
        return;
    }
    let mut next = cell;
    unsafe {
        if size & WORD != 0 {
            next.cast::<u64>().write(0);
            next = next.add(WORD);
        }
        if size & (2 * WORD) != 0 {
            next.cast::<[u64; 2]>().write([0; 2]);
            next = next.add(2 * WORD);
        }
        if size & (4 * WORD) != 0 {
            next.cast::<[u64; 4]>().write([0; 4]);
            next = next.add(4 * WORD);
        }
        if size & (8 * WORD) != 0 {
            next.cast::<[u64; 8]>().write([0; 8]);
            next = next.add(8 * WORD);
        }
        if size & (16 * WORD) != 0 {
            next.cast::<[u64; 16]>().write([0; 16]);
        }
    }
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

fn align_up(n: usize, align: usize) -> usize {
    // Align n upward to the next multiple of align.
    debug_assert!(align.is_power_of_two(), "alignment must be a power of two");
    (n + (align - 1)) & !(align - 1)
}

fn next_heap_goal(live_bytes: usize, config: GcConfig) -> usize {
    scaled_heap_goal(live_bytes, config, 1)
}

fn scaled_heap_goal(live_bytes: usize, config: GcConfig, scale: usize) -> usize {
    let Some(percent) = config.percent else {
        return usize::MAX;
    };
    let growth = (live_bytes as u128)
        .saturating_mul(u128::from(percent))
        .saturating_mul(scale as u128)
        .saturating_div(100)
        .min(usize::MAX as u128) as usize;
    // Even zero-percent pacing needs fresh allocation pressure after a
    // completed collection. Otherwise a nonallocating loop can repeatedly win
    // the collector CAS before a notified peer resumes (as forced stress does).
    let goal = (GC_MIN_TRIGGER * scale)
        .max(live_bytes.saturating_add(growth))
        .max(live_bytes.saturating_add(1));
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
fn register_segment_arenas(arena_map: &mut ArenaMap, segment: &Segment, index: usize) {
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
    #[test]
    fn clear_cell_zeroes_exactly_the_requested_bytes() {
        const WORDS: usize = 48;
        for size in (0..=WORDS * 8).step_by(4) {
            let mut storage = [u64::MAX; WORDS];
            unsafe { clear_cell(storage.as_mut_ptr().cast(), size) };
            let bytes =
                unsafe { std::slice::from_raw_parts(storage.as_ptr().cast::<u8>(), WORDS * 8) };
            assert!(bytes[..size].iter().all(|byte| *byte == 0), "{size}");
            assert!(bytes[size..].iter().all(|byte| *byte == u8::MAX), "{size}");
        }
    }

    fn model_resume_rendezvous(fence: Option<std::sync::atomic::Ordering>) {
        loom::model(move || {
            use loom::sync::{
                Arc,
                atomic::{AtomicBool, AtomicU8, Ordering},
            };
            let parked = Arc::new(AtomicBool::new(true));
            let requested = Arc::new(AtomicU8::new(0));
            let resumes = Arc::new(AtomicBool::new(false));
            let collects = Arc::new(AtomicBool::new(false));
            let mutator = {
                let parked = parked.clone();
                let requested = requested.clone();
                let resumes = resumes.clone();
                loom::thread::spawn(move || {
                    parked.store(false, Ordering::Release);
                    if let Some(fence) = fence {
                        loom::sync::atomic::fence(fence);
                    }
                    if requested.load(Ordering::Acquire) & super::GC_REQUESTED_FLAG == 0 {
                        resumes.store(true, Ordering::Relaxed);
                    }
                })
            };
            let collector = {
                let parked = parked.clone();
                let requested = requested.clone();
                let collects = collects.clone();
                loom::thread::spawn(move || {
                    requested.fetch_or(super::GC_REQUESTED_FLAG, Ordering::AcqRel);
                    if let Some(fence) = fence {
                        loom::sync::atomic::fence(fence);
                    }
                    if parked.load(Ordering::Acquire) {
                        collects.store(true, Ordering::Relaxed);
                    }
                })
            };
            mutator.join().unwrap();
            collector.join().unwrap();
            assert!(
                !(resumes.load(Ordering::Relaxed) && collects.load(Ordering::Relaxed)),
                "collector and mutator both proceeded"
            );
        });
    }

    #[test]
    fn resume_rendezvous_orders_both_publications() {
        model_resume_rendezvous(Some(super::RENDEZVOUS_FENCE));
    }

    #[test]
    #[should_panic(expected = "collector and mutator both proceeded")]
    fn model_exposes_the_previous_acquire_release_rendezvous_race() {
        model_resume_rendezvous(None);
    }

    #[test]
    fn root_capture_tolerates_thread_local_teardown() {
        struct CaptureOnExit;
        impl Drop for CaptureOnExit {
            fn drop(&mut self) {
                assert!(super::capture_current_roots().is_empty());
            }
        }
        thread_local! {
            static CAPTURE_ON_EXIT: CaptureOnExit = const { CaptureOnExit };
        }
        std::thread::spawn(|| {
            // A mutator can unregister after test-only root storage has been
            // destroyed. Reproduce that ordering without racing a collector.
            CAPTURE_ON_EXIT.with(|_| {});
            super::TEST_ROOTS.with(|roots| assert!(roots.borrow().is_empty()));
        })
        .join()
        .unwrap();
    }

    use super::*;
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

    fn pointer_array_nodes(count: usize) -> [GcLayoutNode; 2] {
        [
            GcLayoutNode {
                stride: std::mem::size_of::<*mut u8>() as u64,
                first_child: 1,
                child_count: count.try_into().unwrap(),
                kind: crate::gc_layout::GC_LAYOUT_REPEAT,
                ..POINTER_NODES[0]
            },
            POINTER_NODES[0],
        ]
    }

    #[test]
    fn dense_small_allocations_charge_the_selected_class() {
        for (request, expected) in [(24, 24), (40, 48), (408, 416), (1200, 1280), (5000, 5376)] {
            let mut gc = Gc::new_with_config(GcConfig::default());
            let desc = bytes_desc(request);
            let value = gc.alloc(request, &desc);
            let (span, _) = gc.find_object(value).unwrap();
            assert_eq!(
                gc.spans[span].as_ref().unwrap().object_size,
                expected,
                "request {request}"
            );
            assert_eq!(gc.stats.total_allocated_bytes, expected);
        }
    }

    #[test]
    fn dense_spans_trace_interior_roots_and_reject_tail_padding() {
        for class in CLASSES {
            for scan in [false, true] {
                let mut gc = Gc::new_with_config(GcConfig::default());
                let child_desc = bytes_desc(8);
                let child = gc.alloc(8, &child_desc);
                let desc = if scan {
                    GcDesc {
                        size: class.size,
                        ..pointer_desc()
                    }
                } else {
                    bytes_desc(class.size)
                };
                let count = class.pages * PAGE_SIZE / class.size;
                let values: Vec<_> = (0..count + 1)
                    .map(|_| gc.alloc(class.size, &desc))
                    .collect();
                if scan {
                    unsafe { values[0].cast::<*mut u8>().write(child) };
                }
                let (span_id, _) = gc.find_object(values[0]).unwrap();
                let span = gc.spans[span_id].as_ref().unwrap();
                assert_eq!(span.page_count, class.pages);
                let tail = span.object_count * class.size;
                if tail < span.page_count * PAGE_SIZE {
                    let padding = unsafe { span.base.add(tail) };
                    assert!(
                        gc.find_object(padding).is_none(),
                        "class {} tail",
                        class.size
                    );
                }
                if class.pages > 1 {
                    let second_page = unsafe { span.base.add(PAGE_SIZE + 1) };
                    assert_eq!(gc.find_object(second_page).unwrap().0, span_id);
                }
                let interior = unsafe { values[0].add(class.size - 1) };
                gc.add_root(interior);
                gc.add_root(*values.last().unwrap());
                gc.collect(&[]);
                assert!(is_live(&gc, interior), "class {} interior", class.size);
                assert!(is_live(&gc, *values.last().unwrap()));
                if scan {
                    assert!(is_live(&gc, child));
                }
                gc.collect(&[]);
                assert!(!is_live(&gc, interior));
                assert_eq!(gc.stats.live_bytes, 0);
            }
        }
    }

    #[test]
    fn dense_slots_preserve_explicit_overalignment() {
        for (size, alignment) in [(2560, 512), (3328, 256), (5120, 1024)] {
            let mut gc = Gc::new_with_config(GcConfig::default());
            let desc = GcDesc {
                align: alignment,
                ..bytes_desc(size)
            };
            for _ in 0..16 {
                let value = gc.alloc(size, &desc);
                assert_eq!(value as usize % alignment, 0);
                gc.add_root(value);
            }
            gc.collect(&[]);
            assert_eq!(gc.stats.live_objects, 16);
        }
    }

    #[test]
    fn dense_span_refill_checks_its_full_page_requirement() {
        let mut gc = Gc::new_with_config(GcConfig {
            percent: None,
            memory_limit: Some(SEGMENT_SIZE),
            mark_threads: None,
        });
        let bytes = SEGMENT_SIZE - PAGE_SIZE;
        gc.alloc(bytes, &bytes_desc(bytes));
        // One page remains, but the 1408-byte class needs a two-page span.
        let (index, _) = small_class(1408, 8);
        assert!(gc.checkout_would_cross_soft_limit(index, 0));
    }

    #[test]
    fn zero_size_and_overaligned_allocations_have_valid_storage() {
        let mut gc = Gc::new();
        let empty = bytes_desc(0);
        let empty_value = gc.alloc(0, &empty);
        assert!(!empty_value.is_null());
        let aligned = GcDesc {
            size: 64,
            align: 64,
            nodes: std::ptr::null(),
            node_count: 0,
        };
        let value = gc.alloc(64, &aligned);
        assert_eq!(value as usize % aligned.align, 0);
        gc.add_root(empty_value);
        gc.add_root(value);
        gc.collect(&[]);
        assert!(is_live(&gc, empty_value));
        assert!(is_live(&gc, value));
    }

    #[test]
    fn cycles_are_retained_by_interior_roots_and_collected_when_unreachable() {
        let mut gc = Gc::new();
        let desc = pointer_desc();
        let first = gc.alloc(desc.size, &desc);
        let second = gc.alloc(desc.size, &desc);
        unsafe {
            first.cast::<*mut u8>().write(second);
            second.cast::<*mut u8>().write(first);
        }
        gc.add_root(unsafe { first.add(1) });
        gc.collect(&[]);
        assert!(is_live(&gc, first));
        assert!(is_live(&gc, second));
        gc.collect(&[]);
        assert!(!is_live(&gc, first));
        assert!(!is_live(&gc, second));
    }

    #[test]
    fn class_cycles_trace_fields_and_survive_interior_roots_without_finalization() {
        use crate::class_metadata::ClassDescriptor;
        use crate::gc_classes::{__gc__class_initialize, __gc__class_is_a};
        #[repr(C)]
        struct Object {
            metadata: *const ClassDescriptor,
            next: *mut Object,
            value: usize,
        }
        static BASE_ID: u8 = 10;
        static CHILD_ID: u8 = 11;
        static BASE: ClassDescriptor = ClassDescriptor {
            identity: &BASE_ID,
            base: std::ptr::null(),
            methods: std::ptr::null(),
            method_count: 0,
        };
        static CHILD: ClassDescriptor = ClassDescriptor {
            identity: &CHILD_ID,
            base: &BASE,
            methods: std::ptr::null(),
            method_count: 0,
        };
        let nodes = [GcLayoutNode {
            offset: std::mem::offset_of!(Object, next) as u64,
            stride: 0,
            first_child: 0,
            child_count: 0,
            kind: GC_LAYOUT_POINTER,
            width: 0,
            reserved: [0; 6],
        }];
        let desc = GcDesc {
            size: std::mem::size_of::<Object>(),
            align: std::mem::align_of::<Object>(),
            nodes: nodes.as_ptr(),
            node_count: nodes.len(),
        };
        let mut gc = Gc::new();
        let first = gc.alloc(desc.size, &desc).cast::<Object>();
        let second = gc.alloc(desc.size, &desc).cast::<Object>();
        unsafe {
            __gc__class_initialize(first.cast(), &CHILD);
            __gc__class_initialize(second.cast(), &BASE);
            (*first).next = second;
            (*second).next = first;
            (*first).value = 42;
            // A field address retains the complete object and its cycle.
            gc.add_root(std::ptr::addr_of!((*first).value).cast());
        }
        gc.collect(&[]);
        assert!(is_live(&gc, first.cast()));
        assert!(is_live(&gc, second.cast()));
        unsafe {
            assert_eq!((*first).value, 42);
            assert!(__gc__class_is_a(first.cast(), &BASE_ID));
            assert!(__gc__class_is_a(first.cast(), &CHILD_ID));
        }
        // Once the field root disappears, cyclic class handles do not keep
        // themselves alive and no language cleanup is invoked by collection.
        let work = gc.collect(&[]);
        assert!(work.is_empty());
        assert!(!is_live(&gc, first.cast()));
        assert!(!is_live(&gc, second.cast()));
    }

    fn count_finalization(data: usize) {
        let count = unsafe { &*(data as *const AtomicUsize) };
        count.fetch_add(1, Ordering::AcqRel);
    }

    #[test]
    fn cumulative_pause_time_survives_sample_eviction() {
        let mut stats = GcStats::default();
        for collection in 1..=MAX_GC_PAUSE_SAMPLES + 3 {
            stats.collections = collection;
            stats.record_pause(Duration::from_nanos(7));
        }
        let snapshot = stats.snapshot();
        assert_eq!(snapshot.pause_nanos_since(0).len(), MAX_GC_PAUSE_SAMPLES);
        assert_eq!(
            snapshot.total_pause_ns,
            (MAX_GC_PAUSE_SAMPLES as u64 + 3) * 7
        );
        stats.total_pause_ns = u64::MAX - 1;
        stats.record_pause(Duration::from_nanos(7));
        assert_eq!(stats.snapshot().total_pause_ns, u64::MAX);
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

        assert_eq!(parse_gc_mark_threads("1"), Ok(1));
        assert_eq!(parse_gc_mark_threads(" 8 "), Ok(8));
        assert!(parse_gc_mark_threads("0").is_err());
        assert!(parse_gc_mark_threads("257").is_err());
        assert!(parse_gc_mark_threads("many").is_err());
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
        assert_eq!(next_heap_goal(0, GcConfig::default()), 4 << 20);
        assert_eq!(next_heap_goal(0, GcConfig::default()), GC_MIN_TRIGGER);
        assert_eq!(next_heap_goal(8 << 20, GcConfig::default()), 16 << 20);
        assert_eq!(
            next_heap_goal(
                8 << 20,
                GcConfig {
                    percent: Some(25),
                    memory_limit: Some(9 << 20),
                    mark_threads: None,
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
                    mark_threads: None,
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
                    mark_threads: None,
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
                    mark_threads: None,
                },
            ),
            16 << 20
        );
        assert_eq!(
            next_heap_goal(
                9 << 20,
                GcConfig {
                    percent: Some(100),
                    memory_limit: Some(9 << 20),
                    mark_threads: None,
                },
            ),
            (9 << 20) + 1
        );
    }

    #[test]
    fn soft_limit_refill_distinguishes_owned_and_reusable_spans() {
        let mut gc = Gc::new_with_config(GcConfig {
            percent: None,
            memory_limit: Some(SEGMENT_SIZE),
            mark_threads: None,
        });
        let cached = gc.checkout_span_for_class(0, 0).unwrap();
        let tail_size = SEGMENT_SIZE - PAGE_SIZE;
        let tail_desc = bytes_desc(tail_size);
        gc.alloc(tail_size, &tail_desc);
        assert_eq!(gc.segments.len(), 1);

        // The checked-out span has free cells, but another refill cannot use
        // them. With the segment full, a new span would exceed the limit.
        assert!(gc.checkout_would_cross_soft_limit(0, 0));
        gc.return_checked_out_span(cached.span_id);
        assert!(!gc.checkout_would_cross_soft_limit(0, 0));

        let cached = gc.checkout_span_for_class(0, 0).unwrap();
        gc.config.memory_limit = None;
        assert!(!gc.checkout_would_cross_soft_limit(0, 0));
        gc.return_checked_out_span(cached.span_id);
    }

    #[test]
    fn consumed_free_runs_keep_neighbor_coalescing_available() {
        let mut segment = Segment::test_fake(0x20_0000, 8 * PAGE_SIZE);
        assert_eq!(segment.alloc_pages(8), Some(0));
        for page in [0, 2, 4, 6] {
            segment.free_pages(page, 1);
        }
        assert_eq!(segment.alloc_pages(1), Some(0));
        // Returning page one must merge it with free page two, even after
        // consuming an earlier run from a list with several later entries.
        segment.free_pages(1, 1);
        assert_eq!(segment.alloc_pages(2), Some(1));
        segment.free_pages(3, 1);
        segment.free_pages(5, 1);
        assert_eq!(segment.alloc_pages(4), Some(3));
    }

    #[test]
    fn page_search_hints_preserve_first_fit_across_sizes_frees_and_segment_removal() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        gc.verify = true;
        let desc = bytes_desc(8 * PAGE_SIZE);
        let mut keepers = Vec::new();
        for _ in 0..SEGMENT_PAGES / 8 - 1 {
            keepers.push(gc.alloc(8 * PAGE_SIZE, &desc));
        }
        let first = keepers[0];
        let seven = gc.alloc(7 * PAGE_SIZE, &desc);
        keepers.push(seven);
        let later = gc.alloc(8 * PAGE_SIZE, &desc);
        assert_eq!(gc.segments.len(), 2);
        // An eight-page miss must not hide the earlier segment's final page.
        let one = gc.alloc(PAGE_SIZE, &desc);
        let (id, _) = gc.find_object(one).unwrap();
        assert_eq!(gc.spans[id].as_ref().unwrap().segment, 0);
        keepers.push(one);
        for pointer in keepers.iter().skip(1).copied().chain([later]) {
            gc.add_root(pointer);
        }
        assert!(gc.collect(&[]).is_empty());
        let reused = gc.alloc(8 * PAGE_SIZE, &desc);
        assert_eq!(
            reused, first,
            "freed earlier runs remain first-fit candidates"
        );
        // Removing segment zero shifts the survivor's index. Hints must not
        // retain its old index or cause an unnecessary third mapping.
        gc.add_root(later);
        assert!(gc.collect(&[]).is_empty());
        assert_eq!(gc.segments.len(), 1);
        let next = gc.alloc(8 * PAGE_SIZE, &desc);
        let (id, _) = gc.find_object(next).unwrap();
        assert_eq!(gc.spans[id].as_ref().unwrap().segment, 0);
        assert_eq!(gc.segments.len(), 1);
    }

    #[test]
    fn repeated_large_leaf_interiors_do_not_hide_neighbors_or_survive_the_next_walk() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        gc.verify = true;
        let bytes = 16 * 1024;
        let leaf_desc = bytes_desc(bytes);
        let source = gc.alloc(bytes, &leaf_desc);
        let other_source = gc.alloc(bytes, &leaf_desc);
        let weak = gc.alloc_weak_cell(unsafe { source.add(3) });
        let child_desc = bytes_desc(8);
        let child = gc.alloc(8, &child_desc);
        let parent_desc = GcDesc {
            size: bytes,
            ..pointer_desc()
        };
        let parent = gc.alloc(bytes, &parent_desc);
        unsafe { parent.cast::<*mut u8>().write(child) };
        // DFS reaches the pointer-bearing neighbor after repeated interior
        // leaves, including the final byte at each cached range boundary.
        gc.add_root(parent);
        gc.add_root(weak);
        for source in [source, other_source, source] {
            for offset in [0, 1, bytes / 2, bytes - 1] {
                gc.add_root(unsafe { source.add(offset) });
            }
        }
        assert!(gc.collect(&[]).is_empty());
        for pointer in [source, other_source, parent, child] {
            assert!(
                gc.find_object(pointer).is_some(),
                "every reachable allocation survives"
            );
        }
        assert!(!crate::gc_weak::load_cell(weak).is_null());
        gc.add_root(weak);
        assert!(gc.collect(&[]).is_empty());
        assert!(crate::gc_weak::load_cell(weak).is_null());
        for pointer in [source, other_source, parent, child] {
            assert!(
                !gc.find_object(pointer).is_some_and(|(id, slot)| {
                    atomic_bitset_get(
                        &gc.spans[id].as_ref().unwrap().alloc_map,
                        slot,
                        Ordering::Acquire,
                    )
                }),
                "no cached range outlives its mark walk"
            );
        }
    }

    #[test]
    fn reused_small_slots_are_zero_before_publication() {
        for size in [1_usize, 8, 9, 16, 24, 32, 40, 408] {
            let mut gc = Gc::new_with_config(GcConfig::default());
            let desc = bytes_desc(size);
            let slot_size = small_class(size, 8).1;
            let stale = gc.alloc(size, &desc);
            let keeper = gc.alloc(size, &desc);
            unsafe { std::ptr::write_bytes(stale, 0xa5, slot_size) };
            gc.add_root(keeper);
            assert!(gc.collect(&[]).is_empty());

            let reused = gc.alloc(size, &desc);
            assert_eq!(reused, stale);
            let bytes = unsafe { std::slice::from_raw_parts(reused, slot_size) };
            assert!(bytes.iter().all(|byte| *byte == 0), "slot size {slot_size}");
        }
    }

    #[test]
    fn sequence_reuse_clears_the_header_before_publishing_without_clearing_capacity() {
        const HEADER: usize = 2 * std::mem::size_of::<usize>();
        for size in [HEADER + 3 * 8, PAGE_SIZE + HEADER] {
            let mut gc = Gc::new_with_config(GcConfig::default());
            let nodes = [
                GcLayoutNode {
                    offset: HEADER as u64,
                    stride: 8,
                    first_child: 1,
                    child_count: 0,
                    kind: crate::gc_layout::GC_LAYOUT_INITIALIZED_REPEAT,
                    ..POINTER_NODES[0]
                },
                POINTER_NODES[0],
            ];
            let desc = GcDesc {
                size: 0,
                nodes: nodes.as_ptr(),
                node_count: nodes.len(),
                ..pointer_desc()
            };
            let leaf = bytes_desc(8);
            let stale = gc.alloc(size, &desc);
            let keeper = gc.alloc(size, &desc);
            let old_child = gc.alloc(8, &leaf);
            unsafe {
                std::ptr::write_bytes(stale, 0xa5, size);
                stale.add(HEADER).cast::<*mut u8>().write(old_child);
            }
            gc.add_root(keeper);
            gc.add_root(old_child);
            assert!(gc.collect(&[]).is_empty());

            let reused = gc.try_alloc::<HEADER>(size, &desc).unwrap();
            assert_eq!(reused, stale);
            let bytes = unsafe { std::slice::from_raw_parts(reused, size) };
            assert!(bytes[..HEADER].iter().all(|byte| *byte == 0));
            assert!(bytes[HEADER + 8..].iter().all(|byte| *byte == 0xa5));
            assert_eq!(
                unsafe { reused.add(HEADER).cast::<*mut u8>().read() },
                old_child
            );
            gc.add_root(reused);
            assert!(gc.collect(&[]).is_empty());
            assert!(
                !is_live(&gc, old_child),
                "unpublished stale pointers must not retain targets"
            );

            let child = gc.alloc(8, &leaf);
            unsafe {
                reused.add(HEADER).cast::<*mut u8>().write(child);
                AtomicUsize::from_ptr(reused.cast()).store(1, Ordering::Release);
            }
            gc.add_root(reused);
            assert!(gc.collect(&[]).is_empty());
            assert!(
                is_live(&gc, child),
                "published initialized elements must be traced"
            );
        }
    }

    #[test]
    fn reused_scan_slots_install_the_new_layout_descriptor() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        let array_nodes = pointer_array_nodes(2);
        let array_desc = GcDesc {
            size: 16,
            nodes: array_nodes.as_ptr(),
            node_count: array_nodes.len(),
            ..pointer_desc()
        };
        let scalar_nodes = [GcLayoutNode {
            offset: 8,
            ..POINTER_NODES[0]
        }];
        let scalar_desc = GcDesc {
            size: 16,
            nodes: scalar_nodes.as_ptr(),
            ..pointer_desc()
        };
        let stale = gc.alloc(16, &array_desc);
        let keeper = gc.alloc(16, &array_desc);
        unsafe { std::ptr::write_bytes(stale, 0xa5, 16) };
        gc.add_root(keeper);
        assert!(gc.collect(&[]).is_empty());

        let reused = gc.alloc(16, &scalar_desc);
        assert_eq!(reused, stale);
        let (span_id, index) = gc.find_object(reused).unwrap();
        let span = gc.spans[span_id].as_ref().unwrap();

        assert_eq!(
            span.descs[index].load(Ordering::Relaxed),
            &raw const scalar_desc as *mut _
        );
        assert_eq!(span.sizes[index].load(Ordering::Relaxed), 16);
        assert_eq!(span.allocated.load(Ordering::Relaxed), 2);
        assert!(
            unsafe { std::slice::from_raw_parts(reused, 16) }
                .iter()
                .all(|byte| *byte == 0)
        );
    }

    #[test]
    fn reused_large_pages_are_zero_before_publication() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        let size = PAGE_SIZE + 1;
        let desc = bytes_desc(size);
        let stale = gc.alloc(size, &desc);
        unsafe { std::ptr::write_bytes(stale, 0xa5, size) };
        assert!(gc.collect(&[]).is_empty());

        let reused = gc.alloc(size, &desc);
        assert_eq!(reused, stale);
        let bytes = unsafe { std::slice::from_raw_parts(reused, size) };
        assert!(bytes.iter().all(|byte| *byte == 0));
    }

    #[test]
    fn dead_small_spans_preserve_accounting_interior_roots_and_zeroed_reuse() {
        for has_pointers in [false, true] {
            let mut gc = Gc::new_with_config(GcConfig::default());
            let desc = if has_pointers {
                pointer_desc()
            } else {
                bytes_desc(8)
            };
            // Fill one span, then leave a partially occupied second span.
            let count = PAGE_SIZE / 8 + 3;
            let objects: Vec<_> = (0..count).map(|_| gc.alloc(8, &desc)).collect();
            let keeper = *objects.last().unwrap();
            for dead in &objects[..count - 1] {
                unsafe { std::ptr::write_bytes(*dead, 0xa5, 8) };
            }
            let interior = unsafe { keeper.add(4) };
            gc.add_root(interior);
            assert!(gc.collect(&[]).is_empty());
            assert!(is_live(&gc, keeper));
            assert!(objects[..count - 1].iter().all(|ptr| !is_live(&gc, *ptr)));
            assert_eq!(gc.stats.live_objects, 1);
            assert_eq!(gc.stats.live_bytes, 8);
            assert_eq!(gc.stats.last_freed_objects, count - 1);
            assert_eq!(gc.stats.total_freed_bytes, (count - 1) * 8);

            // Marks must reset even when a span contains survivors, and free
            // slots from a previous sweep must not be counted as new frees.
            gc.add_root(interior);
            assert!(gc.collect(&[]).is_empty());
            assert_eq!(gc.stats.last_freed_objects, 0);
            assert!(gc.collect(&[]).is_empty());
            assert_eq!(gc.stats.last_freed_objects, 1);
            assert_eq!(gc.stats.total_frees, count);
            assert_eq!(gc.stats.total_freed_bytes, count * 8);
            assert_eq!(gc.stats.live_objects, 0);
            assert_eq!(gc.stats.live_bytes, 0);
            assert!(gc.spans.iter().all(Option::is_none));
            assert!(gc.collect(&[]).is_empty());
            assert_eq!(gc.stats.last_freed_objects, 0);
            assert_eq!(gc.stats.total_frees, count);

            // Reuse pages and span IDs in a different class and scan lane.
            let reused_desc = if has_pointers {
                bytes_desc(16)
            } else {
                pointer_desc()
            };
            let reused = gc.alloc(16, &reused_desc);
            assert!(is_live(&gc, reused));
            let bytes = unsafe { std::slice::from_raw_parts(reused, 16) };
            assert!(bytes.iter().all(|byte| *byte == 0));
            gc.add_root(reused);
            assert!(gc.collect(&[]).is_empty());
            assert_eq!(gc.stats.live_bytes, 16);
        }
    }

    #[test]
    fn heap_goal_grows_only_while_collections_take_much_of_the_time() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        gc.scales_heap_goal = true;
        let start = Instant::now();
        let ms = Duration::from_millis;
        // The first collection has no interval to measure.
        gc.update_heap_goal_scale(ms(5), start);
        assert_eq!(gc.heap_goal_scale, 1);
        // 5 ms in every 10 ms is far over; the scale doubles up to its limit.
        for step in 1..=8 {
            gc.update_heap_goal_scale(ms(5), start + ms(10) * step);
        }
        assert_eq!(gc.heap_goal_scale, GC_MAX_HEAP_SCALE);
        // Between the two thresholds, it holds.
        gc.update_heap_goal_scale(ms(1), start + ms(90) + ms(100));
        assert_eq!(gc.heap_goal_scale, GC_MAX_HEAP_SCALE);
        // A quiet process drifts back to the usual target.
        for step in 1..=8 {
            gc.update_heap_goal_scale(ms(1), start + ms(190) + Duration::from_secs(1) * step);
        }
        assert_eq!(gc.heap_goal_scale, 1);
        // Without the permission, or an explicit TARO_GC_PERCENT, it never moves.
        let mut fixed = Gc::new_with_config(GcConfig::default());
        fixed.update_heap_goal_scale(ms(5), start);
        fixed.update_heap_goal_scale(ms(5), start + ms(6));
        assert_eq!(fixed.heap_goal_scale, 1);
    }

    #[test]
    fn scaled_heap_goal_respects_the_memory_limit() {
        let config = GcConfig::default();
        assert_eq!(scaled_heap_goal(0, config, 16), GC_MIN_TRIGGER * 16);
        assert_eq!(scaled_heap_goal(8 << 20, config, 1), next_heap_goal(8 << 20, config));
        assert_eq!(scaled_heap_goal(8 << 20, config, 4), 40 << 20);
        let limited = GcConfig { memory_limit: Some(32 << 20), ..config };
        assert_eq!(scaled_heap_goal(8 << 20, limited, 16), 32 << 20);
    }

    #[test]
    fn sweep_releases_empty_segments_but_retains_one() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        let size = SEGMENT_SIZE + PAGE_SIZE;
        let desc = bytes_desc(size);
        let _ = gc.alloc(size, &desc);
        assert!(gc.segments.len() >= 2);

        assert!(gc.collect(&[]).is_empty());
        assert_eq!(gc.segments.len(), 1);
        assert!(gc.stats.released_bytes >= size);
    }

    #[cfg(unix)]
    // A shape that makes workers share: nodes with several children, where children
    // are reached from more than one parent, with long chains and cycles among them,
    // a pointer-free large leaf with many interior edges, and unreachable nodes.
    fn parallel_mark_graph(gc: &mut Gc, nodes: usize, desc: &GcDesc) -> (Vec<*mut u8>, Vec<bool>) {
        const EDGES: usize = 4;
        let objects: Vec<*mut u8> = (0..nodes).map(|_| gc.alloc(EDGES * 8, desc)).collect();
        let leaf_desc = bytes_desc(4 * PAGE_SIZE);
        let leaf = gc.alloc(4 * PAGE_SIZE, &leaf_desc);
        let mut edges = vec![[usize::MAX; EDGES]; nodes];
        let mut state = 0x9e37_79b9_u64;
        let mut next = |bound: usize| {
            state = state.wrapping_mul(0x5851_f42d_4c95_7f2d).wrapping_add(1);
            (state >> 33) as usize % bound
        };
        // A fifth of the nodes form a part that nothing live points to.
        let reachable_nodes = nodes - nodes / 5;
        for (index, node) in edges.iter_mut().enumerate() {
            if index < reachable_nodes {
                node[0] = (index * 2 + 1).min(reachable_nodes - 1);
                node[1] = (index * 2 + 2).min(reachable_nodes - 1);
                if index % 3 == 0 {
                    node[2] = next(reachable_nodes);
                }
            } else {
                node[0] = reachable_nodes + next(nodes - reachable_nodes);
                // Dead nodes may point at live ones, but not the reverse.
                node[1] = next(reachable_nodes);
            }
        }
        for (index, targets) in edges.iter().enumerate() {
            let fields = objects[index].cast::<*mut u8>();
            for (field, target) in targets.iter().enumerate() {
                if *target != usize::MAX {
                    unsafe { fields.add(field).write(objects[*target]) };
                }
            }
            if index < reachable_nodes && index % 16 == 0 {
                let interior = unsafe { leaf.add(index % (4 * PAGE_SIZE)) };
                unsafe { fields.add(3).write(interior) };
            }
        }
        let mut live = vec![false; nodes];
        let mut pending = vec![0];
        while let Some(index) = pending.pop() {
            if !std::mem::replace(&mut live[index], true) {
                pending.extend(edges[index].iter().copied().filter(|t| *t != usize::MAX));
            }
        }
        let mut objects = objects;
        objects.push(leaf);
        live.push(true);
        (objects, live)
    }

    #[test]
    fn parallel_marking_finds_exactly_what_is_reachable() {
        let nodes_layout = pointer_array_nodes(4);
        let desc = GcDesc {
            size: 32,
            align: 8,
            nodes: nodes_layout.as_ptr(),
            node_count: nodes_layout.len(),
        };
        for threads in [1, 2, 4, 8] {
            for nodes in [1, 100, 50_000] {
                let mut gc = Gc::new_with_config(GcConfig {
                    mark_threads: Some(threads),
                    ..GcConfig::default()
                });
                let (objects, live) = parallel_mark_graph(&mut gc, nodes, &desc);
                let expected = live.iter().filter(|live| **live).count();
                // Twice, as the first leaves marks clear for the second, and helpers
                // sleeping since the first must take up the second.
                for _ in 0..2 {
                    gc.add_root(unsafe { objects[0].add(8) });
                    assert!(gc.collect(&[]).is_empty());
                    assert_eq!(gc.last_marked_objects, expected, "{threads} threads, {nodes} nodes");
                    assert_eq!(gc.stats.live_objects, expected);
                    for (object, live) in objects.iter().zip(&live) {
                        assert_eq!(is_live(&gc, *object), *live);
                    }
                }
            }
        }
    }

    #[test]
    fn concurrent_parallel_collections_each_finish_correctly() {
        // Only tests collect several heaps at once; those beyond the first fall back
        // to marking alone rather than sharing helpers with a stranger's heap.
        let handles: Vec<_> = (0..4)
            .map(|_| {
                std::thread::spawn(|| {
                    let layout = pointer_array_nodes(4);
                    let desc = GcDesc {
                        size: 32,
                        align: 8,
                        nodes: layout.as_ptr(),
                        node_count: layout.len(),
                    };
                    let mut gc = Gc::new_with_config(GcConfig {
                        mark_threads: Some(4),
                        ..GcConfig::default()
                    });
                    let (objects, live) = parallel_mark_graph(&mut gc, 5_000, &desc);
                    for _ in 0..20 {
                        gc.add_root(objects[0]);
                        assert!(gc.collect(&[]).is_empty());
                        assert_eq!(
                            gc.last_marked_objects,
                            live.iter().filter(|live| **live).count()
                        );
                    }
                })
            })
            .collect();
        for handle in handles {
            handle.join().unwrap();
        }
    }

    #[test]
    fn mark_threads_follow_the_heap_and_the_program() {
        assert_eq!(parallel_mark::thread_count(0, 8), 1, "a small heap marks alone");
        let large = 1 << 20;
        assert_eq!(parallel_mark::thread_count(large, 1), 1, "one mutator, one marker");
        assert_eq!(parallel_mark::thread_count(large, 0), 1);
        let available = std::thread::available_parallelism().unwrap().get();
        assert_eq!(parallel_mark::thread_count(large, 2), available.min(2));
        assert!(parallel_mark::thread_count(large, 1024) <= available);
    }

    #[test]
    fn sweep_frees_exactly_the_unmarked_slots_and_reuses_the_lowest() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        let desc = bytes_desc(8);
        // Slots cross several bitmap words, with survivors in only some of them.
        let objects: Vec<_> = (0..200).map(|_| gc.alloc(8, &desc)).collect();
        let (kept, dead): (Vec<_>, Vec<_>) = objects
            .iter()
            .copied()
            .enumerate()
            .partition(|(index, _)| index % 7 == 0 || (64..128).contains(index));
        for (_, object) in &kept {
            gc.add_root(*object);
        }
        assert!(gc.collect(&[]).is_empty());
        assert_eq!(gc.stats.last_freed_objects, dead.len());
        assert_eq!(gc.stats.live_objects, kept.len());
        assert!(kept.iter().all(|(_, object)| is_live(&gc, *object)));
        assert!(dead.iter().all(|(_, object)| !is_live(&gc, *object)));

        let reused: Vec<_> = (0..dead.len()).map(|_| gc.alloc(8, &desc)).collect();
        let freed: Vec<_> = dead.iter().map(|(_, object)| *object).collect();
        assert_eq!(reused, freed, "free slots are taken in address order");
        assert!(reused.iter().all(|object| is_live(&gc, *object)));
    }

    #[test]
    fn a_span_never_allocates_past_its_last_slot() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        // No size class's slots fill the last bitmap word of these spans exactly.
        for size in [48, 80, 112, 3072] {
            let desc = bytes_desc(size);
            let first = gc.alloc(size, &desc);
            let (span_id, _) = gc.find_object(first).unwrap();
            let (count, base, bytes) = {
                let span = gc.spans[span_id].as_ref().unwrap();
                (span.object_count, span.base as usize, span.page_count * PAGE_SIZE)
            };
            assert_ne!(count % 64, 0, "this size must leave spare bitmap bits");
            let mut allocated = 1;
            while allocated < count {
                let object = gc.alloc(size, &desc) as usize;
                assert!(object >= base && object + size <= base + bytes);
                allocated += 1;
            }
            let next = gc.alloc(size, &desc);
            assert_ne!(gc.find_object(next).unwrap().0, span_id, "a full span moves on");
            let span = gc.spans[span_id].as_ref().unwrap();
            assert_eq!(span.allocated.load(Ordering::Relaxed), count);
        }
    }

    #[test]
    fn empty_spans_are_kept_only_for_recent_demand_within_the_warm_budget() {
        let spans_of = |gc: &Gc| gc.spans.iter().flatten().count();
        let mut gc = Gc::new_with_config(GcConfig::default());
        let desc = bytes_desc(8);
        let first = gc.alloc(8, &desc);
        let (span_id, _) = gc.find_object(first).unwrap();
        let span_address = (&**gc.spans[span_id].as_ref().unwrap()) as *const Span;

        // Taken since the last collection, so kept and reused without being rebuilt.
        assert!(gc.collect(&[]).is_empty());
        assert_eq!(spans_of(&gc), 1);
        assert_eq!(gc.kept_empty_span_bytes, CLASSES[small_class(8, 8).0].pages * PAGE_SIZE);
        assert!(!is_live(&gc, first), "keeping a span keeps nothing that was in it");
        assert_eq!(gc.stats.live_objects, 0);
        let reused = gc.alloc(8, &desc);
        assert_eq!(reused, first);
        let (reused_id, _) = gc.find_object(reused).unwrap();
        assert_eq!(
            (&**gc.spans[reused_id].as_ref().unwrap()) as *const Span,
            span_address
        );

        // Not taken since then, so its pages go back for any class to use.
        assert!(gc.collect(&[]).is_empty());
        assert_eq!(spans_of(&gc), 1, "this cycle took a span");
        assert!(gc.collect(&[]).is_empty());
        assert_eq!(spans_of(&gc), 0);
        assert_eq!(gc.kept_empty_span_bytes, 0);

        // A burst far past the warm budget keeps no more than that budget.
        let large = bytes_desc(PAGE_SIZE);
        for _ in 0..(4 * GC_MIN_TRIGGER / PAGE_SIZE) {
            gc.alloc(PAGE_SIZE, &large);
        }
        assert!(gc.collect(&[]).is_empty());
        assert!(gc.kept_empty_span_bytes <= GC_MIN_TRIGGER);
        assert!(gc.kept_empty_span_bytes >= GC_MIN_TRIGGER - 2 * PAGE_SIZE);

        // Under a memory limit, pages stay available to every class.
        let mut limited = Gc::new_with_config(GcConfig {
            memory_limit: Some(1 << 30),
            ..GcConfig::default()
        });
        limited.alloc(8, &desc);
        assert!(limited.collect(&[]).is_empty());
        assert_eq!(spans_of(&limited), 0);
    }

    #[test]
    fn collection_retains_bounded_pages_and_scavenges_under_pressure() {
        let mut gc = Gc::new_with_config(GcConfig::default());
        let desc = bytes_desc(PAGE_SIZE);
        // Keep a live neighbor in each segment so segment release cannot hide
        // whether the next cycle's bounded allocation reserve stays resident.
        let objects: Vec<_> = (0..6 * SEGMENT_PAGES)
            .map(|_| gc.alloc(PAGE_SIZE, &desc))
            .collect();
        let keepers: Vec<_> = objects
            .chunks_exact(SEGMENT_PAGES)
            .map(|segment| segment[SEGMENT_PAGES - 1])
            .collect();
        for &keeper in &keepers {
            unsafe { std::ptr::write_bytes(keeper, 0x5a, PAGE_SIZE) };
            gc.add_root(keeper);
        }
        // This is about free pages, so keep no empty spans in their place.
        gc.span_demand.fill([0; 2]);
        assert!(gc.collect(&[]).is_empty());
        assert_eq!(gc.segments.len(), 6);
        let eligible: usize = gc
            .segments
            .iter()
            .map(|segment| {
                segment
                    .free_runs
                    .iter()
                    .filter_map(|run| {
                        fully_free_os_page_range(
                            segment.base(),
                            run.start,
                            run.len,
                            segment.os_page_size,
                        )
                    })
                    .map(|range| range.len())
                    .sum::<usize>()
            })
            .sum();
        let retained = eligible - gc.stats.scavenged_bytes;
        assert!(
            retained > SEGMENT_SIZE,
            "warm pages should cover more than one segment of the next allocation cycle"
        );
        assert!(retained <= GC_MIN_TRIGGER);
        assert!(retained <= gc.heap_goal - gc.stats.live_bytes);
        assert!(
            gc.stats.scavenged_bytes > 0,
            "excess pages must still be scavenged"
        );

        // Tightening the soft limit must evict the retained pages on the next
        // collection, without touching either live neighboring span.
        gc.config.memory_limit = Some(gc.segment_bytes());
        for &keeper in &keepers {
            gc.add_root(keeper);
        }
        assert!(gc.collect(&[]).is_empty());
        assert_eq!(gc.stats.scavenged_bytes, eligible);
        for &keeper in &keepers {
            assert!(
                unsafe { std::slice::from_raw_parts(keeper, PAGE_SIZE) }
                    .iter()
                    .all(|byte| *byte == 0x5a)
            );
            gc.add_root(keeper);
        }
        assert!(gc.collect(&[]).is_empty());
        assert_eq!(gc.stats.scavenged_bytes, eligible, "do not scavenge twice");
    }

    #[cfg(unix)]
    #[test]
    fn partial_scavenging_is_accounted_once_and_cleared_on_reuse() {
        // Check Darwin's actual page accounting, not just our own bitmap:
        // MADV_DONTNEED succeeds there without making dirty pages reusable.
        #[cfg(target_os = "macos")]
        fn page_state(address: *const u8) -> i32 {
            unsafe extern "C" {
                static mach_task_self_: u32;
                fn mach_vm_page_query(
                    task: u32,
                    address: u64,
                    disposition: *mut i32,
                    references: *mut i32,
                ) -> i32;
            }
            let mut disposition = 0;
            let mut references = 0;
            // SAFETY: query our own mapped page; outputs are valid local words.
            let result = unsafe {
                mach_vm_page_query(
                    mach_task_self_,
                    address as u64,
                    &mut disposition,
                    &mut references,
                )
            };
            assert_eq!(result, 0);
            disposition
        }

        // Pressure bypasses the bounded warm-page reserve.
        let mut gc = Gc::new_with_config(GcConfig {
            memory_limit: Some(SEGMENT_SIZE),
            ..GcConfig::default()
        });
        let desc = bytes_desc(PAGE_SIZE);
        let pages_to_release = os_page_size().max(PAGE_SIZE) / PAGE_SIZE;
        let stale: Vec<_> = (0..pages_to_release)
            .map(|_| gc.alloc(PAGE_SIZE, &desc))
            .collect();
        let keeper = gc.alloc(PAGE_SIZE, &desc);
        unsafe { std::ptr::write_bytes(stale[0], 0xa5, PAGE_SIZE) };
        gc.add_root(keeper);

        assert!(gc.collect(&[]).is_empty());
        let expected = os_page_size().max(PAGE_SIZE);
        assert_eq!(gc.stats.scavenged_bytes, expected);
        gc.add_root(keeper);
        assert!(gc.collect(&[]).is_empty());
        assert_eq!(gc.stats.scavenged_bytes, expected);
        #[cfg(target_os = "macos")]
        {
            let state = page_state(stale[0]);
            // VM_PAGE_QUERY_PAGE_PRESENT / VM_PAGE_QUERY_PAGE_REUSABLE.
            assert!(
                state & 0x0001 == 0 || state & 0x0800 != 0,
                "page state {state:#x}"
            );
        }

        let reused = gc.alloc(PAGE_SIZE, &desc);
        assert!(stale.contains(&reused));
        let (segment, _) = gc.find_object(reused).expect("reused allocation");
        let span = gc.spans[segment].as_ref().expect("reused span");
        let segment = &gc.segments[span.segment];
        let mapping_base = segment.mapping.as_ref().unwrap().as_ptr() as usize;
        let os_page = (reused as usize - mapping_base) / segment.os_page_size;
        assert!(!segment.scavenged_os_pages[os_page]);
        let bytes = unsafe { std::slice::from_raw_parts(reused, PAGE_SIZE) };
        assert!(bytes.iter().all(|byte| *byte == 0));
        #[cfg(target_os = "macos")]
        assert_eq!(
            page_state(reused) & 0x0800,
            0,
            "reused page is charged again"
        );
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
        let ptr = gc.alloc(8, &desc);
        gc.register_reclaimer(
            ptr,
            count_finalization,
            &count as *const AtomicUsize as usize,
        );

        gc.add_root(ptr);
        assert!(gc.collect(&[]).is_empty());

        let work = gc.collect(&[]);
        assert_eq!(work.reclaimers.len(), 1);
        assert_eq!(count.load(Ordering::Acquire), 0);
        for reclaimer in work.reclaimers {
            (reclaimer.callback)(reclaimer.data);
        }
        assert_eq!(count.load(Ordering::Acquire), 1);
        assert!(gc.collect(&[]).is_empty());
    }

    #[test]
    fn pointer_maps_keep_mixed_span_reclaimers_until_the_last_root_is_removed() {
        let mut gc = Gc::new();
        let descriptors = [bytes_desc(8), bytes_desc(256), bytes_desc(16385)];
        let count = AtomicUsize::new(0);
        let mut retained = Vec::new();
        for index in 0..48 {
            let descriptor = &descriptors[index % descriptors.len()];
            let object = gc.alloc(descriptor.size, descriptor);
            gc.register_reclaimer(object, count_finalization, &count as *const _ as usize);
            if index % 2 == 0 {
                gc.add_persistent_root(object);
                gc.add_persistent_root(object);
                gc.remove_persistent_root(object);
                retained.push(object);
            }
        }
        let first = gc.collect(&[]);
        assert_eq!(first.reclaimers.len(), 24);
        assert_eq!(count.load(Ordering::Acquire), 0);
        for reclaimer in first.reclaimers {
            (reclaimer.callback)(reclaimer.data);
        }
        for object in retained {
            gc.remove_persistent_root(object);
        }
        let second = gc.collect(&[]);
        assert_eq!(second.reclaimers.len(), 24);
        for reclaimer in second.reclaimers {
            (reclaimer.callback)(reclaimer.data);
        }
        assert_eq!(count.load(Ordering::Acquire), 48);
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
    fn weak_cell_clears_before_its_managed_target_is_swept() {
        let mut gc = Gc::new();
        let desc = bytes_desc(16);
        let owner = gc.alloc(16, &desc);
        let target = unsafe { owner.add(4) };
        let cell = gc.alloc_weak_cell(target);

        gc.add_root(owner);
        gc.add_root(cell);
        gc.collect(&[]);
        assert_eq!(crate::gc_weak::load_cell(cell), target);
        assert_eq!(
            gc.weak_cells_by_owner
                .get(&(owner as *const u8))
                .map(Vec::len),
            Some(1)
        );

        gc.add_root(cell);
        gc.collect(&[]);
        assert!(crate::gc_weak::load_cell(cell).is_null());
        assert!(gc.find_object(owner).is_none());
        assert!(gc.find_object(cell).is_some());
        assert!(gc.weak_cells_by_owner.is_empty());
    }

    #[test]
    fn unreachable_weak_cells_are_removed_from_the_side_table() {
        let mut gc = Gc::new();
        let desc = bytes_desc(8);
        let owner = gc.alloc(8, &desc);
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

        assert_eq!(crate::gc_weak::load_cell(cell), target.cast_mut());
    }

    #[test]
    fn static_roots_keep_global_pointer_alive() {
        let mut gc = Gc::new();
        let leaf_desc = bytes_desc(8);
        let child = gc.alloc(8, &leaf_desc);
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
    fn fixed_array_tracing_stops_before_allocator_padding() {
        let mut gc = Gc::new();
        let leaf_desc = bytes_desc(8);
        let pointer_desc = pointer_desc();
        let elem_size = std::mem::size_of::<*mut u8>();
        let inside = gc.alloc(8, &leaf_desc);
        let padding = gc.alloc(8, &leaf_desc);
        // Five pointer slots round up to at least six slots. Bytes in
        // allocator padding must not extend the requested buffer capacity.
        let nodes = pointer_array_nodes(5);
        let array_desc = GcDesc {
            size: elem_size * 5,
            nodes: nodes.as_ptr(),
            node_count: nodes.len(),
            ..pointer_desc
        };
        let buffer = gc.alloc(array_desc.size, &array_desc);
        let (span, _) = gc.find_object(buffer).unwrap();
        assert!(gc.spans[span].as_ref().unwrap().object_size >= elem_size * 6);
        unsafe {
            (buffer as *mut *mut u8).write(inside);
            (buffer as *mut *mut u8).add(5).write(padding);
        }
        gc.add_root(buffer);
        gc.collect(&[]);
        gc.add_root(buffer);
        gc.collect(&[]);
        assert!(is_live(&gc, inside));
        assert!(!is_live(&gc, padding));
    }

    #[test]
    fn fixed_array_descriptors_trace_all_elements_in_small_and_large_spans() {
        for capacity in [2, PAGE_SIZE] {
            let mut gc = Gc::new();
            let leaf_desc = bytes_desc(8);
            let pointer_desc = pointer_desc();
            let elem_size = std::mem::size_of::<*mut u8>();
            let first = gc.alloc(8, &leaf_desc);
            let last = gc.alloc(8, &leaf_desc);
            let nodes = pointer_array_nodes(capacity);
            let array_desc = GcDesc {
                size: elem_size * capacity,
                nodes: nodes.as_ptr(),
                node_count: nodes.len(),
                ..pointer_desc
            };
            let buffer = gc.alloc(array_desc.size, &array_desc);
            unsafe {
                (buffer as *mut *mut u8).write(first);
                (buffer as *mut *mut u8).add(capacity - 1).write(last);
            }
            gc.add_root(buffer);
            gc.collect(&[]);
            gc.add_root(buffer);
            gc.collect(&[]);
            assert!(is_live(&gc, first));
            assert!(is_live(&gc, last));
        }
    }

    #[test]
    fn cleared_slot_stops_retaining_its_element() {
        // Fixed arrays trace every declared slot. Dynamic List buffers use
        // the initialized-prefix descriptor tested in gc_sequence instead.
        let mut gc = Gc::new();
        let leaf_desc = bytes_desc(8);
        let pointer_desc = pointer_desc();
        let elem_size = std::mem::size_of::<*mut u8>();
        let child = gc.alloc(8, &leaf_desc);
        let capacity = elem_size * 4;
        let nodes = pointer_array_nodes(4);
        let array_desc = GcDesc {
            size: capacity,
            nodes: nodes.as_ptr(),
            node_count: nodes.len(),
            ..pointer_desc
        };
        let buffer = gc.alloc(capacity, &array_desc);

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
    fn allocation_registers_and_reattaches_before_refill() {
        std::thread::spawn(|| {
            for size in [8, PAGE_SIZE + 1, 8] {
                let ptr = __gc__alloc(size, &BYTE_DESC);
                assert!(!ptr.is_null());
                assert!(CURRENT_THREAD_STATE.with(|slot| {
                    slot.borrow()
                        .as_ref()
                        .is_some_and(|current| current.attached)
                }));
                __gc__thread_detach();
            }
        })
        .join()
        .expect("allocation registration thread");
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
                    // A native barrier cannot poll GC. Join it before entering
                    // managed code so another test's collection cannot strand
                    // some threads at the barrier and others at a safepoint.
                    barrier.wait();
                    __gc__thread_enter_managed();
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

    #[test]
    fn a_reattached_thread_resumes_running_instead_of_staying_parked() {
        std::thread::spawn(|| {
            __gc__thread_enter_managed();
            __gc__thread_detach();
            // Implicit reattachment through allocation must not leave the
            // detach-time safepoint published while this thread mutates.
            assert!(!__gc__alloc(BYTE_DESC.size, &BYTE_DESC).is_null());
            assert!(CURRENT_THREAD_STATE.with(|slot| {
                let slot = slot.borrow();
                let current = slot.as_ref().expect("registered mutator");
                current.attached && !current.state.at_safepoint.load(Ordering::Acquire)
            }));
            __gc__thread_detach();
        })
        .join()
        .unwrap();
    }

    #[test]
    fn foreign_callbacks_register_and_park_their_thread() {
        let (ready_tx, ready_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            // First callback on a thread the runtime never saw.
            let token = __rt__foreign_enter();
            assert_eq!(token, 1);
            assert!(!__gc__alloc(BYTE_DESC.size, &BYTE_DESC).is_null());
            __rt__foreign_exit(token);
            ready_tx.send(()).unwrap();
            release_rx.recv().unwrap();
            // A later callback resumes the parked idle thread; a nested one
            // from running Taro code leaves its state alone.
            let token = __rt__foreign_enter();
            assert_eq!(token, 1);
            assert_eq!(__rt__foreign_enter(), 0);
            __rt__foreign_exit(0);
            __rt__foreign_exit(token);
            ready_tx.send(()).unwrap();
            release_rx.recv().unwrap();
        });
        // Waiting on a native channel cannot poll; park this thread around
        // each wait so concurrent collections are not stranded on it.
        let wait = |rx: &mpsc::Receiver<()>| {
            __rt__gc_enter_blocking();
            rx.recv_timeout(Duration::from_secs(5)).unwrap();
            __rt__gc_exit_blocking();
        };
        wait(&ready_rx);
        // The worker is idle outside Taro; collection must not wait for it.
        __gc__collect();
        release_tx.send(()).unwrap();
        wait(&ready_rx);
        __gc__collect();
        release_tx.send(()).unwrap();
        __rt__gc_enter_blocking();
        worker.join().unwrap();
        __rt__gc_exit_blocking();
        __gc__thread_detach();
    }

    #[test]
    fn a_foreign_handle_roots_its_target_until_deleted() {
        use crate::gc_handles::{__gc__handle_delete, __gc__handle_new, __gc__handle_value};
        let target = std::hint::black_box(__gc__alloc(BYTE_DESC.size, &BYTE_DESC));
        let handle = __gc__handle_new(target);
        let probe = create_weak_cell(target);
        with_gc(|gc| gc.add_persistent_root(probe));
        __gc__collect();
        assert_eq!(crate::gc_weak::load_cell(probe), target);
        assert_eq!(__gc__handle_value(handle), target);

        assert!(__gc__handle_delete(handle));
        assert!(!__gc__handle_delete(handle), "a deleted id stays deleted");
        assert!(__gc__handle_value(handle).is_null());
        __gc__collect();
        assert!(
            crate::gc_weak::load_cell(probe).is_null(),
            "deletion releases the root"
        );
        with_gc(|gc| gc.remove_persistent_root(probe));
        assert_eq!(__gc__handle_new(std::ptr::null()), 0);
        __gc__thread_detach();
    }

    #[test]
    fn an_idle_loop_publishes_its_outer_roots_without_walking_its_stack() {
        let (ready_tx, ready_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel::<()>();
        let (done_tx, done_rx) = mpsc::channel();
        let (finish_tx, finish_rx) = mpsc::channel::<()>();
        let worker = std::thread::spawn(move || {
            __gc__thread_enter_managed();
            // Reachable only through the captured roots: this test's frames have
            // no stack maps, so a walk here would find nothing.
            let target = std::hint::black_box(__gc__alloc(BYTE_DESC.size, &BYTE_DESC));
            OuterRoots(vec![target.cast_const()]).idle_wait(|| {
                ready_tx.send(target as usize).unwrap();
                release_rx.recv().unwrap();
            });
            // Later waits replace them, so an earlier capture pins nothing.
            OuterRoots(Vec::new()).idle_wait(|| {
                done_tx.send(()).unwrap();
                finish_rx.recv().unwrap();
            });
            __gc__thread_detach();
        });
        let target = ready_rx.recv_timeout(Duration::from_secs(5)).unwrap() as *const u8;
        let probe = create_weak_cell(target);
        with_gc(|gc| gc.add_persistent_root(probe));
        __gc__collect();
        assert_eq!(crate::gc_weak::load_cell(probe).cast_const(), target);
        release_tx.send(()).unwrap();
        // A collection from a parallel test can't stall on this thread's wait.
        __rt__gc_enter_blocking();
        done_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        __rt__gc_exit_blocking();
        __gc__collect();
        assert!(crate::gc_weak::load_cell(probe).is_null());
        finish_tx.send(()).unwrap();
        __rt__gc_enter_blocking();
        worker.join().unwrap();
        __rt__gc_exit_blocking();
        with_gc(|gc| gc.remove_persistent_root(probe));
        __gc__thread_detach();
    }

    #[test]
    fn generated_blocking_park_scans_the_frozen_stack_without_walking() {
        let (ready_tx, ready_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            __gc__thread_enter_managed();
            // Reachable only from this frame's stack slot, never published.
            let target = std::hint::black_box(__gc__alloc(BYTE_DESC.size, &BYTE_DESC));
            let slot = std::hint::black_box(&target as *const *mut u8);
            __rt__gc_enter_blocking_at(slot.cast());
            assert!(CURRENT_THREAD_STATE.with(|current| {
                let current = current.borrow();
                let current = current.as_ref().expect("registered mutator");
                unsafe { (*current.state.published_roots.get()).is_empty() }
            }));
            ready_tx.send(target as usize).unwrap();
            release_rx.recv().unwrap();
            __rt__gc_exit_blocking();
            std::hint::black_box(target);
            __gc__thread_detach();
        });
        let target = ready_rx.recv_timeout(Duration::from_secs(5)).unwrap() as *const u8;
        let probe = create_weak_cell(target);
        with_gc(|gc| gc.add_persistent_root(probe));
        __gc__collect();
        assert_eq!(crate::gc_weak::load_cell(probe).cast_const(), target);
        release_tx.send(()).unwrap();
        __rt__gc_enter_blocking();
        worker.join().unwrap();
        __rt__gc_exit_blocking();
        with_gc(|gc| gc.remove_persistent_root(probe));
        __gc__thread_detach();
    }

    #[test]
    fn blocked_mutator_keeps_its_published_interior_root_live() {
        let (ready_tx, ready_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            __gc__thread_enter_managed();
            let target = __gc__alloc(BYTE_DESC.size, &BYTE_DESC);
            let interior = unsafe { target.add(1) };
            TEST_ROOTS.with(|roots| roots.borrow_mut().push(interior));
            __rt__gc_enter_blocking();
            ready_tx.send(interior as usize).unwrap();
            release_rx.recv().unwrap();
            __rt__gc_exit_blocking();
            TEST_ROOTS.with(|roots| roots.borrow_mut().clear());
            __gc__thread_detach();
        });
        let interior = ready_rx.recv_timeout(Duration::from_secs(5)).unwrap() as *const u8;
        let probe = create_weak_cell(interior);
        with_gc(|gc| gc.add_persistent_root(probe));
        __gc__collect();
        assert_eq!(crate::gc_weak::load_cell(probe).cast_const(), interior);
        release_tx.send(()).unwrap();
        // Joining a native worker cannot poll; publish this thread as blocked
        // so an unrelated concurrent collection cannot strand the worker.
        __rt__gc_enter_blocking();
        worker.join().unwrap();
        __rt__gc_exit_blocking();
        __gc__collect();
        assert!(crate::gc_weak::load_cell(probe).is_null());
        with_gc(|gc| gc.remove_persistent_root(probe));
        __gc__thread_detach();
    }

    static RAW_POINTER_NODES: [GcLayoutNode; 1] = [GcLayoutNode {
        offset: 0,
        stride: 0,
        first_child: 0,
        child_count: 0,
        kind: crate::gc_layout::GC_LAYOUT_RAW_POINTER,
        width: 0,
        reserved: [0; 6],
    }];

    fn verifying_gc() -> Gc {
        let mut gc = Gc::new_with_config(GcConfig::default());
        gc.verify = true;
        gc
    }

    /// Leave `dead` freed beside a rooted neighbour, so its span stays mapped.
    fn freed_neighbour(gc: &mut Gc) -> (*mut u8, *mut u8) {
        let keep = gc.alloc(BYTE_DESC.size, &BYTE_DESC);
        let dead = gc.alloc(BYTE_DESC.size, &BYTE_DESC);
        gc.add_root(keep);
        gc.collect(&[]);
        assert!(is_live(gc, keep));
        assert!(!is_live(gc, dead));
        (keep, dead)
    }

    /// Run `test` again in a child process and require it to abort with `message`.
    fn assert_child_aborts(test: &str, env: &str, message: &str) {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", test, "--nocapture"])
            .env(env, "1")
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success(), "{stderr}");
        assert!(stderr.contains(message), "{stderr}");
    }

    #[test]
    fn verification_poisons_freed_cells() {
        let mut gc = verifying_gc();
        let (_, dead) = freed_neighbour(&mut gc);
        let bytes = unsafe { std::slice::from_raw_parts(dead, BYTE_DESC.size) };
        assert!(bytes.iter().all(|byte| *byte == GC_POISON_BYTE));
        // Reusing an untouched poisoned cell hands out zeroed storage.
        let reused = gc.alloc(BYTE_DESC.size, &BYTE_DESC);
        assert_eq!(reused, dead);
        assert!(
            unsafe { std::slice::from_raw_parts(reused, BYTE_DESC.size) }
                .iter()
                .all(|byte| *byte == 0)
        );
    }

    #[test]
    fn verification_rejects_writes_to_freed_cells() {
        if std::env::var_os("TARO_TEST_GC_WRITE_AFTER_FREE").is_some() {
            let mut gc = verifying_gc();
            let (_, dead) = freed_neighbour(&mut gc);
            unsafe { dead.add(3).write(1) };
            let _ = gc.alloc(BYTE_DESC.size, &BYTE_DESC);
            panic!("reusing a written freed cell must abort");
        }
        assert_child_aborts(
            "garbage_collector::tests::verification_rejects_writes_to_freed_cells",
            "TARO_TEST_GC_WRITE_AFTER_FREE",
            "was written at offset 3 after it was freed",
        );
    }

    #[test]
    fn verification_rejects_managed_edges_into_freed_storage() {
        if std::env::var_os("TARO_TEST_GC_DANGLING_EDGE").is_some() {
            let mut gc = verifying_gc();
            let (keep, dead) = freed_neighbour(&mut gc);
            // A missed root: a live object still holds the reclaimed cell.
            let desc = pointer_desc();
            let holder = gc.alloc(desc.size, &desc);
            unsafe { holder.cast::<*mut u8>().write(dead) };
            gc.add_root(keep);
            gc.add_root(holder);
            gc.collect(&[]);
            panic!("a managed edge into freed storage must abort");
        }
        assert_child_aborts(
            "garbage_collector::tests::verification_rejects_managed_edges_into_freed_storage",
            "TARO_TEST_GC_DANGLING_EDGE",
            "references freed storage",
        );
    }

    #[test]
    fn verification_allows_dangling_raw_pointers() {
        let mut gc = verifying_gc();
        let (keep, dead) = freed_neighbour(&mut gc);
        let desc = GcDesc {
            size: std::mem::size_of::<*mut u8>(),
            align: std::mem::align_of::<*mut u8>(),
            nodes: RAW_POINTER_NODES.as_ptr(),
            node_count: RAW_POINTER_NODES.len(),
        };
        let holder = gc.alloc(desc.size, &desc);
        unsafe { holder.cast::<*mut u8>().write(dead) };
        gc.add_root(keep);
        gc.add_root(holder);
        gc.collect(&[]);
        assert!(is_live(&gc, holder));
        assert!(!is_live(&gc, dead));
    }

    fn allocation_panic(size: usize) -> String {
        crate::panic_unwind::catch_executor_panic(|| __gc__alloc(size, &BYTE_DESC))
            .expect_err("the request was allocated")
            .message
    }

    #[test]
    fn oversized_requests_panic_before_allocating() {
        let largest = isize::MAX as usize & !(std::mem::size_of::<usize>() - 1);
        assert_eq!(checked_alloc_size(largest, &BYTE_DESC), largest);
        let before = with_gc(|gc| gc.segment_bytes());
        // The second size would wrap to a tiny one when rounded up to a word.
        for size in [isize::MAX as usize + 1, usize::MAX - 1] {
            assert_eq!(allocation_panic(size), "allocation size overflow");
        }
        assert_eq!(with_gc(|gc| gc.segment_bytes()), before);
    }

    #[test]
    fn unmappable_requests_panic_and_restore_the_reserve() {
        install_emergency_reserve();
        // A valid size beyond every address space fails to map.
        assert_eq!(allocation_panic(1 << 56), "out of memory");
        assert!(EMERGENCY_RESERVE.load(Ordering::Acquire).is_null());
        let small = __gc__alloc(BYTE_DESC.size, &BYTE_DESC);
        assert!(
            !small.is_null(),
            "the heap still allocates after exhaustion"
        );
        __gc__collect();
        assert!(!EMERGENCY_RESERVE.load(Ordering::Acquire).is_null());
    }
}

#[cfg(test)]
mod pacing_progress_tests {
    #[test]
    fn zero_percent_goal_requires_new_allocation_after_collection() {
        let live = super::GC_MIN_TRIGGER * 2;
        let config = super::GcConfig {
            percent: Some(0),
            memory_limit: None,
            mark_threads: None,
        };
        assert!(
            super::next_heap_goal(live, config) > live,
            "a nonallocating mutator must not immediately request another collection"
        );
    }
}
