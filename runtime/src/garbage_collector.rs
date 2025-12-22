//! Stop-the-world, non-moving mark-and-sweep collector for Taro.
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
//!    - Shadow stack frames (compiler emits push/pop + pointer slots).
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

use std::ops::Range;
use std::sync::{Mutex, OnceLock};

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
unsafe impl Sync for GcDesc {}

/// Shadow stack frame layout emitted by the compiler.
///
/// - prev: linked list to the previous frame.
/// - slots: pointer to an array of GC root pointers.
/// - count: number of slots.
#[repr(C)]
pub struct GcShadowFrame {
    pub prev: *mut GcShadowFrame,
    pub slots: *mut *mut u8,
    pub count: usize,
}

// Global shadow stack top.
static mut GC_SHADOW_TOP: *mut GcShadowFrame = std::ptr::null_mut();

#[unsafe(no_mangle)]
pub extern "C" fn __rt__gc_push_frame(frame: *mut GcShadowFrame) {
    unsafe {
        (*frame).prev = GC_SHADOW_TOP;
        GC_SHADOW_TOP = frame;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__gc_pop_frame(frame: *mut GcShadowFrame) {
    unsafe {
        if GC_SHADOW_TOP == frame {
            GC_SHADOW_TOP = (*frame).prev;
        }
    }
}

/// Allocate a GC-managed object with a payload of `size` bytes.
///
/// The descriptor controls pointer tracing and determines scan/noscan lane.
#[unsafe(no_mangle)]
pub extern "C" fn gc_alloc(size: usize, desc: *const GcDesc) -> *mut u8 {
    if size == 0 {
        return std::ptr::null_mut();
    }
    with_gc(|gc| gc.alloc(size, desc, false))
}

/// Allocate a GC-managed buffer for slices/strings.
///
/// The descriptor is for a single element; total allocation is elem_size * cap.
#[unsafe(no_mangle)]
pub extern "C" fn gc_makeslice(desc: *const GcDesc, len: usize, cap: usize) -> *mut u8 {
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
    if total == 0 {
        return std::ptr::null_mut();
    }
    with_gc(|gc| gc.alloc(total, desc, true))
}

#[unsafe(no_mangle)]
pub extern "C" fn gc_desc_u8() -> *const GcDesc {
    static DESC: GcDesc = GcDesc {
        size: 1,
        align: 1,
        ptr_offsets: std::ptr::null(),
        ptr_count: 0,
    };
    &DESC
}

#[unsafe(no_mangle)]
pub extern "C" fn gc_collect() {
    with_gc(|gc| gc.collect());
}

/// Poll for a pending collection at a compiler-inserted safepoint.
#[unsafe(no_mangle)]
pub extern "C" fn gc_poll() {
    with_gc(|gc| {
        if gc.alloc_since_gc >= gc.gc_threshold_bytes {
            gc.collect();
        }
    });
}

/// Register a static/global range as a root.
#[unsafe(no_mangle)]
pub extern "C" fn gc_register_static(begin: *const u8, end: *const u8) {
    if begin.is_null() || end.is_null() || end <= begin {
        return;
    }
    with_gc(|gc| gc.register_static(begin..end));
}

/// Manually add a root pointer (useful for embeddings/tests).
#[unsafe(no_mangle)]
pub extern "C" fn gc_add_root(ptr: *const u8) {
    if ptr.is_null() {
        return;
    }
    with_gc(|gc| gc.add_root(ptr));
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
    // Page index -> span id for that page; SPAN_NONE means free/unassigned.
    page_map: Vec<usize>,
    // Bump pointer in pages for fresh allocation.
    next_page: usize,
    // Free page runs (when spans are returned).
    free_runs: Vec<PageRun>,
}

// Cached segment bounds used to speed up segment lookup by address.
// This allows binary searching instead of scanning every segment.
struct SegmentRange {
    base: usize,
    end: usize,
    index: usize,
}

impl Segment {
    fn new(pages: usize) -> Self {
        // Allocate a page-aligned arena for the segment. Spans will carve pages
        // out of this arena; the segment owns the raw memory.
        let bytes = pages.saturating_mul(PAGE_SIZE);
        let layout =
            std::alloc::Layout::from_size_align(bytes, PAGE_SIZE).expect("segment layout");
        let data = unsafe { std::alloc::alloc_zeroed(layout) };
        if data.is_null() {
            std::alloc::handle_alloc_error(layout);
        }
        Self {
            data,
            len: bytes,
            page_map: vec![SPAN_NONE; pages],
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
        if pages == 0 {
            return;
        }
        self.free_runs.push(PageRun { start, len: pages });
        self.free_runs.sort_by_key(|r| r.start);
        let mut merged: Vec<PageRun> = Vec::with_capacity(self.free_runs.len());
        for run in self.free_runs.drain(..) {
            if let Some(last) = merged.last_mut() {
                if last.start + last.len == run.start {
                    last.len = last.len.saturating_add(run.len);
                    continue;
                }
            }
            merged.push(run);
        }
        self.free_runs = merged;
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
    sizes: Vec<usize>,

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
        desc: *const GcDesc,
        is_array: bool,
    ) -> Option<*mut u8> {
        // Allocate from the free list and record per-slot metadata.
        let index = self.free_list.pop()?;
        bitset_set(&mut self.alloc_map, index, true);
        bitset_set(&mut self.mark_map, index, false);
        if self.has_pointers {
            self.descs[index] = desc;
            self.sizes[index] = payload_size;
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
            bitset_set(&mut self.array_map, index, false);
        }
        self.free_list.push(index);
        self.allocated = self.allocated.saturating_sub(1);
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

    fn log(&self) {
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

#[derive(Debug, Default)]
struct SweepStats {
    objects: usize,
    bytes: usize,
}

// Top-level GC state. Spans are stored separately so the page map can store
// just a span id, and the class lists track spans with free slots.
struct Gc {
    segments: Vec<Segment>,
    // Sorted by base address for binary searching.
    segment_ranges: Vec<SegmentRange>,
    spans: Vec<Option<Span>>,
    size_classes: Vec<usize>,
    // Per size class: [scan spans, noscan spans].
    class_spans: Vec<[Vec<usize>; 2]>,
    static_roots: Vec<Range<*const u8>>,
    manual_roots: Vec<*const u8>,
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
        let base = segments[0].base();
        let end = base + segments[0].len;
        let segment_ranges = vec![SegmentRange {
            base,
            end,
            index: 0,
        }];
        Self {
            segments,
            segment_ranges,
            spans: Vec::new(),
            size_classes,
            class_spans,
            static_roots: Vec::new(),
            manual_roots: Vec::new(),
            stats: GcStats::default(),
            alloc_since_gc: 0,
            gc_threshold_bytes: GC_MIN_TRIGGER,
        }
    }

    fn register_static(&mut self, range: Range<*const u8>) {
        // Static ranges are conservatively scanned as potential roots.
        self.static_roots.push(range);
    }

    fn add_root(&mut self, ptr: *const u8) {
        // Manual roots are consumed on the next collection.
        self.manual_roots.push(ptr);
    }

    // Route small allocations to size-class spans; large allocations get a span.
    // payload_size is the requested size, alloc_size is rounded up for alignment.
    fn alloc(&mut self, size: usize, desc: *const GcDesc, is_array: bool) -> *mut u8 {
        // Compute allocation size with alignment and choose the scan lane.
        let payload_size = size;
        let align = desc_alignment(desc).max(std::mem::size_of::<usize>());
        let alloc_size = align_up(payload_size, align);
        let has_pointers = desc_has_pointers(desc);

        // Small allocations go through size-class spans; large ones get whole pages.
        let (ptr, alloc_bytes) = if alloc_size > PAGE_SIZE {
            self.alloc_large(payload_size, alloc_size, desc, has_pointers, is_array)
        } else {
            self.alloc_small(payload_size, alloc_size, desc, has_pointers, is_array)
        };

        self.after_alloc(ptr, alloc_bytes);
        ptr
    }

    // Allocate from a span that has free slots for this size class.
    fn alloc_small(
        &mut self,
        payload_size: usize,
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
            .alloc_small(payload_size, desc, is_array)
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
            desc,
            has_pointers,
            is_array,
        );
        let total_bytes = pages.saturating_mul(PAGE_SIZE);
        self.spans[span_id] = Some(span);
        (base, total_bytes)
    }

    // Update stats and optionally trigger a collection.
    // The freshly allocated pointer is pushed as a temporary root if GC runs.
    fn after_alloc(&mut self, ptr: *mut u8, alloc_bytes: usize) {
        // Update stats and allow safepoints to decide when to collect.
        self.stats.record_alloc(alloc_bytes);
        self.alloc_since_gc = self.alloc_since_gc.saturating_add(alloc_bytes);
        let _ = ptr;
    }

    fn alloc_span_id(&mut self) -> usize {
        // Span ids are monotonic to avoid stale ids in class lists.
        self.spans.push(None);
        self.spans.len() - 1
    }

    // Reuse a span with free slots or create a new one for this class.
    fn take_span_for_class(&mut self, class_index: usize, lane: usize) -> usize {
        // Pop spans from the per-class list until a live, reusable span is found.
        let list = &mut self.class_spans[class_index][lane];
        while let Some(span_id) = list.pop() {
            if let Some(span) = self.spans.get_mut(span_id).and_then(|s| s.as_mut()) {
                span.in_class_list = false;
                if span.has_free() {
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
        self.insert_segment_range(index);
        let segment = &mut self.segments[index];
        let start_page = segment
            .alloc_pages(pages)
            .expect("new segment has space");
        let base = unsafe { segment.data.add(start_page * PAGE_SIZE) };
        (index, start_page, base)
    }

    // Insert a segment range into the sorted index used for binary search.
    fn insert_segment_range(&mut self, index: usize) {
        // Keep the range list sorted by base for fast binary search.
        let base = self.segments[index].base();
        let end = base + self.segments[index].len;
        let range = SegmentRange { base, end, index };
        let pos = self
            .segment_ranges
            .binary_search_by(|r| r.base.cmp(&base))
            .unwrap_or_else(|p| p);
        self.segment_ranges.insert(pos, range);
    }

    // Find the segment index for a pointer via binary search on ranges.
    fn segment_index_for_ptr(&self, ptr: *const u8) -> Option<usize> {
        // Binary search the segment ranges to find the owning segment.
        let p = ptr as usize;
        let mut lo = 0;
        let mut hi = self.segment_ranges.len();
        while lo < hi {
            let mid = (lo + hi) / 2;
            let range = &self.segment_ranges[mid];
            if p < range.base {
                hi = mid;
            } else if p >= range.end {
                lo = mid + 1;
            } else {
                return Some(range.index);
            }
        }
        None
    }

    fn collect(&mut self) {
        // Stop-the-world collection: gather roots, mark, then sweep.
        let manual_roots = std::mem::take(&mut self.manual_roots);
        let static_roots = std::mem::take(&mut self.static_roots);
        self.mark_roots(manual_roots.into_iter(), &static_roots);
        self.static_roots = static_roots;
        let freed = self.sweep();
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
    }

    fn mark_roots<I>(&mut self, manual_roots: I, static_roots: &[Range<*const u8>])
    where
        I: IntoIterator<Item = *const u8>,
    {
        // Collect candidate roots into a stack for iterative marking.
        let mut stack: Vec<*const u8> = manual_roots.into_iter().collect();

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

        self.push_shadow_roots(&mut stack);
        self.trace_stack(&mut stack);
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
        let base = unsafe { span.base.add(object_index * span.object_size) };
        let elem_size = desc.size;
        let is_array = bitset_get(&span.array_map, object_index);

        if is_array && elem_size != 0 {
            // Arrays/slices: apply field offsets for each element.
            let count = payload_size / elem_size;
            for index in 0..count {
                let elem_base = unsafe { base.add(index * elem_size) };
                self.push_pointer_fields(elem_base, elem_size, desc, stack);
            }
        } else {
            // Single object: trace pointer fields once.
            self.push_pointer_fields(base, payload_size, desc, stack);
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

    fn push_shadow_roots(&self, stack: &mut Vec<*const u8>) {
        // Walk the shadow stack frames produced by codegen.
        let mut frame = unsafe { GC_SHADOW_TOP };
        while !frame.is_null() {
            let count = unsafe { (*frame).count };
            let slots = unsafe { (*frame).slots };
            if !slots.is_null() {
                for i in 0..count {
                    let val = unsafe { *slots.add(i) };
                    if !val.is_null() {
                        stack.push(val as *const u8);
                    }
                }
            }
            frame = unsafe { (*frame).prev };
        }
    }

    // Sweep spans: free unmarked slots, and return empty spans to the segment.
    fn sweep(&mut self) -> SweepStats {
        // Sweep spans: free unmarked slots, return empty spans to segments.
        let mut freed = SweepStats::default();
        for span_id in 0..self.spans.len() {
            let Some(mut span) = self.spans[span_id].take() else {
                continue;
            };

            // Large span: single slot at index 0.
            if span.class_index.is_none() {
                // If the lone object is unmarked, free the entire span.
                if bitset_get(&span.alloc_map, 0) && !bitset_get(&span.mark_map, 0) {
                    let total_bytes = span.page_count.saturating_mul(PAGE_SIZE);
                    bitset_set(&mut span.alloc_map, 0, false);
                    if span.has_pointers && !span.descs.is_empty() {
                        span.descs[0] = std::ptr::null();
                        span.sizes[0] = 0;
                    }
                    span.allocated = 0;
                    self.stats.record_free(total_bytes);
                    freed.objects += 1;
                    freed.bytes = freed.bytes.saturating_add(total_bytes);
                    self.free_span_pages(&span);
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
                span.free_small(index);
                self.stats.record_free(span.object_size);
                freed.objects += 1;
                freed.bytes = freed.bytes.saturating_add(span.object_size);
            }

            // If empty, return the span to the segment.
            if span.allocated == 0 {
                self.free_span_pages(&span);
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
        freed
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

    fn free_page_stats(&self) -> (usize, usize) {
        // Sum free pages/runs across all segments for logging.
        let mut runs: usize = 0;
        let mut pages: usize = 0;
        for segment in &self.segments {
            runs = runs.saturating_add(segment.free_runs.len());
            pages = pages
                .saturating_add(segment.free_runs.iter().map(|r| r.len).sum::<usize>());
            if segment.next_page < segment.page_count() {
                runs = runs.saturating_add(1);
                pages = pages.saturating_add(segment.page_count() - segment.next_page);
            }
        }
        (runs, pages)
    }
}

fn with_gc<R>(f: impl FnOnce(&mut Gc) -> R) -> R {
    // Single global GC instance protected by a mutex.
    static INSTANCE: OnceLock<Mutex<Gc>> = OnceLock::new();
    let gc = INSTANCE.get_or_init(|| Mutex::new(Gc::new()));
    let mut guard = gc.lock().expect("gc mutex");
    f(&mut guard)
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
    // Find the first size class that can fit `size`.
    for (index, class_size) in classes.iter().enumerate() {
        if size <= *class_size {
            return index;
        }
    }
    classes.len().saturating_sub(1)
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
    if has_pointers {
        0
    } else {
        1
    }
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
