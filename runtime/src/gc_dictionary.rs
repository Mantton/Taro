//! Raw SwissTable payload storage, traced using the table's control words.
//!
//! The stdlib owns probing and mutation. This module only allocates aligned
//! groups and supplies their GC layout; no hash function or public map API is
//! implemented here. Empty/deleted payloads are not source-language values.
use crate::{
    garbage_collector::{__gc__alloc, __gc__poll, GcDesc, with_runtime_root},
    gc_existentials::GcValueDescriptor,
    gc_layout::{
        GC_LAYOUT_INITIALIZED_REPEAT, GC_LAYOUT_POINTER, GC_LAYOUT_SWISS_GROUP, GcLayoutNode,
    },
};
use std::{
    cell::RefCell,
    collections::HashMap,
    mem::{align_of, size_of},
    ptr,
    sync::{
        Mutex, OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
};

const EMPTY_CONTROLS: u64 = 0x8080_8080_8080_8080;
const INITIALIZATION_BATCH: usize = 1024;
static POINTER_NODES: [GcLayoutNode; 1] = [GcLayoutNode {
    offset: 0,
    stride: 0,
    first_child: 0,
    child_count: 0,
    kind: GC_LAYOUT_POINTER,
    width: 0,
    reserved: [0; 6],
}];
static POINTER: GcDesc = GcDesc {
    size: size_of::<*mut u8>(),
    align: align_of::<*mut u8>(),
    nodes: POINTER_NODES.as_ptr(),
    node_count: 1,
};

#[repr(C)]
struct Header {
    initialized_groups: AtomicUsize,
}

struct Layout {
    descriptor: &'static GcDesc,
    data_offset: usize,
    group_stride: usize,
}

static LAYOUTS: OnceLock<Mutex<HashMap<usize, &'static Layout>>> = OnceLock::new();
thread_local! {
    // Immutable process-long metadata only; never managed objects.
    static LOCAL_LAYOUTS: RefCell<rustc_hash::FxHashMap<usize, &'static Layout>> =
        RefCell::new(rustc_hash::FxHashMap::default());
}

unsafe fn layout_for(entry: &'static GcDesc) -> Option<&'static Layout> {
    let key = entry as *const GcDesc as usize;
    if let Ok(Some(layout)) = LOCAL_LAYOUTS.try_with(|cache| cache.borrow().get(&key).copied()) {
        return Some(layout);
    }
    let layout = unsafe { canonical_layout_for(entry) }?;
    let _ = LOCAL_LAYOUTS.try_with(|cache| cache.borrow_mut().insert(key, layout));
    Some(layout)
}

unsafe fn canonical_layout_for(entry: &'static GcDesc) -> Option<&'static Layout> {
    let key = entry as *const GcDesc as usize;
    if !entry.align.is_power_of_two() || !entry.size.is_multiple_of(entry.align) {
        return None;
    }
    let align = entry.align.max(align_of::<u64>());
    let entry_offset = align;
    let group_stride = entry.size.checked_mul(8)?.checked_add(entry_offset)?;
    let data_offset = size_of::<Header>().checked_add(align - 1)? & !(align - 1);
    let mut layouts = LAYOUTS
        .get_or_init(|| Mutex::new(HashMap::new()))
        .lock()
        .unwrap();
    if let Some(layout) = layouts.get(&key) {
        return Some(layout);
    }
    let nodes = if entry.node_count == 0 {
        &[][..]
    } else {
        if entry.nodes.is_null() || entry.size == 0 {
            return None;
        }
        let mut nodes = Vec::with_capacity(entry.node_count.checked_add(2)?);
        nodes.push(GcLayoutNode {
            offset: data_offset as u64,
            stride: group_stride as u64,
            first_child: 1,
            child_count: 0, // Header.initialized_groups offset.
            kind: GC_LAYOUT_INITIALIZED_REPEAT,
            width: 0,
            reserved: [0; 6],
        });
        nodes.push(GcLayoutNode {
            offset: entry_offset as u64,
            stride: entry.size as u64,
            first_child: 2,
            child_count: 0, // Group control word offset.
            kind: GC_LAYOUT_SWISS_GROUP,
            width: 0,
            reserved: [0; 6],
        });
        for node in unsafe { std::slice::from_raw_parts(entry.nodes, entry.node_count) } {
            let mut node = *node;
            if node.child_count != 0 {
                node.first_child = node.first_child.checked_add(2)?;
            }
            nodes.push(node);
        }
        Box::leak(nodes.into_boxed_slice())
    };
    let descriptor = Box::leak(Box::new(GcDesc {
        size: 0,
        align,
        nodes: nodes.as_ptr(),
        node_count: nodes.len(),
    }));
    let layout = Box::leak(Box::new(Layout {
        descriptor,
        data_offset,
        group_stride,
    }));
    layouts.insert(key, layout);
    Some(layout)
}

/// Allocate eight-slot groups with empty controls and unpublished raw payloads.
///
/// # Safety
/// `entry` and its graph are immutable process-long compiler metadata. The
/// caller must initialize a complete payload before publishing a full control
/// byte, keeping that initialized value rooted across any intervening safepoint.
/// Deleted payloads may be discarded only after their control becomes non-full.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __gc__dictionary_groups_new(
    entry: *const GcValueDescriptor,
    groups: usize,
) -> *mut u8 {
    let Some(entry) = (unsafe { entry.as_ref() }) else {
        return ptr::null_mut();
    };
    let Some(entry) = (unsafe { entry.layout.as_ref() }) else {
        return ptr::null_mut();
    };
    let Some(layout) = (unsafe { layout_for(entry) }) else {
        return ptr::null_mut();
    };
    let Some(bytes) = groups
        .checked_mul(layout.group_stride)
        // A zero-sized last payload starts just after its control word. Keep
        // even that address inside the allocation, rather than one past it.
        .and_then(|size| {
            if entry.size == 0 {
                size.checked_add(1)
            } else {
                Some(size.max(1))
            }
        })
        .and_then(|size| layout.data_offset.checked_add(size))
        .filter(|bytes| *bytes <= isize::MAX as usize)
    else {
        return ptr::null_mut();
    };
    let allocation = __gc__alloc(bytes, layout.descriptor);
    unsafe {
        let header = allocation.cast::<Header>();
        header.write(Header {
            initialized_groups: AtomicUsize::new(0),
        });
        let data = allocation.add(layout.data_offset);
        if groups >= INITIALIZATION_BATCH {
            // Keep large construction cooperative without charging tiny maps
            // for a root registration. Only valid empty headers are published
            // before each poll; no payload has been initialized or exposed.
            with_runtime_root((&allocation as *const *mut u8).cast(), &POINTER, || {
                initialize_groups::<true>(header, data, groups, layout.group_stride);
            });
        } else {
            initialize_groups::<false>(header, data, groups, layout.group_stride);
        }
        data
    }
}

unsafe fn initialize_groups<const POLL: bool>(
    header: *mut Header,
    data: *mut u8,
    groups: usize,
    stride: usize,
) {
    for group in 0..groups {
        unsafe { data.add(group * stride).cast::<u64>().write(EMPTY_CONTROLS) };
        if POLL && (group + 1).is_multiple_of(INITIALIZATION_BATCH) {
            unsafe {
                (*header)
                    .initialized_groups
                    .store(group + 1, Ordering::Release)
            };
            __gc__poll();
        }
    }
    unsafe {
        (*header)
            .initialized_groups
            .store(groups, Ordering::Release)
    };
}

#[cfg(test)]
mod tests;
