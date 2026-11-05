//! Stable managed sequence storage. Logical collection length belongs to the
//! collection handle; this allocation publishes a separate initialized prefix.
//! The prefix never shrinks: removed/addressed slots stay valid until replaced
//! by another valid value or until this whole allocation becomes unreachable.
//! Publication is a direct header store, without a GC registry lookup/lock.
use crate::{
    garbage_collector::{GcDesc, alloc_with_zeroed_prefix, with_runtime_root},
    gc_existentials::{__gc__value_copy, GcValueDescriptor},
    gc_layout::{GC_LAYOUT_INITIALIZED_REPEAT, GC_LAYOUT_POINTER, GcLayoutNode},
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

#[repr(C)]
struct Header {
    initialized: AtomicUsize,
    capacity: usize,
}
struct Layout {
    descriptor: &'static GcDesc,
    data_offset: usize,
}
static LAYOUTS: OnceLock<Mutex<HashMap<usize, &'static Layout>>> = OnceLock::new();
thread_local! {
    // Descriptors and canonical layouts are immutable and process-long. Cache
    // their addresses locally so warm buffers avoid the global registry lock
    // and its hash work. This contains metadata only, never managed roots.
    static LOCAL_LAYOUTS: RefCell<rustc_hash::FxHashMap<usize, &'static Layout>> =
        RefCell::new(rustc_hash::FxHashMap::default());
}
static POINTER_NODE: [GcLayoutNode; 1] = [GcLayoutNode {
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
    nodes: POINTER_NODE.as_ptr(),
    node_count: 1,
};

fn data_offset(element: &GcDesc) -> Option<usize> {
    if !element.align.is_power_of_two() {
        return None;
    }
    let align = element.align.max(align_of::<Header>());
    if !align.is_power_of_two() {
        return None;
    }
    size_of::<Header>()
        .checked_add(align - 1)
        .map(|size| size & !(align - 1))
}
unsafe fn layout_for(element: &'static GcDesc) -> Option<&'static Layout> {
    let key = element as *const GcDesc as usize;
    if let Ok(Some(layout)) = LOCAL_LAYOUTS.try_with(|cache| cache.borrow().get(&key).copied()) {
        return Some(layout);
    }
    let layout = unsafe { canonical_layout_for(element) }?;
    // Native callbacks can arrive during TLS teardown. The process registry
    // remains authoritative when this thread's optional cache is unavailable.
    let _ = LOCAL_LAYOUTS.try_with(|cache| cache.borrow_mut().insert(key, layout));
    Some(layout)
}

unsafe fn canonical_layout_for(element: &'static GcDesc) -> Option<&'static Layout> {
    let data_offset = data_offset(element)?;
    let mut layouts = LAYOUTS
        .get_or_init(|| Mutex::new(HashMap::new()))
        .lock()
        .unwrap();
    let key = element as *const GcDesc as usize;
    if let Some(layout) = layouts.get(&key) {
        return Some(layout);
    }
    let nodes = if element.node_count == 0 {
        &[][..]
    } else {
        if element.size == 0 || element.nodes.is_null() {
            return None;
        }
        let mut nodes = Vec::with_capacity(element.node_count.checked_add(1)?);
        nodes.push(GcLayoutNode {
            offset: data_offset as u64,
            stride: element.size as u64,
            first_child: 1,
            child_count: 0,
            kind: GC_LAYOUT_INITIALIZED_REPEAT,
            width: 0,
            reserved: [0; 6],
        });
        for node in unsafe { std::slice::from_raw_parts(element.nodes, element.node_count) } {
            // Child indices in the embedded element graph move by one; leaf
            // fields have no child, while Repeat's child_count is its length.
            let mut node = *node;
            if node.child_count != 0 {
                node.first_child = node.first_child.checked_add(1)?;
            }
            nodes.push(node);
        }
        Box::leak(nodes.into_boxed_slice())
    };
    let descriptor = Box::leak(Box::new(GcDesc {
        size: 0,
        align: element.align.max(align_of::<Header>()),
        nodes: nodes.as_ptr(),
        node_count: nodes.len(),
    }));
    let layout = Box::leak(Box::new(Layout {
        descriptor,
        data_offset,
    }));
    layouts.insert(key, layout);
    Some(layout)
}

/// Allocate capacity without publishing source-language values. The returned
/// interior address is stable, including for empty and zero-sized buffers.
/// Only the header is zeroed before allocation publication. Spare capacity is
/// uninitialized and must be fully written before extending the traced prefix.
/// # Safety
/// `element` and all reachable descriptor data are immutable and process-long.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __gc__buffer_new(
    element: *const GcValueDescriptor,
    capacity: usize,
) -> *mut u8 {
    let Some(value) = (unsafe { element.as_ref() }) else {
        return ptr::null_mut();
    };
    let Some(element) = (unsafe { value.layout.as_ref() }) else {
        return ptr::null_mut();
    };
    let Some(layout) = (unsafe { layout_for(element) }) else {
        return ptr::null_mut();
    };
    let Some(bytes) = element
        .size
        .checked_mul(capacity)
        .and_then(|size| layout.data_offset.checked_add(size.max(1)))
    else {
        return ptr::null_mut();
    };
    if bytes > isize::MAX as usize {
        return ptr::null_mut();
    }
    let allocation =
        unsafe { alloc_with_zeroed_prefix::<{ size_of::<Header>() }>(bytes, layout.descriptor) };
    unsafe {
        allocation.cast::<Header>().write(Header {
            initialized: AtomicUsize::new(0),
            capacity,
        });
        allocation.add(layout.data_offset)
    }
}

/// Publish a fully initialized contiguous prefix. Logical removal never clears
/// or unpublishes a slot: persistent element references may still access it.
/// Caller synchronization covers structural mutations, as for ordinary handles.
/// # Safety
/// `data` is a live buffer of exactly `element`'s type. Every slot below
/// `initialized` holds a valid value before publication; initialized slots stay
/// valid across all later safepoints. This operation itself cannot collect.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __gc__buffer_publish(
    data: *mut u8,
    element: *const GcValueDescriptor,
    initialized: usize,
) {
    let element = unsafe { &*(*element).layout };
    let offset = data_offset(element).expect("invalid buffer element alignment");
    let header = unsafe { &*data.sub(offset).cast::<Header>() };
    assert!(
        initialized <= header.capacity,
        "initialized buffer extent exceeds capacity"
    );
    if initialized > header.initialized.load(Ordering::Relaxed) {
        header.initialized.store(initialized, Ordering::Release);
    }
}

/// Grow by ordinary element copies. The old allocation and its initialized
/// slots stay intact for interior references. New value payloads are copied
/// independently, while their reference and class targets remain shared.
/// # Safety
/// `old_data` is a live matching buffer (or null for logical length zero).
/// `length` does not exceed its initialized prefix; metadata is process-long.
/// Callers publish their surrounding source frame before this collecting call.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __gc__buffer_grow(
    old_data: *mut u8,
    element: *const GcValueDescriptor,
    length: usize,
    capacity: usize,
) -> *mut u8 {
    let Some(value) = (unsafe { element.as_ref() }) else {
        return ptr::null_mut();
    };
    let Some(descriptor) = (unsafe { value.layout.as_ref() }) else {
        return ptr::null_mut();
    };
    let Some(offset) = data_offset(descriptor) else {
        return ptr::null_mut();
    };
    if length > capacity || (old_data.is_null() && length != 0) {
        return ptr::null_mut();
    }
    if !old_data.is_null() {
        let header = unsafe { &*old_data.sub(offset).cast::<Header>() };
        if length > header.initialized.load(Ordering::Acquire) {
            return ptr::null_mut();
        }
    }
    unsafe {
        with_runtime_root((&old_data as *const *mut u8).cast(), &POINTER, || {
            let new_data = __gc__buffer_new(element, capacity);
            if new_data.is_null() {
                return new_data;
            }
            with_runtime_root((&new_data as *const *mut u8).cast(), &POINTER, || {
                if value.copy_count == 0 {
                    let bytes = length * descriptor.size;
                    if bytes != 0 {
                        ptr::copy_nonoverlapping(old_data, new_data, bytes);
                    }
                    __gc__buffer_publish(new_data, element, length);
                } else {
                    for index in 0..length {
                        let offset = index * descriptor.size;
                        __gc__value_copy(new_data.add(offset), old_data.add(offset), element);
                        __gc__buffer_publish(new_data, element, index + 1);
                    }
                }
            });
            new_data
        })
    }
}

#[cfg(test)]
mod tests;
