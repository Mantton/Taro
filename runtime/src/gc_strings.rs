//! Immutable managed bytes for the two-word source string ABI. Native input
//! storage is borrowed for the call; GC input storage is explicitly rooted
//! across the allocating copy because Rust frames have no source stack maps.
use crate::{
    garbage_collector::{__gc__alloc, GcDesc, with_runtime_root},
    gc_layout::{GC_LAYOUT_POINTER, GcLayoutNode},
};
use std::{
    mem::{align_of, size_of},
    ptr,
};

static BYTES: GcDesc = GcDesc {
    size: 0,
    align: 1,
    nodes: ptr::null(),
    node_count: 0,
};
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
    size: size_of::<*const u8>(),
    align: align_of::<*const u8>(),
    nodes: POINTER_NODES.as_ptr(),
    node_count: 1,
};

/// # Safety
/// Nonempty data describes `length` initialized readable bytes. Empty input
/// may be null. The returned bytes are independent, immutable managed storage.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __gc__string_copy(data: *const u8, length: usize) -> *const u8 {
    if length == 0 {
        return ptr::null();
    }
    assert!(
        !data.is_null() && length <= isize::MAX as usize,
        "invalid string byte range"
    );
    unsafe {
        with_runtime_root((&data as *const *const u8).cast(), &POINTER, || {
            let destination = __gc__alloc(length, &BYTES);
            ptr::copy_nonoverlapping(data, destination, length);
            destination.cast_const()
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::garbage_collector as gc;

    #[test]
    fn copies_bytes_preserves_interior_roots_and_reclaims_dead_strings() {
        std::thread::spawn(|| unsafe {
            gc::__gc__thread_enter_managed();
            let mut input = *b"abcdef";
            let data = __gc__string_copy(input.as_ptr(), input.len());
            input.fill(0);
            let interior = data.add(2);
            let probe = with_runtime_root((&data as *const *const u8).cast(), &POINTER, || {
                gc::create_weak_cell(data)
            });
            with_runtime_root((&probe as *const *mut u8).cast(), &POINTER, || {
                with_runtime_root((&interior as *const *const u8).cast(), &POINTER, || {
                    gc::__gc__collect();
                    assert!(!crate::gc_weak::load_cell(probe).is_null());
                    assert_eq!(std::slice::from_raw_parts(interior, 2), b"cd");
                });
                // No outer source root remains. The allocating copy must root
                // the interior input itself before servicing this request.
                gc::__gc__test_request_collection();
                let copy = __gc__string_copy(interior, 2);
                with_runtime_root((&copy as *const *const u8).cast(), &POINTER, || {
                    gc::__gc__collect();
                    assert!(crate::gc_weak::load_cell(probe).is_null());
                    assert_eq!(std::slice::from_raw_parts(copy, 2), b"cd");
                });
            });
            assert!(__gc__string_copy(ptr::null(), 0).is_null());
            gc::__gc__thread_detach();
        })
        .join()
        .unwrap();
    }
}
