use super::*;
use crate::{
    garbage_collector as gc,
    gc_layout::{GC_LAYOUT_AGGREGATE, GC_LAYOUT_POINTER, GC_LAYOUT_TAGGED},
};

const fn node(offset: u64, kind: u8, child: u32, count: u32, width: u8) -> GcLayoutNode {
    GcLayoutNode {
        offset,
        stride: 0,
        first_child: child,
        child_count: count,
        kind,
        width,
        reserved: [0; 6],
    }
}

static POINTER_NODES: [GcLayoutNode; 1] = [node(0, GC_LAYOUT_POINTER, 0, 0, 0)];
static POINTER: GcDesc = GcDesc {
    size: 8,
    align: 8,
    nodes: POINTER_NODES.as_ptr(),
    node_count: 1,
};
static WORD: GcDesc = GcDesc {
    size: 8,
    align: 8,
    nodes: ptr::null(),
    node_count: 0,
};

#[repr(C)]
struct Variant {
    tag: u64,
    pointer: *mut u8,
}
static VARIANT_NODES: [GcLayoutNode; 3] = [
    node(0, GC_LAYOUT_TAGGED, 1, 2, 8),
    node(0, GC_LAYOUT_AGGREGATE, 0, 0, 0),
    node(8, GC_LAYOUT_POINTER, 0, 0, 0),
];
static VARIANT: GcDesc = GcDesc {
    size: size_of::<Variant>(),
    align: align_of::<Variant>(),
    nodes: VARIANT_NODES.as_ptr(),
    node_count: VARIANT_NODES.len(),
};
static VALUE: GcValueDescriptor = GcValueDescriptor {
    layout: &VARIANT,
    copies: ptr::null(),
    copy_count: 0,
};

fn managed(operation: impl FnOnce() + Send + 'static) {
    std::thread::spawn(|| {
        gc::__gc__thread_enter_managed();
        operation();
        gc::__gc__thread_detach();
    })
    .join()
    .unwrap();
}

unsafe fn slot(data: *mut u8, layout: &Layout, group: usize, slot: usize) -> *mut Variant {
    unsafe {
        data.add(group * layout.group_stride + 8 + slot * size_of::<Variant>())
            .cast()
    }
}

#[test]
fn group_layout_is_compact_aligned_and_canonical_across_threads() {
    static ENTRY: GcDesc = GcDesc {
        size: 40,
        align: 8,
        nodes: ptr::null(),
        node_count: 0,
    };
    static WIDE: GcDesc = GcDesc {
        size: 32,
        align: 32,
        nodes: ptr::null(),
        node_count: 0,
    };
    let first = unsafe { layout_for(&ENTRY) }.unwrap();
    assert_eq!((first.data_offset, first.group_stride), (8, 328));
    let expected = first as *const Layout as usize;
    let other = std::thread::spawn(|| {
        let layout = unsafe { layout_for(&ENTRY) }.unwrap();
        LOCAL_LAYOUTS.with(|cache| {
            assert!(
                cache
                    .borrow()
                    .contains_key(&(&ENTRY as *const GcDesc as usize))
            )
        });
        layout as *const Layout as usize
    })
    .join()
    .unwrap();
    assert_eq!(expected, other);
    let wide = unsafe { layout_for(&WIDE) }.unwrap();
    assert_eq!((wide.data_offset, wide.group_stride), (32, 288));
}

#[test]
fn only_full_slots_are_traced_and_deleted_payloads_are_reclaimed() {
    for groups in [1, 128, 1024] {
        managed(move || unsafe {
            let layout = layout_for(&VARIANT).unwrap();
            let data = __gc__dictionary_groups_new(&VALUE, groups);
            gc::with_runtime_root((&data as *const *mut u8).cast(), &POINTER, || {
                // Neither empty nor tombstone payloads need even valid enum
                // tags. Exercise both small spans and large allocations.
                for group in 0..groups {
                    for index in 0..8 {
                        slot(data, layout, group, index).write(Variant {
                            tag: u64::MAX,
                            pointer: usize::MAX as *mut u8,
                        });
                    }
                }
                gc::__gc__collect();
                let target = gc::__gc__alloc(8, &WORD);
                target.cast::<u64>().write(42);
                slot(data, layout, groups - 1, 7).write(Variant {
                    tag: 1,
                    pointer: target,
                });
                let controls = data.add((groups - 1) * layout.group_stride).cast::<u64>();
                controls.write((EMPTY_CONTROLS & !(0xff_u64 << 56)) | (0x7f_u64 << 56));
                let probe = gc::create_weak_cell(target);
                gc::with_gc(|heap| heap.add_persistent_root(probe));
                gc::__gc__collect();
                assert_eq!(
                    *(*slot(data, layout, groups - 1, 7)).pointer.cast::<u64>(),
                    42
                );
                assert_eq!(crate::gc_weak::load_cell(probe), target);
                // Clear occupancy only; leave stale reference bytes behind.
                controls.write((EMPTY_CONTROLS & !(0xff_u64 << 56)) | (0xfe_u64 << 56));
                gc::__gc__collect();
                assert!(crate::gc_weak::load_cell(probe).is_null());
                gc::with_gc(|heap| heap.remove_persistent_root(probe));
            });
        });
    }
}

#[test]
fn full_control_bytes_at_every_slot_select_the_corresponding_payload() {
    use crate::gc_layout::{TraceMode, trace_layout};
    let layout = unsafe { layout_for(&VARIANT) }.unwrap();
    let nodes = unsafe {
        std::slice::from_raw_parts(layout.descriptor.nodes, layout.descriptor.node_count)
    };
    // Native storage with the same allocation header avoids collection/test
    // scheduling effects while checking every control-byte position.
    let mut allocation = vec![0_u64; (layout.data_offset + layout.group_stride) / 8];
    let base = allocation.as_mut_ptr().cast::<u8>();
    unsafe {
        base.cast::<usize>().write(1);
        let data = base.add(layout.data_offset);
        for selected in 0..8 {
            for index in 0..8 {
                slot(data, layout, 0, index).write(Variant {
                    tag: if index == selected { 1 } else { u64::MAX },
                    pointer: (0x100 + index) as *mut u8,
                });
            }
            data.cast::<u64>()
                .write(EMPTY_CONTROLS & !(0xff_u64 << (selected * 8)));
            let mut pointers = Vec::new();
            trace_layout(
                base,
                nodes,
                allocation.len() * 8,
                TraceMode::Heap,
                |pointer| pointers.push(pointer as usize),
            )
            .unwrap();
            assert_eq!(pointers, [0x100 + selected]);
        }
        assert!(trace_layout(base, nodes, allocation.len() * 8, TraceMode::Stack, |_| {}).is_err());
        assert!(
            trace_layout(base, nodes, layout.data_offset + 7, TraceMode::Heap, |_| {}).is_err()
        );
    }
}

#[test]
fn invalid_and_overflowing_allocations_are_rejected_and_zero_sized_entries_work() {
    static ZERO: GcDesc = GcDesc {
        size: 0,
        align: 1,
        nodes: ptr::null(),
        node_count: 0,
    };
    static INVALID: GcDesc = GcDesc {
        size: 8,
        align: 3,
        nodes: ptr::null(),
        node_count: 0,
    };
    static ZERO_VALUE: GcValueDescriptor = GcValueDescriptor {
        layout: &ZERO,
        copies: ptr::null(),
        copy_count: 0,
    };
    static INVALID_VALUE: GcValueDescriptor = GcValueDescriptor {
        layout: &INVALID,
        copies: ptr::null(),
        copy_count: 0,
    };
    unsafe {
        assert!(__gc__dictionary_groups_new(ptr::null(), 1).is_null());
        assert!(__gc__dictionary_groups_new(&INVALID_VALUE, 1).is_null());
        assert!(__gc__dictionary_groups_new(&VALUE, usize::MAX).is_null());
    }
    managed(|| unsafe {
        let data = __gc__dictionary_groups_new(&ZERO_VALUE, 1);
        assert!(!data.is_null());
        assert_eq!(*data.cast::<u64>(), EMPTY_CONTROLS);
        // The zero-sized payload is after the control word but still inside
        // the allocation, so a typed zero-sized reference is a valid root.
        let payload = data.add(8);
        gc::with_runtime_root((&payload as *const *mut u8).cast(), &POINTER, || {
            gc::__gc__collect();
            assert_eq!(*data.cast::<u64>(), EMPTY_CONTROLS);
        });
    });
}
