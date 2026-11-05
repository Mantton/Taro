use super::*;
use crate::{garbage_collector as gc, gc_layout::*};
use std::{
    mem::{align_of, size_of},
    ptr,
};

const fn node(offset: u64, kind: u8, first_child: u32, child_count: u32) -> GcLayoutNode {
    GcLayoutNode {
        offset,
        stride: 0,
        first_child,
        child_count,
        kind,
        width: 0,
        reserved: [0; 6],
    }
}
static IDENTITY: u8 = 1;
static WORD: GcDesc = GcDesc {
    size: 8,
    align: 8,
    nodes: ptr::null(),
    node_count: 0,
};
static POINTER_NODE: [GcLayoutNode; 1] = [node(0, GC_LAYOUT_POINTER, 0, 0)];
static POINTER: GcDesc = GcDesc {
    size: size_of::<usize>(),
    align: align_of::<usize>(),
    nodes: POINTER_NODE.as_ptr(),
    node_count: 1,
};
const fn metadata(value: &'static GcValueDescriptor) -> GcTypeMetadata {
    GcTypeMetadata {
        dispatch: TypeMetadata {
            entries: ptr::null(),
            len: 0,
            identity: &IDENTITY,
        },
        value,
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
struct Header {
    data: *mut u8,
    metadata: *const GcTypeMetadata,
}
static HEADER: GcDesc = GcDesc {
    size: size_of::<Header>(),
    align: align_of::<Header>(),
    nodes: POINTER_NODE.as_ptr(),
    node_count: 1,
};
#[repr(C)]
#[derive(Clone, Copy)]
struct Record {
    scalar: u64,
    shared: *mut u64,
}
static RECORD_NODE: [GcLayoutNode; 1] = [node(8, GC_LAYOUT_POINTER, 0, 0)];
static RECORD: GcDesc = GcDesc {
    size: size_of::<Record>(),
    align: align_of::<Record>(),
    nodes: RECORD_NODE.as_ptr(),
    node_count: 1,
};
static RECORD_COPY: GcValueDescriptor = GcValueDescriptor {
    layout: &RECORD,
    copies: ptr::null(),
    copy_count: 0,
};
static RECORD_META: GcTypeMetadata = metadata(&RECORD_COPY);
static PAIR_TRACE: [GcLayoutNode; 2] = [
    GcLayoutNode {
        stride: size_of::<Header>() as u64,
        ..node(0, GC_LAYOUT_REPEAT, 1, 2)
    },
    node(0, GC_LAYOUT_POINTER, 0, 0),
];
static PAIR: GcDesc = GcDesc {
    size: size_of::<[Header; 2]>(),
    align: align_of::<Header>(),
    nodes: PAIR_TRACE.as_ptr(),
    node_count: 2,
};
static PAIR_COPY: GcValueDescriptor = GcValueDescriptor {
    layout: &PAIR,
    copies: PAIR_TRACE.as_ptr(),
    copy_count: 2,
};
static PAIR_META: GcTypeMetadata = metadata(&PAIR_COPY);

// These tests assert exact reclamation in one shared heap. Running them in
// parallel lets one test's stale stack or root words falsely retain another's
// probe target (5 in 100 module runs), which the non-moving collector permits.
static MANAGED_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn managed(operation: impl FnOnce() + Send + 'static) {
    let _serial = MANAGED_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    std::thread::spawn(|| {
        gc::__gc__thread_enter_managed();
        // Every erased allocation forces a rendezvous, not just a normal
        // allocator fast path. Stack sources and partial copy results must
        // keep their managed references alive without compiler root maps.
        COLLECT_ON_BOX.with(|enabled| enabled.set(true));
        operation();
        COLLECT_ON_BOX.with(|enabled| enabled.set(false));
        gc::__gc__thread_detach();
    })
    .join()
    .unwrap();
}

#[test]
fn nested_erased_copies_separate_values_and_keep_reference_targets_live() {
    managed(|| unsafe {
        let shared = gc::__gc__alloc(8, &WORD).cast::<u64>();
        shared.write(7);
        with_runtime_root((&shared as *const *mut u64).cast(), &POINTER, || {
            let record = Record { scalar: 11, shared };
            let original = Header {
                data: __gc__existential_box((&record as *const Record).cast(), &RECORD_META),
                metadata: &RECORD_META,
            };
            with_runtime_root((&original as *const Header).cast(), &HEADER, || {
                let pair = [original; 2];
                let cloned =
                    __gc__existential_box(pair.as_ptr().cast(), &PAIR_META).cast::<Header>();
                with_runtime_root((&cloned as *const *mut Header).cast(), &POINTER, || {
                    gc::__gc__collect();
                    let first = cloned.read();
                    let second = cloned.add(1).read();
                    assert_ne!(first.data, original.data);
                    assert_ne!(first.data, second.data);
                    assert_eq!(first.metadata, &RECORD_META as *const GcTypeMetadata);
                    let record_copy = first.data.cast::<Record>();
                    (*record_copy).scalar = 42;
                    assert_eq!((*original.data.cast::<Record>()).scalar, 11);
                    assert_eq!((*second.data.cast::<Record>()).scalar, 11);
                    assert_eq!((*record_copy).shared, shared);
                    (*(*record_copy).shared) = 99;
                    assert_eq!(*(*original.data.cast::<Record>()).shared, 99);
                    // The in-place path is used for copies already staged in a
                    // destination local; it must still make fresh payloads.
                    let old_first = first.data;
                    __gc__value_copy(cloned.cast(), cloned.cast(), &PAIR_COPY);
                    assert_ne!((*cloned).data, old_first);
                    assert_eq!((*(*cloned).data.cast::<Record>()).scalar, 42);
                });
            });
        });
    });
}

#[test]
fn class_handle_shells_are_independent_while_object_identity_is_shared() {
    static CLASS_COPY: GcValueDescriptor = GcValueDescriptor {
        layout: &POINTER,
        copies: ptr::null(),
        copy_count: 0,
    };
    static CLASS_META: GcTypeMetadata = metadata(&CLASS_COPY);
    managed(|| unsafe {
        let object = gc::__gc__alloc(8, &WORD);
        object.cast::<u64>().write(23);
        let first = Header {
            data: __gc__existential_box((&object as *const *mut u8).cast(), &CLASS_META),
            metadata: &CLASS_META,
        };
        with_runtime_root((&first as *const Header).cast(), &HEADER, || {
            let mut second = first;
            __gc__value_copy(
                (&mut second as *mut Header).cast(),
                (&first as *const Header).cast(),
                &GcValueDescriptor {
                    layout: &HEADER,
                    copies: POINTER_NODE.as_ptr(),
                    copy_count: 1,
                },
            );
            with_runtime_root((&second as *const Header).cast(), &HEADER, || {
                assert_ne!(first.data, second.data);
                assert_eq!(first.data.cast::<*mut u8>().read(), object);
                assert_eq!(second.data.cast::<*mut u8>().read(), object);
                let replacement = gc::__gc__alloc(8, &WORD);
                replacement.cast::<u64>().write(77);
                second.data.cast::<*mut u8>().write(replacement);
                gc::__gc__collect();
                assert_eq!(first.data.cast::<*mut u8>().read(), object);
                assert_eq!(*object.cast::<u64>(), 23);
                assert_eq!(*replacement.cast::<u64>(), 77);
            });
        });
    });
}

#[test]
fn inactive_variant_bytes_are_never_copied_as_erased_headers() {
    static NODES: [GcLayoutNode; 3] = [
        GcLayoutNode {
            width: 1,
            ..node(0, GC_LAYOUT_TAGGED, 1, 2)
        },
        node(0, GC_LAYOUT_AGGREGATE, 0, 0),
        node(8, GC_LAYOUT_POINTER, 0, 0),
    ];
    static ENUM: GcDesc = GcDesc {
        size: 24,
        align: 8,
        nodes: NODES.as_ptr(),
        node_count: 3,
    };
    static ENUM_COPY: GcValueDescriptor = GcValueDescriptor {
        layout: &ENUM,
        copies: NODES.as_ptr(),
        copy_count: 3,
    };
    static ENUM_META: GcTypeMetadata = metadata(&ENUM_COPY);
    managed(|| unsafe {
        // Nonzero inactive bytes would be invalid metadata if visited.
        let source = [0u64, u64::MAX, u64::MAX];
        let cloned = __gc__existential_box(source.as_ptr().cast(), &ENUM_META);
        with_runtime_root((&cloned as *const *mut u8).cast(), &POINTER, || {
            gc::__gc__collect();
            assert_eq!(*cloned.cast::<[u64; 3]>(), source);
        });
    });
}

#[test]
fn zero_sized_payloads_have_real_distinct_storage() {
    static EMPTY: GcDesc = GcDesc {
        size: 0,
        align: 1,
        nodes: ptr::null(),
        node_count: 0,
    };
    static EMPTY_COPY: GcValueDescriptor = GcValueDescriptor {
        layout: &EMPTY,
        copies: ptr::null(),
        copy_count: 0,
    };
    static EMPTY_META: GcTypeMetadata = metadata(&EMPTY_COPY);
    managed(|| unsafe {
        let first = __gc__existential_box(ptr::null(), &EMPTY_META);
        with_runtime_root((&first as *const *mut u8).cast(), &POINTER, || {
            let second = __gc__existential_box(ptr::null(), &EMPTY_META);
            assert!(!first.is_null());
            assert!(!second.is_null());
            assert_ne!(first, second);
        });
    });
}

#[test]
fn runtime_roots_protect_stack_values_and_leave_no_root_after_unwind() {
    managed(|| unsafe {
        let target = gc::__gc__alloc(8, &WORD);
        target.cast::<u64>().write(51);
        let probe = gc::create_weak_cell(target);
        gc::with_gc(|heap| heap.add_persistent_root(probe));
        let unwound = std::panic::catch_unwind(|| {
            with_runtime_root((&target as *const *mut u8).cast(), &POINTER, || {
                gc::__gc__collect();
                assert_eq!(crate::gc_weak::load_cell(probe), target);
                panic!("leave runtime root scope");
            });
        });
        assert!(unwound.is_err());
        gc::__gc__collect();
        assert!(crate::gc_weak::load_cell(probe).is_null());
        gc::with_gc(|heap| heap.remove_persistent_root(probe));
    });
}
