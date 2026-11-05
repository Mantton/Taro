use super::*;
use crate::{
    garbage_collector as gc,
    gc_existentials::{__gc__existential_box, GcTypeMetadata},
    gc_layout::*,
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
static WORD: GcDesc = GcDesc {
    size: 8,
    align: 8,
    nodes: ptr::null(),
    node_count: 0,
};
static WORD_VALUE: GcValueDescriptor = GcValueDescriptor {
    layout: &WORD,
    copies: ptr::null(),
    copy_count: 0,
};
static SLOT: GcValueDescriptor = GcValueDescriptor {
    layout: &POINTER,
    copies: ptr::null(),
    copy_count: 0,
};

#[test]
fn layout_cache_keeps_canonical_metadata_after_thread_exit() {
    static WIDE: GcDesc = GcDesc {
        size: 32,
        align: 32,
        nodes: ptr::null(),
        node_count: 0,
    };
    let barrier = std::sync::Arc::new(std::sync::Barrier::new(4));
    let workers: Vec<_> = (0..4)
        .map(|_| {
            let barrier = barrier.clone();
            std::thread::spawn(move || {
                barrier.wait();
                let mut result = Vec::new();
                for element in [&WORD, &POINTER, &WIDE] {
                    let first = unsafe { layout_for(element) }.unwrap();
                    for _ in 0..16 {
                        assert!(ptr::eq(first, unsafe { layout_for(element) }.unwrap()));
                    }
                    result.push((first as *const Layout as usize, first.data_offset));
                }
                result
            })
        })
        .collect();
    let results: Vec<_> = workers
        .into_iter()
        .map(|worker| worker.join().unwrap())
        .collect();
    assert!(results.iter().all(|result| result == &results[0]));
    assert_eq!(results[0][2].1, 32);
    for (index, element) in [&WORD, &POINTER, &WIDE].into_iter().enumerate() {
        let layout = unsafe { layout_for(element) }.unwrap();
        assert_eq!(layout as *const Layout as usize, results[0][index].0);
    }
}

#[test]
fn layout_lookup_falls_back_after_cache_tls_teardown() {
    use std::sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    };
    struct LateLookup(Arc<AtomicBool>);
    impl Drop for LateLookup {
        fn drop(&mut self) {
            let destroyed = LOCAL_LAYOUTS.try_with(|_| ()).is_err();
            let layout = unsafe { layout_for(&WORD) }.unwrap();
            self.0.store(
                destroyed && layout.data_offset == size_of::<Header>(),
                Ordering::Release,
            );
        }
    }
    thread_local! {
        static LATE: RefCell<Option<LateLookup>> = const { RefCell::new(None) };
    }
    let completed = Arc::new(AtomicBool::new(false));
    let result = completed.clone();
    std::thread::spawn(move || {
        // TLS destructors run in reverse initialization order: the optional
        // layout cache is gone before this native destructor asks for a layout.
        LATE.with(|slot| *slot.borrow_mut() = Some(LateLookup(result)));
        assert!(unsafe { layout_for(&WORD) }.is_some());
    })
    .join()
    .unwrap();
    assert!(completed.load(Ordering::Acquire));
}
#[repr(C)]
#[derive(Clone, Copy)]
struct Variant {
    tag: u64,
    pointer: *mut u8,
}
static VARIANT_NODES: [GcLayoutNode; 3] = [
    GcLayoutNode {
        width: 8,
        ..node(0, GC_LAYOUT_TAGGED, 1, 2)
    },
    node(0, GC_LAYOUT_AGGREGATE, 0, 0),
    node(8, GC_LAYOUT_POINTER, 0, 0),
];
static VARIANT: GcDesc = GcDesc {
    size: size_of::<Variant>(),
    align: align_of::<Variant>(),
    nodes: VARIANT_NODES.as_ptr(),
    node_count: 3,
};
static VARIANT_VALUE: GcValueDescriptor = GcValueDescriptor {
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
unsafe fn header(data: *mut u8, descriptor: &GcDesc) -> &'static Header {
    unsafe { &*data.sub(data_offset(descriptor).unwrap()).cast::<Header>() }
}

#[test]
fn only_initialized_slots_are_traced_for_small_and_large_allocations() {
    for capacity in [4, 2048] {
        managed(move || unsafe {
            let data = __gc__buffer_new(&VARIANT_VALUE, capacity).cast::<Variant>();
            with_runtime_root((&data as *const *mut Variant).cast(), &POINTER, || {
                // Poison capacity before even the first publication. Scanning
                // zero/default values would miss this invalid live-tag error.
                for index in 0..capacity {
                    data.add(index).write(Variant {
                        tag: u64::MAX,
                        pointer: usize::MAX as *mut u8,
                    });
                }
                gc::__gc__collect();
                let target = gc::__gc__alloc(8, &WORD);
                target.cast::<u64>().write(42);
                data.write(Variant {
                    tag: 1,
                    pointer: target,
                });
                __gc__buffer_publish(data.cast(), &VARIANT_VALUE, 1);
                gc::__gc__collect();
                assert_eq!(*(*data).pointer.cast::<u64>(), 42);
                assert_eq!(
                    header(data.cast(), &VARIANT)
                        .initialized
                        .load(Ordering::Acquire),
                    1
                );
            });
        });
    }
}

#[test]
fn removal_does_not_invalidate_references_or_unpublish_storage() {
    managed(|| unsafe {
        let data = __gc__buffer_new(&SLOT, 2).cast::<*mut u8>();
        let (target, probe) =
            with_runtime_root((&data as *const *mut *mut u8).cast(), &POINTER, || {
                let target = gc::__gc__alloc(8, &WORD);
                target.cast::<u64>().write(31);
                data.write(target);
                __gc__buffer_publish(data.cast(), &SLOT, 1);
                let probe = gc::create_weak_cell(target);
                gc::with_gc(|heap| heap.add_persistent_root(probe));
                (target, probe)
            });
        let interior = data.cast::<u8>();
        with_runtime_root((&interior as *const *mut u8).cast(), &POINTER, || {
            __gc__buffer_publish(data.cast(), &SLOT, 0);
            gc::__gc__collect();
            assert_eq!(
                header(data.cast(), &POINTER)
                    .initialized
                    .load(Ordering::Acquire),
                1
            );
            assert_eq!(crate::gc_weak::load_cell(probe), target);
            assert_eq!(*(*data).cast::<u64>(), 31);
        });
        gc::__gc__collect();
        assert!(crate::gc_weak::load_cell(probe).is_null());
        gc::with_gc(|heap| heap.remove_persistent_root(probe));
    });
}

#[test]
fn growth_keeps_old_interior_addresses_valid_and_copies_only_logical_values() {
    managed(|| unsafe {
        let data = __gc__buffer_new(&SLOT, 3).cast::<*mut u8>();
        let old_slot = with_runtime_root((&data as *const *mut *mut u8).cast(), &POINTER, || {
            for index in 0..3 {
                let target = gc::__gc__alloc(8, &WORD);
                target.cast::<u64>().write(10 + index as u64);
                data.add(index).write(target);
                __gc__buffer_publish(data.cast(), &SLOT, index + 1);
            }
            data.add(2)
        });
        // Keep only the old element address, rather than the collection's
        // backing-data handle, while growth allocates another buffer.
        with_runtime_root((&old_slot as *const *mut *mut u8).cast(), &POINTER, || {
            let grown = __gc__buffer_grow(data.cast(), &SLOT, 1, 8).cast::<*mut u8>();
            with_runtime_root((&grown as *const *mut *mut u8).cast(), &POINTER, || {
                gc::__gc__collect();
                assert_ne!(data, grown);
                assert_eq!(*(*grown).cast::<u64>(), 10);
                assert_eq!(*(*old_slot).cast::<u64>(), 12);
                assert_eq!(
                    header(grown.cast(), &POINTER)
                        .initialized
                        .load(Ordering::Acquire),
                    1
                );
                let replacement = gc::__gc__alloc(8, &WORD);
                replacement.cast::<u64>().write(99);
                grown.write(replacement);
                assert_eq!(*(*data).cast::<u64>(), 10);
                assert_eq!(*(*grown).cast::<u64>(), 99);
            });
        });
    });
}

#[test]
fn growth_uses_ordinary_erased_value_copies() {
    #[repr(C)]
    struct Erased {
        data: *mut u8,
        metadata: *const GcTypeMetadata,
    }
    static ERASED_LAYOUT: GcDesc = GcDesc {
        size: size_of::<Erased>(),
        align: align_of::<Erased>(),
        nodes: POINTER_NODE.as_ptr(),
        node_count: 1,
    };
    static ERASED: GcValueDescriptor = GcValueDescriptor {
        layout: &ERASED_LAYOUT,
        copies: POINTER_NODE.as_ptr(),
        copy_count: 1,
    };
    static ID: u8 = 1;
    static META: GcTypeMetadata = GcTypeMetadata {
        dispatch: crate::dispatch_metadata::TypeMetadata {
            entries: ptr::null(),
            len: 0,
            identity: &ID,
        },
        value: &WORD_VALUE,
    };
    managed(|| unsafe {
        let data = __gc__buffer_new(&ERASED, 1).cast::<Erased>();
        with_runtime_root((&data as *const *mut Erased).cast(), &POINTER, || {
            let scalar = 17u64;
            data.write(Erased {
                data: __gc__existential_box((&scalar as *const u64).cast(), &META),
                metadata: &META,
            });
            __gc__buffer_publish(data.cast(), &ERASED, 1);
            crate::gc_existentials::COLLECT_ON_BOX.with(|enabled| enabled.set(true));
            let grown = __gc__buffer_grow(data.cast(), &ERASED, 1, 2).cast::<Erased>();
            crate::gc_existentials::COLLECT_ON_BOX.with(|enabled| enabled.set(false));
            with_runtime_root((&grown as *const *mut Erased).cast(), &POINTER, || {
                gc::__gc__collect();
                assert_ne!((*data).data, (*grown).data);
                (*grown).data.cast::<u64>().write(90);
                assert_eq!(*(*data).data.cast::<u64>(), 17);
            });
        });
    });
}

#[test]
fn empty_zero_sized_overaligned_and_invalid_capacities_are_handled() {
    static EMPTY: GcDesc = GcDesc {
        size: 0,
        align: 1,
        nodes: ptr::null(),
        node_count: 0,
    };
    static EMPTY_VALUE: GcValueDescriptor = GcValueDescriptor {
        layout: &EMPTY,
        copies: ptr::null(),
        copy_count: 0,
    };
    static ALIGNED: GcDesc = GcDesc {
        size: 64,
        align: 64,
        nodes: ptr::null(),
        node_count: 0,
    };
    static ALIGNED_VALUE: GcValueDescriptor = GcValueDescriptor {
        layout: &ALIGNED,
        copies: ptr::null(),
        copy_count: 0,
    };
    managed(|| unsafe {
        for (value, capacity) in [
            (&EMPTY_VALUE, usize::MAX),
            (&WORD_VALUE, 0),
            (&ALIGNED_VALUE, 2),
        ] {
            let data = __gc__buffer_new(value, capacity);
            assert!(!data.is_null());
            assert_eq!(data as usize % (*value.layout).align, 0);
            with_runtime_root((&data as *const *mut u8).cast(), &POINTER, || {
                gc::__gc__collect()
            });
        }
        assert!(__gc__buffer_new(&WORD_VALUE, usize::MAX).is_null());
        assert!(__gc__buffer_grow(ptr::null_mut(), &WORD_VALUE, 1, 2).is_null());
        assert!(__gc__buffer_grow(ptr::null_mut(), &WORD_VALUE, 2, 1).is_null());
        let data = __gc__buffer_new(&WORD_VALUE, 2);
        assert!(
            __gc__buffer_grow(data, &WORD_VALUE, 1, 4).is_null(),
            "uninitialized values cannot be grown"
        );
    });
}
