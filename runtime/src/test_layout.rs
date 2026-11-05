//! Process-long layouts for Rust integration tests. Source layouts are emitted
//! by the compiler; test fixtures must obey the same descriptor lifetime.
use crate::{garbage_collector::GcDesc, gc_existentials::GcValueDescriptor};
pub(crate) static UNIT: GcDesc = GcDesc {
    size: 0,
    align: 1,
    nodes: std::ptr::null(),
    node_count: 0,
};
pub(crate) static BYTE: GcDesc = GcDesc {
    size: 1,
    align: 1,
    nodes: std::ptr::null(),
    node_count: 0,
};
pub(crate) fn noscan(size: usize, align: usize) -> &'static GcDesc {
    Box::leak(Box::new(GcDesc {
        size,
        align,
        nodes: std::ptr::null(),
        node_count: 0,
    }))
}
pub(crate) fn value<T>() -> &'static GcValueDescriptor {
    Box::leak(Box::new(GcValueDescriptor {
        layout: noscan(size_of::<T>(), align_of::<T>()),
        copies: std::ptr::null(),
        copy_count: 0,
    }))
}
static POINTER_NODES: [crate::gc_layout::GcLayoutNode; 1] = [crate::gc_layout::GcLayoutNode {
    offset: 0,
    stride: 0,
    first_child: 0,
    child_count: 0,
    kind: crate::gc_layout::GC_LAYOUT_POINTER,
    width: 0,
    reserved: [0; 6],
}];
pub(crate) static POINTER: GcDesc = GcDesc {
    size: size_of::<*mut u8>(),
    align: align_of::<*mut u8>(),
    nodes: POINTER_NODES.as_ptr(),
    node_count: 1,
};
pub(crate) static POINTER_VALUE: GcValueDescriptor = GcValueDescriptor {
    layout: &POINTER,
    copies: std::ptr::null(),
    copy_count: 0,
};
