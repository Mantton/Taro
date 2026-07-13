//! Runtime support for GC-coordinated weak pointers.
//!
//! A weak cell is itself GC-managed so ordinary Taro values can own and copy
//! its address. Its target is deliberately omitted from the cell descriptor:
//! the collector tracks that edge in a side table and clears it after marking,
//! before the target can be swept.

use std::sync::atomic::{AtomicPtr, Ordering};

use crate::garbage_collector::GcDesc;

#[repr(C)]
struct WeakCell {
    target: AtomicPtr<u8>,
}

static WEAK_CELL_DESC: GcDesc = GcDesc {
    size: std::mem::size_of::<WeakCell>(),
    align: std::mem::align_of::<WeakCell>(),
    ptr_offsets: std::ptr::null(),
    ptr_count: 0,
};

pub(crate) fn cell_desc() -> &'static GcDesc {
    &WEAK_CELL_DESC
}

pub(crate) unsafe fn initialize_cell(cell: *mut u8, target: *const u8) {
    unsafe {
        cell.cast::<WeakCell>().write(WeakCell {
            target: AtomicPtr::new(target.cast_mut()),
        });
    }
}

pub(crate) fn clear_cell(cell: *mut u8) {
    if cell.is_null() {
        return;
    }
    unsafe {
        (*cell.cast::<WeakCell>())
            .target
            .store(std::ptr::null_mut(), Ordering::Release);
    }
}

pub(crate) fn load_cell(cell: *const u8) -> *mut u8 {
    if cell.is_null() {
        return std::ptr::null_mut();
    }
    unsafe { (*cell.cast::<WeakCell>()).target.load(Ordering::Acquire) }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__weak_create(target: *const u8) -> *mut u8 {
    if target.is_null() {
        return std::ptr::null_mut();
    }
    crate::garbage_collector::create_weak_cell(target)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__weak_value(cell: *mut u8) -> *mut u8 {
    crate::garbage_collector::ensure_thread_registered();
    load_cell(cell)
}
