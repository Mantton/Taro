//! GC-coordinated weak cells, restored from main's explicit Weak API.
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
    nodes: std::ptr::null(),
    node_count: 0,
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

/// Create a non-owning GC cell. The target address escapes for placement, but
/// the cell descriptor deliberately does not trace it as a strong edge.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __gc__weak_create(target: *const u8) -> *mut u8 {
    if target.is_null() {
        return std::ptr::null_mut();
    }
    crate::garbage_collector::create_weak_cell(target)
}

/// Load a strong-reference snapshot. Collection is cooperative: generated code
/// publishes the returned pointer before reaching another safepoint.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__weak_value(cell: *const u8) -> *mut u8 {
    crate::garbage_collector::ensure_thread_registered();
    load_cell(cell)
}

/// Private candidate-runtime oracle, deliberately separate from a language weak
/// reference API. Collection and observation occur in the same native call.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__test_probe_create(target: *const u8) -> *mut u8 {
    crate::garbage_collector::create_weak_cell(target)
}

#[unsafe(no_mangle)]
pub extern "C" fn __gc__test_collect_probe_is_live(probe: *mut u8) -> bool {
    if probe.is_null() {
        return false;
    }
    // Protect the probe independently of the caller map, without protecting its
    // weak target. A source root bug cannot make the oracle read a freed cell.
    crate::garbage_collector::with_gc(|gc| gc.add_persistent_root(probe));
    crate::garbage_collector::__gc__collect();
    let alive = !load_cell(probe).is_null();
    crate::garbage_collector::with_gc(|gc| gc.remove_persistent_root(probe));
    alive
}
