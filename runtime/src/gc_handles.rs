//! Integer handles for managed objects stored by foreign code.
//!
//! C may keep an integer across collections where it may not keep a managed
//! pointer: the pointer is held as a persistent root until the handle is
//! deleted. Ids are never reused, so a stale handle reads as absent instead of
//! reaching another object.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{LazyLock, Mutex};

use crate::garbage_collector::with_gc;

static HANDLES: LazyLock<Mutex<HashMap<usize, usize>>> = LazyLock::new(Default::default);
static NEXT_HANDLE: AtomicUsize = AtomicUsize::new(1);

/// Root `target` and return its handle, or 0 for a null target.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__handle_new(target: *const u8) -> usize {
    if target.is_null() {
        return 0;
    }
    with_gc(|gc| gc.add_persistent_root(target));
    let id = NEXT_HANDLE.fetch_add(1, Ordering::Relaxed);
    HANDLES.lock().unwrap().insert(id, target as usize);
    id
}

/// The rooted target, or null once deleted or for an id never issued.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__handle_value(id: usize) -> *mut u8 {
    HANDLES
        .lock()
        .unwrap()
        .get(&id)
        .map_or(std::ptr::null_mut(), |&target| target as *mut u8)
}

/// Unroot the handle's target; false when it was already deleted.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__handle_delete(id: usize) -> bool {
    let Some(target) = HANDLES.lock().unwrap().remove(&id) else {
        return false;
    };
    with_gc(|gc| gc.remove_persistent_root(target as *const u8));
    true
}
