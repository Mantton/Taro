//! Collected coroutine storage, rooted until cancellation and native I/O
//! completion draining have finished. Runtime cleanup thunks still release
//! their Rust/backend resources before this root lease ends.
use crate::garbage_collector::root_slots;
use crate::garbage_collector::{__gc__alloc, GcDesc};

/// Allocate a frame in the collected heap. The allocation is zeroed, so
/// fields not yet written trace as null.
///
/// # Safety
/// descriptor is the exact GC layout of the generated frame. The returned
/// unique root lease transfers once into create_owned.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __gc__async_frame_allocate(descriptor: *const GcDesc) -> *mut u8 {
    let size = unsafe { descriptor.as_ref() }
        .unwrap_or_else(|| crate::abi::invalid_metadata("null GC async frame layout"))
        .size;
    if size == 0 {
        crate::abi::invalid_metadata("empty GC async frame layout");
    }
    let frame = __gc__alloc(size, descriptor);
    // Root the frame before any constructor input moves into it. The opaque
    // constructor token is its lease, which becomes the native handle.
    root_slots::acquire(frame.cast_const()).cast()
}

/// Read the data address carried by the opaque constructor root lease.
///
/// # Safety
/// owner is the unique live result of __gc__async_frame_allocate. It has not been
/// consumed by create_owned, and no concurrent mutation or release can occur.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__async_frame_data(owner: *mut u8) -> *mut u8 {
    if owner.is_null() {
        crate::abi::invalid_metadata("null GC async frame owner");
    }
    unsafe { root_slots::rooted(owner.cast()) }
}

#[cfg(test)]
mod tests;
