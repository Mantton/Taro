//! Traced erased payloads preserve ordinary concrete value semantics. Copying
//! an erased struct creates independent value storage; references and class
//! objects remain shared. Even a class payload gets its own handle slot, so
//! rebinding that slot cannot change another erased value. No user Clone,
//! destructor, ownership counter or exclusivity check participates in copying.
use crate::{
    dispatch_metadata::TypeMetadata,
    garbage_collector::{__gc__alloc, GcDesc, with_runtime_root},
    gc_layout::{GcLayoutNode, visit_pointer_slots},
};

/// The three-field dispatch prefix is shared with pure conformance lookup.
/// Candidate metadata is immutable and process-long, rather than owned by an
/// erased wrapper. Its identity denotes the exact stored type, including the
/// declared class handle type, independently of an object's dynamic class.
#[repr(C)]
pub(crate) struct GcTypeMetadata {
    pub dispatch: TypeMetadata,
    pub value: *const GcValueDescriptor,
}

unsafe impl Sync for GcTypeMetadata {}

/// Physical value-copy recipe. `layout` traces the complete value. `copies`
/// uses the same aggregate/array/tag nodes, but pointer nodes denote only inline
/// erased headers requiring fresh payload storage. It never follows references
/// or descends into class objects. Empty recipes are an ordinary byte copy.
#[repr(C)]
pub(crate) struct GcValueDescriptor {
    pub layout: *const GcDesc,
    pub copies: *const GcLayoutNode,
    pub copy_count: usize,
}

unsafe impl Sync for GcValueDescriptor {}

/// # Safety
/// `metadata` and its descriptors are valid process-long compiler metadata.
/// `source` holds one initialized concrete value of precisely that type and
/// remains valid throughout this operation. Zero-sized values may use null.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __gc__existential_box(
    source: *const u8,
    metadata: *const GcTypeMetadata,
) -> *mut u8 {
    let metadata = unsafe { &*metadata };
    assert!(
        !metadata.dispatch.identity.is_null(),
        "missing erased type identity"
    );
    let descriptor = unsafe { &*metadata.value };
    let layout = unsafe { &*descriptor.layout };
    unsafe {
        with_runtime_root(source, descriptor.layout, || {
            #[cfg(test)]
            COLLECT_ON_BOX.with(|enabled| {
                if enabled.get() {
                    crate::garbage_collector::__gc__collect();
                }
            });
            let destination = __gc__alloc(layout.size.max(1), descriptor.layout);
            // The byte copy itself cannot collect. Publish valid source bytes
            // before rooting destination and performing nested allocations.
            if layout.size != 0 {
                std::ptr::copy(source, destination, layout.size);
            }
            copy_inline_payloads(destination, descriptor);
            destination
        })
    }
}

/// # Safety
/// Both storage ranges are valid for the descriptor's complete value size.
/// Source is initialized and describes exactly this type. Destination becomes
/// initialized; overlap, including in-place payload duplication, is permitted.
/// Callers root any surrounding values they need across this collecting call.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __gc__value_copy(
    destination: *mut u8,
    source: *const u8,
    descriptor: *const GcValueDescriptor,
) {
    let descriptor = unsafe { &*descriptor };
    let layout = unsafe { &*descriptor.layout };
    // Copying bytes cannot collect. After this copy, destination itself roots
    // every source edge needed while replacing nested erased payloads.
    unsafe {
        if layout.size != 0 {
            std::ptr::copy(source, destination, layout.size);
        }
        copy_inline_payloads(destination, descriptor);
    }
}

unsafe fn copy_inline_payloads(destination: *mut u8, descriptor: &GcValueDescriptor) {
    if descriptor.copy_count == 0 {
        return;
    }
    let layout = unsafe { &*descriptor.layout };
    let copies = unsafe { std::slice::from_raw_parts(descriptor.copies, descriptor.copy_count) };
    unsafe {
        with_runtime_root(destination, descriptor.layout, || {
            visit_pointer_slots(destination, copies, layout.size, |slot| {
                // Every erased header begins with (payload, metadata); witness
                // pointers that follow are immutable and were copied already.
                let slot = slot.cast::<*mut u8>().cast_mut();
                let payload = slot.read();
                let metadata = slot.add(1).cast::<*const GcTypeMetadata>().read();
                let copied = __gc__existential_box(payload, metadata);
                slot.write(copied);
            })
            .expect("invalid erased value-copy layout");
        });
    }
}

#[cfg(test)]
thread_local! {
    pub(crate) static COLLECT_ON_BOX: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
mod tests;
