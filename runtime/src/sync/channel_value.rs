//! Queued messages are independent GC value copies. A persistent root covers
//! staging, publication and receipt; rejecting a staged copy leaves its source
//! unchanged. The collector reclaims abandoned messages without callbacks.
use crate::{
    garbage_collector::{__gc__alloc, with_gc, with_runtime_root},
    gc_existentials::{__gc__value_copy, GcValueDescriptor},
};
use std::sync::Arc;

pub(super) struct ChannelLayout {
    pub(super) size: usize,
    element: *const GcValueDescriptor,
}
// Immutable compiler-produced tables have process lifetime.
unsafe impl Send for ChannelLayout {}
unsafe impl Sync for ChannelLayout {}
impl ChannelLayout {
    /// # Safety
    /// element is the process-long compiler descriptor of the channel's type.
    pub(super) unsafe fn new(element: *const GcValueDescriptor) -> Option<Arc<Self>> {
        let layout = unsafe { element.as_ref()?.layout.as_ref() }?;
        if !layout.align.is_power_of_two()
            || !layout.size.is_multiple_of(layout.align)
            || std::alloc::Layout::from_size_align(layout.size, layout.align).is_err()
        {
            return None;
        }
        Some(Arc::new(Self {
            size: layout.size,
            element,
        }))
    }
}

pub(super) struct QueuedValue {
    data: *mut u8,
    size: usize,
    committed: bool,
}
// Channel locking serializes publication/removal. Removed messages are private
// to the receiving thread until their value is copied to destination storage.
unsafe impl Send for QueuedValue {}
impl QueuedValue {
    /// # Safety
    /// source is an initialized value of layout's exact type and remains valid
    /// while the collected copy is made. A zero-sized source may be null.
    pub(super) unsafe fn prepare(layout: &ChannelLayout, source: *const u8) -> Result<Self, i32> {
        if layout.size != 0 && source.is_null() {
            return Err(libc::EINVAL);
        }
        unsafe {
            with_runtime_root(source, (*layout.element).layout, || {
                let data = if layout.size == 0 {
                    std::ptr::null_mut()
                } else {
                    __gc__alloc(layout.size, (*layout.element).layout)
                };
                // Own the root before value copying, which can allocate or
                // unwind. Its guard also retires the root on a failed copy.
                let message = Self {
                    data,
                    size: layout.size,
                    committed: false,
                };
                if !data.is_null() {
                    with_gc(|gc| gc.add_persistent_root(data.cast_const()));
                    __gc__value_copy(data, source, layout.element);
                }
                Ok(message)
            })
        }
    }
    pub(super) fn commit(&mut self) {
        self.committed = true;
    }
    /// # Safety
    /// destination is disjoint, aligned, writable element storage. No callback
    /// intervenes between the byte copy and retiring the message's root lease.
    pub(super) unsafe fn move_into(&mut self, destination: *mut u8) {
        assert!(
            self.committed,
            "only committed queue messages may be received"
        );
        if self.size != 0 {
            unsafe { std::ptr::copy_nonoverlapping(self.data, destination, self.size) };
        }
        self.committed = false;
    }
}
impl Drop for QueuedValue {
    fn drop(&mut self) {
        if !self.data.is_null() {
            with_gc(|gc| gc.remove_persistent_root(self.data.cast_const()));
        }
    }
}

#[cfg(test)]
mod tests;
