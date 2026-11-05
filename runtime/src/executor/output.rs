//! Task results live in collected storage. A persistent root keeps a completed
//! result alive until delivery or abandonment; no language destructor runs.
use crate::garbage_collector::root_slots::RootLease;
use crate::garbage_collector::{__gc__alloc, GcDesc};
use std::sync::atomic::{AtomicBool, Ordering};

pub(super) struct TaskOutput {
    initialized: AtomicBool,
    data: *mut u8,
    size: usize,
    _root: Option<RootLease>,
}
// The scheduler serializes publication and transfers this root lease between
// workers. The allocation itself stays at a stable address.
unsafe impl Send for TaskOutput {}
impl TaskOutput {
    #[cfg(test)]
    pub(super) fn empty() -> Self {
        unsafe { Self::new(&crate::test_layout::UNIT) }
    }
    /// # Safety
    /// desc is the exact, process-long collected layout of the result. The
    /// zeroed bytes are not a value until a successful poll publishes them.
    pub(super) unsafe fn new(desc: &GcDesc) -> Self {
        let (data, root) = if desc.size == 0 {
            (std::ptr::null_mut(), None)
        } else {
            let data = __gc__alloc(desc.size, desc);
            (data, Some(RootLease::new(data.cast_const())))
        };
        Self {
            initialized: AtomicBool::new(false),
            data,
            size: desc.size,
            _root: root,
        }
    }
    pub(super) fn as_mut_ptr(&mut self) -> *mut u8 {
        self.data
    }
    #[cfg(test)]
    pub(super) fn as_ptr(&self) -> *const u8 {
        self.data.cast_const()
    }
    #[cfg(test)]
    pub(super) fn len(&self) -> usize {
        self.size
    }
    #[cfg(test)]
    pub(super) fn is_empty(&self) -> bool {
        self.size == 0
    }
    pub(super) fn publication(&self) -> &AtomicBool {
        &self.initialized
    }
    /// # Safety
    /// This result is fully initialized. A non-null destination is disjoint,
    /// aligned, writable result storage and becomes initialized by this copy.
    pub(super) unsafe fn copy_into(self, destination: *mut u8) {
        if !destination.is_null() && self.size != 0 {
            assert!(
                self.initialized.load(Ordering::Acquire),
                "unpublished task result"
            );
            unsafe { std::ptr::copy_nonoverlapping(self.data, destination, self.size) };
        }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_layout::{BYTE, noscan};

    #[test]
    fn result_roots_survive_delivery_and_retire_on_abandonment() {
        use crate::{garbage_collector as gc, test_layout::POINTER};
        std::thread::spawn(|| unsafe {
            gc::__gc__thread_enter_managed();
            for deliver in [false, true] {
                let mut output = TaskOutput::new(&POINTER);
                let target = gc::__gc__alloc(1, &BYTE);
                target.write(42);
                output.as_mut_ptr().cast::<*mut u8>().write(target);
                output.publication().store(true, Ordering::Release);
                let probe = gc::create_weak_cell(target);
                gc::with_runtime_root((&raw const probe).cast(), &POINTER, || {
                    gc::__gc__collect();
                    assert!(!crate::gc_weak::load_cell(probe).is_null());
                    if deliver {
                        let mut destination: *mut u8 = std::ptr::null_mut();
                        output.copy_into((&raw mut destination).cast());
                        gc::with_runtime_root((&raw const destination).cast(), &POINTER, || {
                            gc::__gc__collect();
                            assert_eq!(destination.read(), 42);
                        });
                    } else {
                        drop(output);
                    }
                    gc::__gc__collect();
                    assert!(crate::gc_weak::load_cell(probe).is_null());
                });
            }
            gc::__gc__thread_detach();
        })
        .join()
        .unwrap();
    }

    #[test]
    fn pending_storage_preserves_publication_across_rust_transfers() {
        let mut output = unsafe { TaskOutput::new(&BYTE) };
        assert!(!output.publication().load(Ordering::Acquire));
        unsafe { output.as_mut_ptr().write(7) };
        output.publication().store(true, Ordering::Release);
        let address = output.as_ptr();
        let transferred = output;
        assert_eq!(transferred.as_ptr(), address);
        assert!(transferred.initialized.load(Ordering::Acquire));
        let mut destination = 0;
        unsafe { transferred.copy_into(&raw mut destination) };
        assert_eq!(destination, 7);
    }

    #[test]
    fn result_storage_honors_alignment_and_zero_size() {
        let output = unsafe { TaskOutput::new(noscan(64, 64)) };
        assert_eq!(output.as_ptr() as usize % 64, 0);
        assert_eq!(output.len(), 64);
        let unit = TaskOutput::empty();
        assert!(unit.is_empty());
        unit.publication().store(true, Ordering::Release);
        unsafe { unit.copy_into(std::ptr::NonNull::<u8>::dangling().as_ptr()) };
    }

    #[test]
    fn terminal_frame_cleanup_sees_result_already_published() {
        struct Frame {
            publication: *const AtomicBool,
            observed: std::sync::Arc<AtomicBool>,
        }
        unsafe extern "C-unwind" fn poll(_: *mut u8, _: *mut u8, out: *mut u8) -> u8 {
            unsafe { out.write(42) };
            1
        }
        unsafe extern "C-unwind" fn destroy(pointer: *mut u8) {
            let frame = unsafe { Box::from_raw(pointer.cast::<Frame>()) };
            frame.observed.store(
                unsafe { &*frame.publication }.load(Ordering::Acquire),
                Ordering::Release,
            );
        }
        let mut output = unsafe { TaskOutput::new(&BYTE) };
        let observed = std::sync::Arc::new(AtomicBool::new(false));
        let frame = Box::into_raw(Box::new(Frame {
            publication: output.publication(),
            observed: observed.clone(),
        }));
        let handle = crate::task::__rt__async_create(
            frame.cast(),
            poll as *const u8,
            destroy as *const u8,
            1,
        );
        let data = output.as_mut_ptr();
        assert_eq!(
            crate::task::poll_with_output_publication(handle, data, Some(output.publication())),
            1
        );
        assert!(
            observed.load(Ordering::Acquire),
            "cleanup may collect and must see publication"
        );
        assert_eq!(unsafe { output.as_ptr().read() }, 42);
        crate::task::__rt__async_destroy(handle);
    }
}
