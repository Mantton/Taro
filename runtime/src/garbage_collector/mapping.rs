use std::ptr::{self, NonNull};

/// Owns the full anonymous mapping, including any padding used to align a GC
/// segment. Access through raw pointers is governed by the collector.
pub(super) struct Mapping {
    base: NonNull<u8>,
    len: usize,
}

impl Mapping {
    pub(super) fn new(len: usize) -> Option<Self> {
        if len == 0 || len > isize::MAX as usize {
            return None;
        }
        // SAFETY: the kernel chooses the address for this private anonymous
        // mapping, which has no backing file.
        let base = unsafe {
            libc::mmap(
                ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANON,
                -1,
                0,
            )
        };
        if base == libc::MAP_FAILED {
            return None;
        }
        let Some(pointer) = NonNull::new(base.cast()) else {
            // SAFETY: mmap succeeded at address zero. Release that mapping
            // because a null address cannot back a Rust allocation.
            unsafe { libc::munmap(base, len) };
            return None;
        };
        Some(Self { base: pointer, len })
    }

    pub(super) fn as_ptr(&self) -> *mut u8 {
        self.base.as_ptr()
    }

    /// # Safety
    /// The range must consist of whole native pages. The caller must ensure
    /// that discarding or reusing those pages cannot affect live objects,
    /// borrows, or concurrent accesses.
    pub(super) unsafe fn advise(&self, offset: usize, len: usize, advice: libc::c_int) -> bool {
        if len == 0 || !offset.checked_add(len).is_some_and(|end| end <= self.len) {
            return false;
        }
        // SAFETY: the checked range is inside this mapping and the caller
        // guarantees that its pages can receive the specified advice.
        unsafe { libc::madvise(self.as_ptr().add(offset).cast(), len, advice) == 0 }
    }
}

impl Drop for Mapping {
    fn drop(&mut self) {
        // SAFETY: this owner holds the original base and length from mmap.
        unsafe { libc::munmap(self.as_ptr().cast(), self.len) };
    }
}

#[cfg(test)]
mod tests {
    use super::Mapping;
    use crate::garbage_collector::os_page_size;

    #[test]
    fn anonymous_mapping_has_zeroed_native_pages_and_bounds_advice() {
        let page_size = os_page_size();
        let mapping = Mapping::new(page_size).expect("map one native page");
        assert_eq!(mapping.as_ptr().addr() % page_size, 0);
        // SAFETY: this fresh mapping owns one initialized, zero-filled page.
        let page = unsafe { std::slice::from_raw_parts(mapping.as_ptr(), page_size) };
        assert!(page.iter().all(|&byte| byte == 0));

        // The out-of-range advice must be rejected before reaching the OS.
        // The immutable borrow above ends at the assertion.
        assert!(!unsafe { mapping.advise(page_size, page_size, libc::MADV_DONTNEED) });
        assert!(Mapping::new(0).is_none());
        assert!(Mapping::new(usize::MAX).is_none());
    }
}
