//! Word-atomic copies for values that hold pointers.
//!
//! Codegen lowers large pointer-bearing aggregate copies to LLVM's
//! element-wise unordered-atomic memmove, whose libcall lives here: every
//! pointer-aligned word moves with one access, so a racing reader never sees
//! a torn pointer. Words are independent; the copy as a whole is not atomic.
use std::sync::atomic::{AtomicU64, Ordering};

/// # Safety
/// `destination` and `source` are 8-byte aligned and valid for `len` bytes,
/// and `len` is a multiple of 8. The ranges may overlap.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __llvm_memmove_element_unordered_atomic_8(
    destination: *mut u8,
    source: *const u8,
    len: usize,
) {
    let words = len / 8;
    let destination = destination.cast::<AtomicU64>();
    let source = source.cast::<AtomicU64>();
    let copy = |index: usize| unsafe {
        let word = (*source.add(index)).load(Ordering::Relaxed);
        (*destination.add(index)).store(word, Ordering::Relaxed);
    };
    // Copy away from the overlap so no source word is overwritten first.
    if (destination as usize) <= (source as usize) {
        (0..words).for_each(copy);
    } else {
        (0..words).rev().for_each(copy);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn copies_whole_words_in_either_overlap_direction() {
        let mut words: Vec<u64> = (0..8).collect();
        let base = words.as_mut_ptr().cast::<u8>();
        unsafe { __llvm_memmove_element_unordered_atomic_8(base.add(8), base, 48) };
        assert_eq!(words, [0, 0, 1, 2, 3, 4, 5, 7]);
        unsafe { __llvm_memmove_element_unordered_atomic_8(base, base.add(16), 48) };
        assert_eq!(words, [1, 2, 3, 4, 5, 7, 5, 7]);
    }
}
