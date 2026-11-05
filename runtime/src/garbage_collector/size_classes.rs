//! Dense allocation classes through 8 KiB, using Go 1.26.2's sizes and span
//! geometry. Larger allocations retain Taro's whole-page path.
//!
//! Tables adapted from Go's internal/runtime/gc/sizeclasses.go.
//! Copyright 2009 The Go Authors. BSD license: runtime/GO-LICENSE.

#[derive(Clone, Copy)]
pub(super) struct SizeClass {
    pub size: usize,
    pub pages: usize,
}

pub(super) const CLASSES: [SizeClass; 51] = [
    SizeClass { size: 8, pages: 1 },
    SizeClass { size: 16, pages: 1 },
    SizeClass { size: 24, pages: 1 },
    SizeClass { size: 32, pages: 1 },
    SizeClass { size: 48, pages: 1 },
    SizeClass { size: 64, pages: 1 },
    SizeClass { size: 80, pages: 1 },
    SizeClass { size: 96, pages: 1 },
    SizeClass {
        size: 112,
        pages: 1,
    },
    SizeClass {
        size: 128,
        pages: 1,
    },
    SizeClass {
        size: 144,
        pages: 1,
    },
    SizeClass {
        size: 160,
        pages: 1,
    },
    SizeClass {
        size: 176,
        pages: 1,
    },
    SizeClass {
        size: 192,
        pages: 1,
    },
    SizeClass {
        size: 208,
        pages: 1,
    },
    SizeClass {
        size: 224,
        pages: 1,
    },
    SizeClass {
        size: 240,
        pages: 1,
    },
    SizeClass {
        size: 256,
        pages: 1,
    },
    SizeClass {
        size: 288,
        pages: 1,
    },
    SizeClass {
        size: 320,
        pages: 1,
    },
    SizeClass {
        size: 352,
        pages: 1,
    },
    SizeClass {
        size: 384,
        pages: 1,
    },
    SizeClass {
        size: 416,
        pages: 1,
    },
    SizeClass {
        size: 448,
        pages: 1,
    },
    SizeClass {
        size: 480,
        pages: 1,
    },
    SizeClass {
        size: 512,
        pages: 1,
    },
    SizeClass {
        size: 576,
        pages: 1,
    },
    SizeClass {
        size: 640,
        pages: 1,
    },
    SizeClass {
        size: 704,
        pages: 1,
    },
    SizeClass {
        size: 768,
        pages: 1,
    },
    SizeClass {
        size: 896,
        pages: 1,
    },
    SizeClass {
        size: 1024,
        pages: 1,
    },
    SizeClass {
        size: 1152,
        pages: 1,
    },
    SizeClass {
        size: 1280,
        pages: 1,
    },
    SizeClass {
        size: 1408,
        pages: 2,
    },
    SizeClass {
        size: 1536,
        pages: 1,
    },
    SizeClass {
        size: 1792,
        pages: 2,
    },
    SizeClass {
        size: 2048,
        pages: 1,
    },
    SizeClass {
        size: 2304,
        pages: 2,
    },
    SizeClass {
        size: 2688,
        pages: 1,
    },
    SizeClass {
        size: 3072,
        pages: 3,
    },
    SizeClass {
        size: 3200,
        pages: 2,
    },
    SizeClass {
        size: 3456,
        pages: 3,
    },
    SizeClass {
        size: 4096,
        pages: 1,
    },
    SizeClass {
        size: 4864,
        pages: 3,
    },
    SizeClass {
        size: 5376,
        pages: 2,
    },
    SizeClass {
        size: 6144,
        pages: 3,
    },
    SizeClass {
        size: 6528,
        pages: 4,
    },
    SizeClass {
        size: 6784,
        pages: 5,
    },
    SizeClass {
        size: 6912,
        pages: 6,
    },
    SizeClass {
        size: 8192,
        pages: 1,
    },
];

// Like Go, use 8-byte lookup buckets through 1 KiB and 128-byte buckets above
// it. These are compile-time tables; the common allocation path is one lookup.
const fn lookup<const N: usize>(base: usize, step: usize) -> [u8; N] {
    let mut table = [0; N];
    let mut index = 0;
    let mut bucket = 0;
    while bucket < N {
        let size = base + bucket * step;
        while CLASSES[index].size < size {
            index += 1;
        }
        table[bucket] = index as u8;
        bucket += 1;
    }
    table
}
const SMALL: [u8; 129] = lookup(0, 8);
const MEDIUM: [u8; 57] = lookup(1024, 128);

#[inline]
pub(super) fn class_for(size: usize, alignment: usize) -> usize {
    debug_assert!(size <= 8192);
    debug_assert!(alignment.is_power_of_two() && alignment <= 8192);
    let mut index = if size <= 1024 {
        SMALL[size.div_ceil(8)] as usize
    } else {
        MEDIUM[(size - 1024).div_ceil(128)] as usize
    };
    // A rounded request alone does not guarantee aligned subsequent slots:
    // e.g. a 2560-byte request aligned to 512 would otherwise choose 2688.
    // Keep the dense class when possible, or advance to an aligned stride.
    while CLASSES[index].size & (alignment - 1) != 0 {
        index += 1;
    }
    index
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lookup_selects_the_first_fitting_aligned_class() {
        for alignment in (3..=13).map(|shift| 1 << shift) {
            for size in (alignment..=8192).step_by(alignment) {
                let expected = CLASSES
                    .iter()
                    .position(|class| class.size >= size && class.size.is_multiple_of(alignment))
                    .unwrap();
                assert_eq!(
                    class_for(size, alignment),
                    expected,
                    "size={size} align={alignment}"
                );
            }
        }
        for size in 0..=8192 {
            let expected = CLASSES.iter().position(|class| class.size >= size).unwrap();
            assert_eq!(class_for(size, 8), expected, "size={size}");
        }
    }

    #[test]
    fn spans_pack_slots_without_excessive_tail_waste() {
        assert_eq!(CLASSES.last().unwrap().size, 8192);
        for (index, class) in CLASSES.iter().enumerate() {
            assert!(index == 0 || CLASSES[index - 1].size < class.size);
            let bytes = class.pages * 8192;
            assert!(class.size <= bytes);
            assert!(bytes % class.size <= bytes / 8);
        }
        assert_eq!(CLASSES[class_for(408, 8)].size, 416);
        assert_eq!(CLASSES[class_for(40, 8)].size, 48);
    }
}
