#[unsafe(no_mangle)]
pub extern "C" fn __rt__exit(code: i32) {
    std::process::exit(code);
}

use std::cell::Cell;
use std::ops::Range;
use std::sync::{Mutex, OnceLock};

// === Public FFI surface ===

/// Describes a GC-managed type: object size and offsets of pointer fields.
/// Pointer offsets are from the start of the payload (after the header).
#[repr(C)]
#[derive(Debug)]
pub struct GcDesc {
    pub size: usize,
    pub ptr_offsets: *const usize,
    pub ptr_count: usize,
}

#[unsafe(no_mangle)]
pub extern "C" fn gc_alloc(size: usize, desc: *const GcDesc) -> *mut u8 {
    with_gc(|gc| gc.alloc(size, desc))
}

#[unsafe(no_mangle)]
pub extern "C" fn gc_collect() {
    with_gc(|gc| gc.collect());
}

/// Register a static/global range as a root.
#[unsafe(no_mangle)]
pub extern "C" fn gc_register_static(begin: *const u8, end: *const u8) {
    if begin.is_null() || end.is_null() || end <= begin {
        return;
    }
    with_gc(|gc| gc.register_static(begin..end));
}

/// Manually add a root pointer (useful for embeddings/tests).
#[unsafe(no_mangle)]
pub extern "C" fn gc_add_root(ptr: *const u8) {
    if ptr.is_null() {
        return;
    }
    with_gc(|gc| gc.add_root(ptr));
}

// === Runtime GC implementation ===

const CHUNK_SIZE: usize = 1 << 20; // 1 MiB default chunk size

struct Header {
    mark: Cell<bool>,
    desc: *const GcDesc,
    payload_size: usize,
}

struct Object {
    start: *mut u8,    // points to header
    total_size: usize, // header + payload (aligned)
    header: *mut Header,
}

struct FreeBlock {
    ptr: *mut u8,
    size: usize,
}

struct Chunk {
    data: Vec<u8>,
    offset: usize,
    /// Side table for interior-pointer lookup: header pointer for each word.
    header_map: Vec<*mut Header>,
}

impl Chunk {
    fn new() -> Self {
        let data = vec![0; CHUNK_SIZE];
        let words = data.len() / std::mem::size_of::<usize>();
        Self {
            data,
            offset: 0,
            header_map: vec![std::ptr::null_mut(); words],
        }
    }

    fn base(&self) -> usize {
        self.data.as_ptr() as usize
    }

    fn contains(&self, ptr: *const u8) -> bool {
        let p = ptr as usize;
        p >= self.base() && p < self.base() + self.data.len()
    }

    fn alloc(&mut self, size: usize, align: usize) -> Option<*mut u8> {
        let base_ptr = self.base();
        let off = base_ptr + self.offset;
        let aligned = (off + (align - 1)) & !(align - 1);
        let delta = aligned - off;
        let new_off = self.offset + delta + size;
        if new_off > self.data.len() {
            return None;
        }
        self.offset = new_off;
        Some(aligned as *mut u8)
    }

    fn map_header(&mut self, header: *mut Header, start: *mut u8, size: usize) {
        let word_size = std::mem::size_of::<usize>();
        let base = self.base();
        let start_idx = ((start as usize) - base) / word_size;
        let end_idx = ((start as usize + size + word_size - 1) - base) / word_size;
        for idx in start_idx..=end_idx.min(self.header_map.len().saturating_sub(1)) {
            self.header_map[idx] = header;
        }
    }

    fn clear_header(&mut self, start: *mut u8, size: usize) {
        let word_size = std::mem::size_of::<usize>();
        let base = self.base();
        let start_idx = ((start as usize) - base) / word_size;
        let end_idx = ((start as usize + size + word_size - 1) - base) / word_size;
        for idx in start_idx..=end_idx.min(self.header_map.len().saturating_sub(1)) {
            self.header_map[idx] = std::ptr::null_mut();
        }
    }
}

struct Gc {
    chunks: Vec<Chunk>,
    objects: Vec<Object>,
    free_list: Vec<FreeBlock>,
    static_roots: Vec<Range<*const u8>>,
    manual_roots: Vec<*const u8>,
}

// GC is only accessed under a Mutex; raw pointers are fine.
unsafe impl Send for Gc {}
unsafe impl Sync for Gc {}

impl Gc {
    fn new() -> Self {
        Self {
            chunks: vec![Chunk::new()],
            objects: Vec::new(),
            free_list: Vec::new(),
            static_roots: Vec::new(),
            manual_roots: Vec::new(),
        }
    }

    fn register_static(&mut self, range: Range<*const u8>) {
        self.static_roots.push(range);
    }

    fn add_root(&mut self, ptr: *const u8) {
        self.manual_roots.push(ptr);
    }

    fn alloc(&mut self, size: usize, desc: *const GcDesc) -> *mut u8 {
        let header_size = std::mem::size_of::<Header>();
        let total = align_up(header_size + size, std::mem::align_of::<Header>());

        // Try free list first (first-fit).
        if let Some(idx) = self
            .free_list
            .iter()
            .position(|b| b.size >= total && (b.ptr as usize) % std::mem::align_of::<Header>() == 0)
        {
            let block = self.free_list.swap_remove(idx);
            unsafe {
                let header = block.ptr as *mut Header;
                (*header).mark.set(false);
                (*header).desc = desc;
                (*header).payload_size = size;
                let payload = block.ptr.add(header_size);
                self.objects.push(Object {
                    start: block.ptr,
                    total_size: block.size,
                    header,
                });
                if let Some(chunk) = self.chunk_mut_for(block.ptr) {
                    chunk.map_header(header, block.ptr, block.size);
                }
                return payload;
            }
        }

        // Otherwise bump allocate from the current chunk (or new chunk).
        let ptr = loop {
            if let Some(chunk) = self.chunks.last_mut() {
                if let Some(p) = chunk.alloc(total, std::mem::align_of::<Header>()) {
                    break p;
                }
            }
            self.chunks.push(Chunk::new());
        };

        unsafe {
            let header = ptr as *mut Header;
            (*header).mark.set(false);
            (*header).desc = desc;
            (*header).payload_size = size;
            let payload = ptr.add(header_size);
            self.objects.push(Object {
                start: ptr,
                total_size: total,
                header,
            });
            if let Some(chunk) = self.chunk_mut_for(ptr) {
                chunk.map_header(header, ptr, total);
            }
            payload
        }
    }

    fn collect(&mut self) {
        self.mark_roots();
        self.sweep();
        self.manual_roots.clear();
    }

    fn mark_roots(&mut self) {
        for ptr in self.manual_roots.clone() {
            self.mark_ptr(ptr);
        }
        // Clone static_roots to avoid holding an immutable borrow while marking.
        for range in self.static_roots.clone() {
            let mut p = range.start as usize;
            let end = range.end as usize;
            while p + std::mem::size_of::<usize>() <= end {
                let word = p as *const usize;
                let candidate = unsafe { *word } as *const u8;
                self.mark_ptr(candidate);
                p += std::mem::size_of::<usize>();
            }
        }
    }

    fn mark_ptr(&mut self, ptr: *const u8) {
        if let Some(obj_idx) = self.find_object(ptr) {
            let header = unsafe { &*self.objects[obj_idx].header };
            if header.mark.replace(true) {
                return; // already marked
            }
            let desc = unsafe { header.desc.as_ref() };
            if let Some(desc) = desc {
                for i in 0..desc.ptr_count {
                    let off = unsafe { *desc.ptr_offsets.add(i) };
                    if off < header.payload_size {
                        let field_ptr = unsafe {
                            self.objects[obj_idx]
                                .start
                                .add(std::mem::size_of::<Header>() + off)
                        };
                        let val = unsafe { *(field_ptr as *const *const u8) };
                        self.mark_ptr(val);
                    }
                }
            }
        }
    }

    fn sweep(&mut self) {
        let mut i = 0;
        while i < self.objects.len() {
            let obj = &self.objects[i];
            let header = unsafe { &*obj.header };
            if header.mark.get() {
                header.mark.set(false);
                i += 1;
                continue;
            }

            // Dead: reclaim into free list.
            let (start_ptr, total_size, _header_ptr) = (obj.start, obj.total_size, obj.header);
            self.free_list.push(FreeBlock {
                ptr: obj.start,
                size: obj.total_size,
            });
            self.objects.swap_remove(i);
            if let Some(chunk) = self.chunk_mut_for(start_ptr) {
                chunk.clear_header(start_ptr, total_size);
            }

            println!("Freed memory")
        }
    }

    fn find_object(&self, ptr: *const u8) -> Option<usize> {
        let chunk = self.chunks.iter().find(|c| c.contains(ptr))?;
        let word_size = std::mem::size_of::<usize>();
        let idx = ((ptr as usize) - chunk.base()) / word_size;
        let header_ptr = *chunk.header_map.get(idx)?;
        if header_ptr.is_null() {
            return None;
        }
        self.objects.iter().position(|obj| obj.header == header_ptr)
    }

    fn chunk_mut_for(&mut self, ptr: *mut u8) -> Option<&mut Chunk> {
        self.chunks.iter_mut().find(|c| c.contains(ptr))
    }
}

fn with_gc<R>(f: impl FnOnce(&mut Gc) -> R) -> R {
    static INSTANCE: OnceLock<Mutex<Gc>> = OnceLock::new();
    let gc = INSTANCE.get_or_init(|| Mutex::new(Gc::new()));
    let mut guard = gc.lock().expect("gc mutex");
    f(&mut guard)
}

fn align_up(n: usize, align: usize) -> usize {
    (n + (align - 1)) & !(align - 1)
}
