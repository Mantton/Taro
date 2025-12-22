#[unsafe(no_mangle)]
pub extern "C" fn gcptr_null() -> *mut u8 {
    std::ptr::null_mut()
}

#[unsafe(no_mangle)]
pub extern "C" fn gcptr_is_null(ptr: *const u8) -> bool {
    ptr.is_null()
}

#[unsafe(no_mangle)]
pub extern "C" fn gcptr_from_raw(ptr: *const u8) -> *mut u8 {
    ptr as *mut u8
}

#[unsafe(no_mangle)]
pub extern "C" fn gcptr_to_raw(ptr: *const u8) -> *const u8 {
    ptr
}

#[unsafe(no_mangle)]
pub extern "C" fn gcptr_add_bytes(ptr: *mut u8, offset: usize) -> *mut u8 {
    ptr.wrapping_add(offset)
}

#[unsafe(no_mangle)]
pub extern "C" fn gc_memcpy(dst: *mut u8, src: *const u8, len: usize) {
    unsafe {
        std::ptr::copy_nonoverlapping(src, dst, len);
    }
}
