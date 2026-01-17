#[repr(C)]
pub struct StringHeader {
    pub data: *const u8,
    pub len: usize,
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__string_data(s: StringHeader) -> *const u8 {
    s.data
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__string_len(s: StringHeader) -> usize {
    s.len
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__string_from_parts(data: *const u8, len: usize) -> StringHeader {
    StringHeader { data, len }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__string_eq(lhs: StringHeader, rhs: StringHeader) -> bool {
    if lhs.len != rhs.len {
        return false;
    }
    if lhs.len == 0 {
        return true;
    }
    if lhs.data.is_null() || rhs.data.is_null() {
        return false;
    }
    let lhs_bytes = unsafe { std::slice::from_raw_parts(lhs.data, lhs.len) };
    let rhs_bytes = unsafe { std::slice::from_raw_parts(rhs.data, rhs.len) };
    lhs_bytes == rhs_bytes
}
