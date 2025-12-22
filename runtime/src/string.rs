use std::io::Write;

#[repr(C)]
pub struct StringHeader {
    pub data: *const u8,
    pub len: usize,
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__print(s: StringHeader) {
    if s.len == 0 || s.data.is_null() {
        return;
    }
    let bytes = unsafe { std::slice::from_raw_parts(s.data, s.len) };
    let mut out = std::io::stdout();
    let _ = out.write_all(bytes);
    let _ = out.flush();
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
