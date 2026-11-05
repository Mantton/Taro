//! Trusted compiler metadata validation and source locations.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct RawSource {
    pub file: *const u8,
    pub file_len: usize,
    pub line: u32,
    pub column: u32,
}
pub(crate) struct Source {
    pub file: &'static [u8],
    pub line: u32,
    pub column: u32,
}
pub(crate) fn invalid_metadata(reason: &str) -> ! {
    eprintln!("fatal: invalid runtime metadata: {reason}");
    std::process::abort()
}
pub(crate) unsafe fn read_source(source: *const RawSource) -> Source {
    if source.is_null() {
        invalid_metadata("null source descriptor");
    }
    let source = unsafe { source.read() };
    let file: &'static [u8] = if source.file_len == 0 {
        b""
    } else {
        if source.file.is_null() {
            invalid_metadata("null file bytes");
        }
        // Compiler file literals are immutable process-long metadata. The raw
        // source header itself is only read during this call and is not stored.
        unsafe { std::slice::from_raw_parts(source.file, source.file_len) }
    };
    Source {
        file,
        line: source.line,
        column: source.column,
    }
}
