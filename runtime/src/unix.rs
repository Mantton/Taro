//! Unix runtime shims exposed through stable non-variadic exports.
//!
//! Taro's direct C FFI is currently fixed-signature oriented. For APIs like
//! libc `open` (variadic), these wrappers provide stable entry points.

use core::ffi::{c_char, c_int};

#[cfg(unix)]
unsafe extern "C" {
    fn open(path: *const c_char, oflag: c_int, ...) -> c_int;
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__open2(path: *const u8, oflags: i32) -> i32 {
    #[cfg(unix)]
    unsafe {
        return open(path.cast::<c_char>(), oflags as c_int) as i32;
    }

    #[cfg(not(unix))]
    {
        let _ = path;
        let _ = oflags;
        -1
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__open3(path: *const u8, oflags: i32, mode: i32) -> i32 {
    #[cfg(unix)]
    unsafe {
        return open(path.cast::<c_char>(), oflags as c_int, mode as c_int) as i32;
    }

    #[cfg(not(unix))]
    {
        let _ = path;
        let _ = oflags;
        let _ = mode;
        -1
    }
}
