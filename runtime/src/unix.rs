//! Unix runtime shims exposed through stable non-variadic exports.
//!
//! Taro's direct C FFI is currently fixed-signature oriented. For APIs like
//! libc `open` (variadic), these wrappers provide stable entry points.

use core::ffi::{c_char, c_int};
use std::ffi::{CStr, OsStr};
use std::os::unix::ffi::OsStrExt;
use std::path::PathBuf;
use std::time::UNIX_EPOCH;

#[cfg(unix)]
unsafe extern "C" {
    fn open(path: *const c_char, oflag: c_int, ...) -> c_int;
}

#[cfg(target_os = "linux")]
unsafe extern "C" {
    fn __errno_location() -> *mut c_int;
}

#[cfg(target_os = "macos")]
unsafe extern "C" {
    fn __error() -> *mut c_int;
}

#[inline]
#[cfg(target_os = "linux")]
unsafe fn errno_ptr() -> *mut c_int {
    unsafe { __errno_location() }
}

#[inline]
#[cfg(target_os = "macos")]
unsafe fn errno_ptr() -> *mut c_int {
    unsafe { __error() }
}

#[inline]
#[cfg(all(unix, not(any(target_os = "linux", target_os = "macos"))))]
unsafe fn errno_ptr() -> *mut c_int {
    core::ptr::null_mut()
}

const EINVAL: i32 = 22;
const FILE_KIND_FILE: i32 = 1;
const FILE_KIND_DIR: i32 = 2;
const FILE_KIND_SYMLINK: i32 = 3;
const FILE_KIND_OTHER: i32 = 4;

fn path_from_c(path: *const u8) -> Result<PathBuf, i32> {
    if path.is_null() {
        return Err(EINVAL);
    }

    let c_path = unsafe { CStr::from_ptr(path.cast::<c_char>()) };
    let os = OsStr::from_bytes(c_path.to_bytes());
    Ok(PathBuf::from(os))
}

fn io_error_code(err: &std::io::Error) -> i32 {
    err.raw_os_error().unwrap_or(EINVAL)
}

fn file_kind(file_type: std::fs::FileType) -> i32 {
    if file_type.is_file() {
        FILE_KIND_FILE
    } else if file_type.is_dir() {
        FILE_KIND_DIR
    } else if file_type.is_symlink() {
        FILE_KIND_SYMLINK
    } else {
        FILE_KIND_OTHER
    }
}

fn system_time_to_secs(value: std::io::Result<std::time::SystemTime>) -> i64 {
    match value {
        Ok(ts) => match ts.duration_since(UNIX_EPOCH) {
            Ok(delta) => {
                if delta.as_secs() > i64::MAX as u64 {
                    i64::MAX
                } else {
                    delta.as_secs() as i64
                }
            }
            Err(before) => {
                let delta = before.duration();
                if delta.as_secs() > i64::MAX as u64 {
                    i64::MIN
                } else {
                    -(delta.as_secs() as i64)
                }
            }
        },
        Err(_) => -1,
    }
}

fn write_metadata_out(
    meta: &std::fs::Metadata,
    out_kind: *mut i32,
    out_len: *mut usize,
    out_readonly: *mut i32,
    out_modified_secs: *mut i64,
    out_accessed_secs: *mut i64,
    out_created_secs: *mut i64,
) -> i32 {
    if out_kind.is_null()
        || out_len.is_null()
        || out_readonly.is_null()
        || out_modified_secs.is_null()
        || out_accessed_secs.is_null()
        || out_created_secs.is_null()
    {
        return EINVAL;
    }

    let size = meta.len();
    if size > usize::MAX as u64 {
        return EINVAL;
    }

    let kind = file_kind(meta.file_type());
    let readonly = if meta.permissions().readonly() { 1 } else { 0 };
    let modified = system_time_to_secs(meta.modified());
    let accessed = system_time_to_secs(meta.accessed());
    let created = system_time_to_secs(meta.created());

    unsafe {
        *out_kind = kind;
        *out_len = size as usize;
        *out_readonly = readonly;
        *out_modified_secs = modified;
        *out_accessed_secs = accessed;
        *out_created_secs = created;
    }

    0
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

#[unsafe(no_mangle)]
pub extern "C" fn __rt__errno() -> i32 {
    #[cfg(unix)]
    unsafe {
        let ptr = errno_ptr();
        if ptr.is_null() {
            return 0;
        }
        return *ptr as i32;
    }

    #[cfg(not(unix))]
    {
        0
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_metadata(
    path: *const u8,
    out_kind: *mut i32,
    out_len: *mut usize,
    out_readonly: *mut i32,
    out_modified_secs: *mut i64,
    out_accessed_secs: *mut i64,
    out_created_secs: *mut i64,
) -> i32 {
    let path = match path_from_c(path) {
        Ok(value) => value,
        Err(code) => return code,
    };

    match std::fs::metadata(path) {
        Ok(meta) => write_metadata_out(
            &meta,
            out_kind,
            out_len,
            out_readonly,
            out_modified_secs,
            out_accessed_secs,
            out_created_secs,
        ),
        Err(err) => io_error_code(&err),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_symlink_metadata(
    path: *const u8,
    out_kind: *mut i32,
    out_len: *mut usize,
    out_readonly: *mut i32,
    out_modified_secs: *mut i64,
    out_accessed_secs: *mut i64,
    out_created_secs: *mut i64,
) -> i32 {
    let path = match path_from_c(path) {
        Ok(value) => value,
        Err(code) => return code,
    };

    match std::fs::symlink_metadata(path) {
        Ok(meta) => write_metadata_out(
            &meta,
            out_kind,
            out_len,
            out_readonly,
            out_modified_secs,
            out_accessed_secs,
            out_created_secs,
        ),
        Err(err) => io_error_code(&err),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_create_dir_all(path: *const u8) -> i32 {
    let path = match path_from_c(path) {
        Ok(value) => value,
        Err(code) => return code,
    };

    match std::fs::create_dir_all(path) {
        Ok(()) => 0,
        Err(err) => io_error_code(&err),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_remove_dir_all(path: *const u8) -> i32 {
    let path = match path_from_c(path) {
        Ok(value) => value,
        Err(code) => return code,
    };

    match std::fs::remove_dir_all(path) {
        Ok(()) => 0,
        Err(err) => io_error_code(&err),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_read_dir(
    path: *const u8,
    out_buf: *mut u8,
    cap: usize,
    out_written: *mut usize,
) -> i32 {
    if out_written.is_null() {
        return EINVAL;
    }

    let path = match path_from_c(path) {
        Ok(value) => value,
        Err(code) => return code,
    };

    let mut encoded = Vec::<u8>::new();
    encoded.extend_from_slice(&[0, 0, 0, 0]);
    let mut count: u32 = 0;

    let iter = match std::fs::read_dir(path) {
        Ok(value) => value,
        Err(err) => return io_error_code(&err),
    };

    for next in iter {
        let entry = match next {
            Ok(value) => value,
            Err(err) => return io_error_code(&err),
        };

        let name = entry.file_name();
        let name_bytes = name.as_os_str().as_bytes();
        if name_bytes.len() > u32::MAX as usize {
            return EINVAL;
        }

        let file_type = match entry.file_type() {
            Ok(value) => value,
            Err(err) => return io_error_code(&err),
        };

        let kind = file_kind(file_type) as u8;
        if count == u32::MAX {
            return EINVAL;
        }

        encoded.push(kind);

        let name_len = name_bytes.len() as u32;
        encoded.extend_from_slice(&name_len.to_le_bytes());
        encoded.extend_from_slice(name_bytes);
        count += 1;
    }

    encoded[0..4].copy_from_slice(&count.to_le_bytes());

    unsafe {
        *out_written = encoded.len();
    }

    if out_buf.is_null() {
        return 0;
    }

    if cap < encoded.len() {
        return EINVAL;
    }

    unsafe {
        std::ptr::copy_nonoverlapping(encoded.as_ptr(), out_buf, encoded.len());
    }
    0
}
