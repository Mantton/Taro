//! Stable Unix filesystem shims for the Taro standard library.
//!
//! POSIX exposes metadata and directory entries through C structs whose
//! layouts vary by operating system and architecture. Keeping that layout
//! knowledge here lets `std.sys.fs` consume a small scalar ABI instead of
//! duplicating libc internals in Taro source.

use crate::panic_unwind::RtString;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Seek, SeekFrom};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::ptr;

const FILE_TYPE_REGULAR: u8 = 1;
const FILE_TYPE_DIRECTORY: u8 = 2;
const FILE_TYPE_SYMLINK: u8 = 3;
const FILE_TYPE_BLOCK_DEVICE: u8 = 4;
const FILE_TYPE_CHARACTER_DEVICE: u8 = 5;
const FILE_TYPE_FIFO: u8 = 6;
const FILE_TYPE_SOCKET: u8 = 7;
const FILE_TYPE_OTHER: u8 = 8;

fn error_code(error: io::Error) -> i32 {
    error.raw_os_error().unwrap_or(libc::EIO)
}

fn input_bytes(value: RtString) -> Result<Vec<u8>, i32> {
    if value.len == 0 {
        return Ok(Vec::new());
    }
    if value.ptr.is_null() {
        return Err(libc::EINVAL);
    }

    let bytes = unsafe { std::slice::from_raw_parts(value.ptr, value.len) };
    if bytes.contains(&0) {
        return Err(libc::EINVAL);
    }
    Ok(bytes.to_vec())
}

fn input_path(value: RtString) -> Result<PathBuf, i32> {
    input_bytes(value).map(|bytes| PathBuf::from(OsString::from_vec(bytes)))
}

fn file_type_code(file_type: fs::FileType) -> u8 {
    if file_type.is_file() {
        FILE_TYPE_REGULAR
    } else if file_type.is_dir() {
        FILE_TYPE_DIRECTORY
    } else if file_type.is_symlink() {
        FILE_TYPE_SYMLINK
    } else if file_type.is_block_device() {
        FILE_TYPE_BLOCK_DEVICE
    } else if file_type.is_char_device() {
        FILE_TYPE_CHARACTER_DEVICE
    } else if file_type.is_fifo() {
        FILE_TYPE_FIFO
    } else if file_type.is_socket() {
        FILE_TYPE_SOCKET
    } else {
        FILE_TYPE_OTHER
    }
}

fn valid_nanos(value: i64) -> Option<u32> {
    if (0..1_000_000_000).contains(&value) {
        Some(value as u32)
    } else {
        None
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_metadata(
    path: RtString,
    follow_symlinks: bool,
    file_type_out: *mut u8,
    len_out: *mut u64,
    modified_secs_out: *mut i64,
    modified_nanos_out: *mut u32,
    accessed_secs_out: *mut i64,
    accessed_nanos_out: *mut u32,
) -> i32 {
    if file_type_out.is_null()
        || len_out.is_null()
        || modified_secs_out.is_null()
        || modified_nanos_out.is_null()
        || accessed_secs_out.is_null()
        || accessed_nanos_out.is_null()
    {
        return libc::EINVAL;
    }

    let path = match input_path(path) {
        Ok(path) => path,
        Err(code) => return code,
    };
    let metadata = match if follow_symlinks {
        fs::metadata(&path)
    } else {
        fs::symlink_metadata(&path)
    } {
        Ok(metadata) => metadata,
        Err(error) => return error_code(error),
    };

    let Some(modified_nanos) = valid_nanos(metadata.mtime_nsec()) else {
        return libc::EIO;
    };
    let Some(accessed_nanos) = valid_nanos(metadata.atime_nsec()) else {
        return libc::EIO;
    };

    unsafe {
        file_type_out.write(file_type_code(metadata.file_type()));
        len_out.write(metadata.len());
        modified_secs_out.write(metadata.mtime());
        modified_nanos_out.write(modified_nanos);
        accessed_secs_out.write(metadata.atime());
        accessed_nanos_out.write(accessed_nanos);
    }
    0
}

struct RuntimeReadDir {
    inner: fs::ReadDir,
    // `dir_read` returns a borrowed pointer. Retaining the current name in the
    // handle keeps that pointer valid until the next read or close call.
    current_name: Vec<u8>,
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_dir_open(path: RtString, error_out: *mut i32) -> usize {
    if error_out.is_null() {
        return 0;
    }
    unsafe { error_out.write(0) };

    let path = match input_path(path) {
        Ok(path) => path,
        Err(code) => {
            unsafe { error_out.write(code) };
            return 0;
        }
    };
    let inner = match fs::read_dir(path) {
        Ok(inner) => inner,
        Err(error) => {
            unsafe { error_out.write(error_code(error)) };
            return 0;
        }
    };

    Box::into_raw(Box::new(RuntimeReadDir {
        inner,
        current_name: Vec::new(),
    })) as usize
}

/// Return 0 for an entry, -1 for EOF, or a positive errno on failure.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_dir_read(
    handle: usize,
    name_out: *mut *mut u8,
    len_out: *mut usize,
    file_type_out: *mut u8,
) -> i32 {
    if handle == 0 {
        return libc::EBADF;
    }
    if name_out.is_null() || len_out.is_null() || file_type_out.is_null() {
        return libc::EINVAL;
    }

    let state = unsafe { &mut *(handle as *mut RuntimeReadDir) };
    let entry = match state.inner.next() {
        Some(Ok(entry)) => entry,
        Some(Err(error)) => return error_code(error),
        None => return -1,
    };
    let file_type = match entry.file_type() {
        Ok(file_type) => file_type_code(file_type),
        Err(error) => return error_code(error),
    };
    state.current_name = entry.file_name().into_vec();

    unsafe {
        name_out.write(state.current_name.as_mut_ptr());
        len_out.write(state.current_name.len());
        file_type_out.write(file_type);
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_dir_close(handle: usize) -> i32 {
    if handle == 0 {
        return libc::EBADF;
    }
    unsafe { drop(Box::from_raw(handle as *mut RuntimeReadDir)) };
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_remove_dir_all(path: RtString) -> i32 {
    let path = match input_path(path) {
        Ok(path) => path,
        Err(code) => return code,
    };

    let metadata = match fs::symlink_metadata(&path) {
        Ok(metadata) => metadata,
        Err(error) if error.raw_os_error() == Some(libc::ENOENT) => return 0,
        Err(error) => return error_code(error),
    };

    // Rust's Unix implementation uses openat/unlinkat with O_NOFOLLOW for
    // directories. That descriptor-relative traversal is what makes the
    // no-symlink-following guarantee hold even under replacement races.
    let result = if metadata.file_type().is_dir() {
        fs::remove_dir_all(&path)
    } else {
        fs::remove_file(&path)
    };
    match result {
        Ok(()) => 0,
        Err(error) if error.raw_os_error() == Some(libc::ENOENT) => 0,
        Err(error) => error_code(error),
    }
}

fn open_regular_source(path: &Path) -> Result<(File, fs::Metadata), i32> {
    let file = OpenOptions::new()
        .read(true)
        // Avoid waiting indefinitely if a path is concurrently replaced by a
        // FIFO or device before it is opened.
        .custom_flags(libc::O_NONBLOCK)
        .open(path)
        .map_err(error_code)?;
    let metadata = file.metadata().map_err(error_code)?;
    if !metadata.file_type().is_file() {
        return Err(if metadata.file_type().is_dir() {
            libc::EISDIR
        } else {
            libc::EINVAL
        });
    }
    Ok((file, metadata))
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_copy(from: RtString, to: RtString, copied_out: *mut u64) -> i32 {
    if copied_out.is_null() {
        return libc::EINVAL;
    }
    let from = match input_path(from) {
        Ok(path) => path,
        Err(code) => return code,
    };
    let to = match input_path(to) {
        Ok(path) => path,
        Err(code) => return code,
    };

    let (mut source, source_metadata) = match open_regular_source(&from) {
        Ok(source) => source,
        Err(code) => return code,
    };
    let source_mode = source_metadata.mode();
    let mut destination = match OpenOptions::new()
        .write(true)
        .create(true)
        // Deliberately omit O_TRUNC until descriptor identity is checked.
        .mode(source_mode)
        .custom_flags(libc::O_NONBLOCK)
        .open(&to)
    {
        Ok(destination) => destination,
        Err(error) => return error_code(error),
    };
    let destination_metadata = match destination.metadata() {
        Ok(metadata) => metadata,
        Err(error) => return error_code(error),
    };
    if !destination_metadata.file_type().is_file() {
        return if destination_metadata.file_type().is_dir() {
            libc::EISDIR
        } else {
            libc::EINVAL
        };
    }

    // Comparing the opened descriptors, rather than their input strings,
    // catches hard links and symlink aliases before destination truncation.
    if source_metadata.dev() == destination_metadata.dev()
        && source_metadata.ino() == destination_metadata.ino()
    {
        return libc::EINVAL;
    }
    if let Err(error) = destination.set_len(0) {
        return error_code(error);
    }
    if let Err(error) = destination.seek(SeekFrom::Start(0)) {
        return error_code(error);
    }

    let copied = match io::copy(&mut source, &mut destination) {
        Ok(copied) => copied,
        Err(error) => return error_code(error),
    };
    if let Err(error) = destination.set_permissions(fs::Permissions::from_mode(source_mode)) {
        return error_code(error);
    }

    unsafe { copied_out.write(copied) };
    0
}

fn allocate_owned_bytes(
    bytes: &[u8],
    data_out: *mut *mut u8,
    len_out: *mut usize,
) -> Result<(), i32> {
    if data_out.is_null() || len_out.is_null() {
        return Err(libc::EINVAL);
    }
    unsafe {
        data_out.write(ptr::null_mut());
        len_out.write(0);
    }
    if bytes.is_empty() {
        return Ok(());
    }

    let data = unsafe { libc::malloc(bytes.len()).cast::<u8>() };
    if data.is_null() {
        return Err(libc::ENOMEM);
    }
    unsafe {
        ptr::copy_nonoverlapping(bytes.as_ptr(), data, bytes.len());
        data_out.write(data);
        len_out.write(bytes.len());
    }
    Ok(())
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_owned_bytes_free(data: *mut u8) {
    if !data.is_null() {
        unsafe { libc::free(data.cast()) };
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_canonicalize(
    path: RtString,
    data_out: *mut *mut u8,
    len_out: *mut usize,
) -> i32 {
    let path = match input_path(path) {
        Ok(path) => path,
        Err(code) => return code,
    };
    let canonical = match fs::canonicalize(path) {
        Ok(path) => path.into_os_string().into_vec(),
        Err(error) => return error_code(error),
    };
    match allocate_owned_bytes(&canonical, data_out, len_out) {
        Ok(()) => 0,
        Err(code) => code,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__fs_create_temp_dir(
    parent: RtString,
    prefix: RtString,
    data_out: *mut *mut u8,
    len_out: *mut usize,
) -> i32 {
    let parent_bytes = match input_bytes(parent) {
        Ok(bytes) => bytes,
        Err(code) => return code,
    };
    let prefix = match input_bytes(prefix) {
        Ok(bytes) => bytes,
        Err(code) => return code,
    };
    if prefix.contains(&b'/') {
        return libc::EINVAL;
    }

    let parent = if parent_bytes.is_empty() {
        std::env::temp_dir()
    } else {
        PathBuf::from(OsString::from_vec(parent_bytes))
    };
    let mut template = parent
        .join(OsStr::from_bytes(&prefix))
        .into_os_string()
        .into_vec();
    template.extend_from_slice(b"XXXXXX");
    template.push(0);

    let created = unsafe { libc::mkdtemp(template.as_mut_ptr().cast()) };
    if created.is_null() {
        return error_code(io::Error::last_os_error());
    }
    let created_len = template.len() - 1;
    let created_bytes = &template[..created_len];
    match allocate_owned_bytes(created_bytes, data_out, len_out) {
        Ok(()) => 0,
        Err(code) => {
            // If returning the path fails, retain no unowned temporary
            // directory for the caller to discover later.
            let _ = fs::remove_dir(Path::new(OsStr::from_bytes(created_bytes)));
            code
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::TempDir;

    fn rt_path(path: &Path) -> RtString {
        let bytes = path.as_os_str().as_bytes();
        RtString {
            ptr: bytes.as_ptr(),
            len: bytes.len(),
        }
    }

    #[test]
    fn metadata_rejects_embedded_nul() {
        let path = b"bad\0path";
        let value = RtString {
            ptr: path.as_ptr(),
            len: path.len(),
        };
        let mut file_type = 0_u8;
        let mut len = 0_u64;
        let mut modified_secs = 0_i64;
        let mut modified_nanos = 0_u32;
        let mut accessed_secs = 0_i64;
        let mut accessed_nanos = 0_u32;
        assert_eq!(
            __rt__fs_metadata(
                value,
                true,
                &mut file_type,
                &mut len,
                &mut modified_secs,
                &mut modified_nanos,
                &mut accessed_secs,
                &mut accessed_nanos,
            ),
            libc::EINVAL
        );
    }

    #[test]
    fn input_path_preserves_non_utf8_bytes() {
        let bytes = b"raw-\xff-name";
        let value = RtString {
            ptr: bytes.as_ptr(),
            len: bytes.len(),
        };

        let path = input_path(value).expect("non-NUL Unix path bytes should be accepted");
        assert_eq!(path.as_os_str().as_bytes(), bytes);
    }

    #[test]
    fn copy_rejects_same_descriptor_before_truncation() {
        let root = TempDir::new("copy");
        let source = root.join("source");
        fs::write(&source, b"preserved").unwrap();

        let mut copied = 0_u64;
        assert_eq!(
            __rt__fs_copy(rt_path(&source), rt_path(&source), &mut copied),
            libc::EINVAL
        );
        assert_eq!(fs::read(&source).unwrap(), b"preserved");
    }

    #[test]
    fn recursive_remove_unlinks_symlink_without_following_target() {
        let root = TempDir::new("remove");
        let target = root.join("target");
        let tree = root.join("tree");
        fs::create_dir_all(&target).unwrap();
        fs::create_dir_all(&tree).unwrap();
        fs::write(target.join("kept"), b"value").unwrap();
        std::os::unix::fs::symlink(&target, tree.join("link")).unwrap();

        assert_eq!(__rt__fs_remove_dir_all(rt_path(&tree)), 0);
        assert!(target.join("kept").exists());
    }
}
