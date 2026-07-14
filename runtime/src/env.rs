//! Stable Unix process-environment shims for the Taro standard library.
//!
//! Unix environment strings are arbitrary non-NUL bytes, while Rust's most
//! convenient environment APIs are text-oriented. This module keeps the ABI
//! byte-preserving and owns every value returned across the runtime boundary.

use crate::panic_unwind::RtString;
use std::ffi::{CStr, OsString};
use std::io;
use std::mem::MaybeUninit;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::path::PathBuf;
use std::ptr;
use std::sync::{Mutex, MutexGuard};

// Rust correctly marks process-environment mutation as unsafe on Unix because
// C APIs expose borrowed pointers into global storage. Serializing every Taro
// access ensures that our reads copy those bytes before another Taro task can
// invalidate them. FFI code that mutates `environ` must provide the same
// process-wide exclusion, just as it must for native C callers.
static PROCESS_STATE_LOCK: Mutex<()> = Mutex::new(());

fn lock_process_state() -> MutexGuard<'static, ()> {
    // None of the guarded operations intentionally panic. If an unrelated
    // panic ever poisons the lock, retaining access is safer than making all
    // future environment and cwd calls fail permanently.
    PROCESS_STATE_LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

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

fn input_name(value: RtString) -> Result<OsString, i32> {
    let bytes = input_bytes(value)?;
    // POSIX reserves '=' as the name/value delimiter. Rejecting it for every
    // operation keeps get/remove validation consistent with setenv rather than
    // turning malformed names into surprising "missing" results.
    if bytes.is_empty() || bytes.contains(&b'=') {
        return Err(libc::EINVAL);
    }
    Ok(OsString::from_vec(bytes))
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
pub extern "C" fn __rt__env_owned_bytes_free(data: *mut u8) {
    if !data.is_null() {
        unsafe { libc::free(data.cast()) };
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__env_get(
    name: RtString,
    data_out: *mut *mut u8,
    len_out: *mut usize,
    present_out: *mut bool,
) -> i32 {
    if present_out.is_null() {
        return libc::EINVAL;
    }
    unsafe { present_out.write(false) };

    let name = match input_name(name) {
        Ok(name) => name,
        Err(code) => return code,
    };
    let _guard = lock_process_state();
    let Some(value) = std::env::var_os(&name) else {
        // Initialize the ordinary outputs too so defensive foreign callers do
        // not observe stale pointers for a missing variable.
        return match allocate_owned_bytes(&[], data_out, len_out) {
            Ok(()) => 0,
            Err(code) => code,
        };
    };

    match allocate_owned_bytes(value.as_bytes(), data_out, len_out) {
        Ok(()) => {
            unsafe { present_out.write(true) };
            0
        }
        Err(code) => code,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__env_set(name: RtString, value: RtString) -> i32 {
    let name = match input_name(name) {
        Ok(name) => name,
        Err(code) => return code,
    };
    let value = match input_bytes(value) {
        Ok(value) => OsString::from_vec(value),
        Err(code) => return code,
    };

    let _guard = lock_process_state();
    // SAFETY: validated inputs cannot trigger the documented panics, and using
    // Rust's platform wrapper also shares its internal environment lock with
    // runtime configuration reads outside this module. PROCESS_STATE_LOCK adds
    // linear ordering across the public Taro API.
    unsafe { std::env::set_var(name, value) };
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__env_remove(name: RtString) -> i32 {
    let name = match input_name(name) {
        Ok(name) => name,
        Err(code) => return code,
    };

    let _guard = lock_process_state();
    // SAFETY: see __rt__env_set; the name was validated and Rust's internal
    // environment lock coordinates this mutation with runtime config reads.
    unsafe { std::env::remove_var(name) };
    0
}

struct EnvironmentSnapshot {
    entries: Vec<(Vec<u8>, Vec<u8>)>,
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__env_snapshot_open(len_out: *mut usize) -> usize {
    if len_out.is_null() {
        return 0;
    }

    let entries = {
        let _guard = lock_process_state();
        // Preserve the OS-provided order. The public guarantee is ownership at
        // one point in time; imposing a sort here would hide an allocation and
        // differ from Go's os.Environ and the filesystem traversal APIs.
        std::env::vars_os()
            .map(|(name, value)| (name.into_vec(), value.into_vec()))
            .collect::<Vec<_>>()
    };
    unsafe { len_out.write(entries.len()) };
    Box::into_raw(Box::new(EnvironmentSnapshot { entries })) as usize
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__env_snapshot_at(
    handle: usize,
    index: usize,
    name_data_out: *mut *const u8,
    name_len_out: *mut usize,
    value_data_out: *mut *const u8,
    value_len_out: *mut usize,
) -> i32 {
    if handle == 0
        || name_data_out.is_null()
        || name_len_out.is_null()
        || value_data_out.is_null()
        || value_len_out.is_null()
    {
        return libc::EINVAL;
    }

    let snapshot = unsafe { &*(handle as *const EnvironmentSnapshot) };
    let Some((name, value)) = snapshot.entries.get(index) else {
        return libc::EINVAL;
    };
    unsafe {
        name_data_out.write(name.as_ptr());
        name_len_out.write(name.len());
        value_data_out.write(value.as_ptr());
        value_len_out.write(value.len());
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__env_snapshot_close(handle: usize) {
    if handle != 0 {
        unsafe { drop(Box::from_raw(handle as *mut EnvironmentSnapshot)) };
    }
}

fn export_path(result: io::Result<PathBuf>, data_out: *mut *mut u8, len_out: *mut usize) -> i32 {
    let path = match result {
        Ok(path) => path.into_os_string().into_vec(),
        Err(error) => return error_code(error),
    };
    match allocate_owned_bytes(&path, data_out, len_out) {
        Ok(()) => 0,
        Err(code) => code,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__env_current_dir(data_out: *mut *mut u8, len_out: *mut usize) -> i32 {
    let _guard = lock_process_state();
    export_path(std::env::current_dir(), data_out, len_out)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__env_set_current_dir(path: RtString) -> i32 {
    let path = match input_bytes(path) {
        Ok(path) => PathBuf::from(OsString::from_vec(path)),
        Err(code) => return code,
    };
    let _guard = lock_process_state();
    match std::env::set_current_dir(path) {
        Ok(()) => 0,
        Err(error) => error_code(error),
    }
}

fn passwd_home_dir() -> Result<Vec<u8>, i32> {
    let configured = unsafe { libc::sysconf(libc::_SC_GETPW_R_SIZE_MAX) };
    let mut capacity = if configured > 0 {
        configured as usize
    } else {
        // POSIX permits sysconf to report no fixed limit. A modest starting
        // buffer plus ERANGE growth avoids either a tiny platform assumption or
        // an unnecessarily large allocation in the common case.
        1024
    };

    loop {
        let mut record = MaybeUninit::<libc::passwd>::uninit();
        let mut result = ptr::null_mut();
        let mut buffer = vec![0_u8; capacity];
        let status = unsafe {
            libc::getpwuid_r(
                libc::getuid(),
                record.as_mut_ptr(),
                buffer.as_mut_ptr().cast(),
                buffer.len(),
                &mut result,
            )
        };
        if status == 0 {
            if result.is_null() {
                return Err(libc::ENOENT);
            }
            let record = unsafe { record.assume_init() };
            if record.pw_dir.is_null() {
                return Err(libc::ENOENT);
            }
            return Ok(unsafe { CStr::from_ptr(record.pw_dir) }.to_bytes().to_vec());
        }
        if status != libc::ERANGE {
            return Err(status);
        }
        capacity = match capacity.checked_mul(2) {
            Some(next) => next,
            None => return Err(libc::ENOMEM),
        };
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__env_home_dir(data_out: *mut *mut u8, len_out: *mut usize) -> i32 {
    let _guard = lock_process_state();
    let home = std::env::var_os("HOME")
        .filter(|value| !value.is_empty())
        .map(|value| value.into_vec())
        .map(Ok)
        // A missing or empty HOME is not itself an error: Unix still has an
        // authoritative home directory in the current user's passwd record.
        .unwrap_or_else(passwd_home_dir);
    let home = match home {
        Ok(home) => home,
        Err(code) => return code,
    };
    match allocate_owned_bytes(&home, data_out, len_out) {
        Ok(()) => 0,
        Err(code) => code,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__env_temp_dir(data_out: *mut *mut u8, len_out: *mut usize) -> i32 {
    let _guard = lock_process_state();
    // Match Go's simple Unix contract: honor a non-empty TMPDIR and otherwise
    // return /tmp. This stays predictable across libc and OS versions and does
    // not imply that the returned directory currently exists or is writable.
    let temp = std::env::var_os("TMPDIR")
        .filter(|value| !value.is_empty())
        .map(|value| value.into_vec())
        .unwrap_or_else(|| b"/tmp".to_vec());
    match allocate_owned_bytes(&temp, data_out, len_out) {
        Ok(()) => 0,
        Err(code) => code,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_TEST_KEY: AtomicU64 = AtomicU64::new(0);

    fn test_key(label: &str) -> OsString {
        OsString::from(format!(
            "TARO_RUNTIME_ENV_{label}_{}_{}",
            std::process::id(),
            NEXT_TEST_KEY.fetch_add(1, Ordering::Relaxed)
        ))
    }

    fn rt_bytes(bytes: &[u8]) -> RtString {
        RtString {
            ptr: bytes.as_ptr(),
            len: bytes.len(),
        }
    }

    struct RestoreVariable {
        name: OsString,
        value: Option<OsString>,
    }

    impl RestoreVariable {
        fn capture(name: OsString) -> Self {
            let value = std::env::var_os(&name);
            Self { name, value }
        }
    }

    impl Drop for RestoreVariable {
        fn drop(&mut self) {
            // SAFETY: runtime unit tests are serialised by Rust's own env lock,
            // and each test uses a process-unique key not observed elsewhere.
            unsafe {
                match &self.value {
                    Some(value) => std::env::set_var(&self.name, value),
                    None => std::env::remove_var(&self.name),
                }
            }
        }
    }

    #[test]
    fn get_distinguishes_missing_and_empty_values() {
        let key = test_key("EMPTY");
        let _restore = RestoreVariable::capture(key.clone());
        let key_bytes = key.as_bytes();
        assert_eq!(__rt__env_remove(rt_bytes(key_bytes)), 0);

        let mut data = ptr::null_mut();
        let mut len = usize::MAX;
        let mut present = true;
        assert_eq!(
            __rt__env_get(rt_bytes(key_bytes), &mut data, &mut len, &mut present),
            0
        );
        assert!(!present);
        assert_eq!(len, 0);

        assert_eq!(__rt__env_set(rt_bytes(key_bytes), rt_bytes(b"")), 0);
        assert_eq!(
            __rt__env_get(rt_bytes(key_bytes), &mut data, &mut len, &mut present),
            0
        );
        assert!(present);
        assert_eq!(len, 0);
    }

    #[test]
    fn values_and_snapshots_preserve_raw_bytes() {
        let key = test_key("RAW");
        let _restore = RestoreVariable::capture(key.clone());
        let key_bytes = key.as_bytes();
        let value = b"raw-\xff-value";
        assert_eq!(__rt__env_set(rt_bytes(key_bytes), rt_bytes(value)), 0);

        let mut snapshot_len = 0;
        let handle = __rt__env_snapshot_open(&mut snapshot_len);
        assert_ne!(handle, 0);
        let mut found = false;
        for index in 0..snapshot_len {
            let mut name_data = ptr::null();
            let mut name_len = 0;
            let mut value_data = ptr::null();
            let mut value_len = 0;
            assert_eq!(
                __rt__env_snapshot_at(
                    handle,
                    index,
                    &mut name_data,
                    &mut name_len,
                    &mut value_data,
                    &mut value_len,
                ),
                0
            );
            let name = unsafe { std::slice::from_raw_parts(name_data, name_len) };
            if name == key_bytes {
                let captured = unsafe { std::slice::from_raw_parts(value_data, value_len) };
                assert_eq!(captured, value);
                found = true;
            }
        }
        __rt__env_snapshot_close(handle);
        assert!(found);
    }

    #[test]
    fn names_and_values_reject_invalid_posix_forms() {
        let mut data = ptr::null_mut();
        let mut len = 0;
        let mut present = false;
        assert_eq!(
            __rt__env_get(rt_bytes(b"BAD\0NAME"), &mut data, &mut len, &mut present),
            libc::EINVAL
        );
        assert_eq!(
            __rt__env_set(rt_bytes(b""), rt_bytes(b"value")),
            libc::EINVAL
        );
        assert_eq!(
            __rt__env_set(rt_bytes(b"BAD=NAME"), rt_bytes(b"value")),
            libc::EINVAL
        );
        assert_eq!(
            __rt__env_set(rt_bytes(b"VALID_NAME"), rt_bytes(b"BAD\0VALUE")),
            libc::EINVAL
        );
    }
}
