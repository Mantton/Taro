//! Unix runtime shims exposed through stable non-variadic exports.
//!
//! Taro's direct C FFI is currently fixed-signature oriented. For APIs like
//! libc `open` (variadic), these wrappers provide stable entry points.

use core::ffi::{c_char, c_int};

/// Fixed ABI for the integer-only descriptor/status flag operations used by
/// std. In particular, Darwin's variadic argument must be placed on the stack;
/// declaring libc fcntl as a fixed three-argument function is not ABI-correct.
/// Pointer-taking commands are rejected before entering libc.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__fcntl_int(fd: i32, command: i32, argument: i32) -> i32 {
    unsafe {
        match command {
            libc::F_GETFD | libc::F_GETFL => libc::fcntl(fd, command),
            libc::F_SETFD | libc::F_SETFL => libc::fcntl(fd, command, argument),
            _ => {
                #[cfg(target_os = "macos")]
                {
                    *libc::__error() = libc::EINVAL;
                }
                #[cfg(target_os = "linux")]
                {
                    *libc::__errno_location() = libc::EINVAL;
                }
                -1
            }
        }
    }
}

#[cfg(all(test, any(target_os = "macos", target_os = "linux")))]
mod tests {
    #[test]
    fn integer_fcntl_roundtrips_flags_and_rejects_pointer_commands() {
        let mut descriptors = [-1; 2];
        assert_eq!(unsafe { libc::pipe(descriptors.as_mut_ptr()) }, 0);
        struct Pipe([i32; 2]);
        impl Drop for Pipe {
            fn drop(&mut self) {
                for fd in self.0 {
                    unsafe {
                        libc::close(fd);
                    }
                }
            }
        }
        let pipe = Pipe(descriptors);
        let fd = pipe.0[0];
        for flags in [libc::FD_CLOEXEC, 0] {
            assert_eq!(super::__rt__fcntl_int(fd, libc::F_SETFD, flags), 0);
            assert_eq!(
                super::__rt__fcntl_int(fd, libc::F_GETFD, 0) & libc::FD_CLOEXEC,
                flags
            );
        }
        let status = super::__rt__fcntl_int(fd, libc::F_GETFL, 0);
        assert!(status >= 0);
        assert_eq!(
            super::__rt__fcntl_int(fd, libc::F_SETFL, status | libc::O_NONBLOCK),
            0
        );
        assert_ne!(
            super::__rt__fcntl_int(fd, libc::F_GETFL, 0) & libc::O_NONBLOCK,
            0
        );
        assert_eq!(super::__rt__fcntl_int(fd, libc::F_GETLK, 0), -1);
        assert_eq!(
            std::io::Error::last_os_error().raw_os_error(),
            Some(libc::EINVAL)
        );
    }
}

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
