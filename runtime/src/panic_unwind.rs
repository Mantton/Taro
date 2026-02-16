use std::{
    backtrace::Backtrace,
    cell::{Cell, RefCell},
    io::Write,
};

const PANIC_EXIT_CODE: i32 = 101;
#[cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]
const TARO_EXCEPTION_CLASS: u64 = u64::from_be_bytes(*b"TAROPAN!");

#[repr(C)]
#[derive(Clone, Copy)]
pub struct RtString {
    ptr: *const u8,
    len: usize,
}

impl RtString {
    fn to_owned_lossy(self) -> String {
        if self.ptr.is_null() || self.len == 0 {
            return String::new();
        }
        let bytes = unsafe { std::slice::from_raw_parts(self.ptr, self.len) };
        String::from_utf8_lossy(bytes).into_owned()
    }
}

struct PanicReport {
    message: String,
    backtrace: String,
    location: Option<String>,
}

std::thread_local! {
    static PANIC_REPORT: RefCell<Option<PanicReport>> = const { RefCell::new(None) };
    static PANIC_ACTIVE: Cell<bool> = const { Cell::new(false) };
}

#[inline]
fn set_panic_report(message: String) {
    set_panic_report_with_location(message, None);
}

#[inline]
fn set_panic_report_with_location(message: String, location: Option<String>) {
    let backtrace = format!("{:#}", Backtrace::force_capture());
    PANIC_REPORT.with(|slot| {
        *slot.borrow_mut() = Some(PanicReport {
            message,
            backtrace,
            location,
        });
    });
}

fn format_location(file: RtString, line: usize, column: usize) -> Option<String> {
    let file = file.to_owned_lossy();
    if file.is_empty() {
        return None;
    }
    if line == 0 {
        return Some(file);
    }
    if column == 0 {
        return Some(format!("{file}:{line}"));
    }
    Some(format!("{file}:{line}:{column}"))
}

fn write_report(default_message: &str) {
    let mut stderr = std::io::stderr().lock();
    let mut had_report = false;

    PANIC_REPORT.with(|slot| {
        if let Some(report) = slot.borrow().as_ref() {
            had_report = true;
            let _ = writeln!(stderr, "panic: {}", report.message);
            if let Some(location) = report.location.as_ref() {
                let _ = writeln!(stderr, "  at {}", location);
            }
            let _ = writeln!(stderr, "stack backtrace:");
            let _ = writeln!(stderr, "{}", report.backtrace);
        }
    });

    if !had_report {
        let _ = writeln!(stderr, "panic: {}", default_message);
        let _ = writeln!(stderr, "stack backtrace:");
        let _ = writeln!(stderr, "{:#}", Backtrace::force_capture());
    }

    let _ = stderr.flush();
}

fn abort_with_report(default_message: &str) -> ! {
    write_report(default_message);
    std::process::exit(PANIC_EXIT_CODE);
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__panic_abort(message: RtString) -> ! {
    __rt__panic_abort_at(
        message,
        RtString {
            ptr: std::ptr::null(),
            len: 0,
        },
        0,
        0,
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__panic_abort_at(
    message: RtString,
    file: RtString,
    line: usize,
    column: usize,
) -> ! {
    let msg = message.to_owned_lossy();
    let location = format_location(file, line, column);
    set_panic_report_with_location(msg, location);
    abort_with_report("panic aborted");
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__panic_abort_unwind(exception_ptr: *mut u8) -> ! {
    if PANIC_REPORT.with(|slot| slot.borrow().is_none()) {
        if exception_ptr.is_null() {
            set_panic_report("panic reached runtime boundary".to_string());
        } else {
            set_panic_report("foreign unwind reached runtime boundary".to_string());
        }
    }
    abort_with_report("panic reached runtime boundary");
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__panic_unwind(message: RtString) -> ! {
    __rt__panic_unwind_at(
        message,
        RtString {
            ptr: std::ptr::null(),
            len: 0,
        },
        0,
        0,
    )
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__panic_unwind_at(
    message: RtString,
    file: RtString,
    line: usize,
    column: usize,
) -> ! {
    let already_panicking = PANIC_ACTIVE.with(|flag| {
        let active = flag.get();
        flag.set(true);
        active
    });
    if already_panicking {
        set_panic_report("panic while unwinding".to_string());
        abort_with_report("panic while unwinding");
    }

    let msg = message.to_owned_lossy();
    let location = format_location(file, line, column);
    set_panic_report_with_location(msg, location);

    #[cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]
    unsafe {
        let exception = Box::new(UnwindException {
            exception_class: TARO_EXCEPTION_CLASS,
            exception_cleanup: Some(unwind_exception_cleanup),
            private_1: 0,
            private_2: 0,
        });
        let exception_ptr = Box::into_raw(exception);
        let reason = _Unwind_ForcedUnwind(exception_ptr, forced_unwind_stop, std::ptr::null_mut());
        // If forced unwind returns, unwinding failed.
        _Unwind_DeleteException(exception_ptr);
        let msg = format!("unwind failed with reason {}", reason);
        set_panic_report(msg);
        abort_with_report("unwind failed");
    }

    #[cfg(not(all(unix, any(target_arch = "x86_64", target_arch = "aarch64"))))]
    {
        static WARN_ONCE: std::sync::Once = std::sync::Once::new();
        WARN_ONCE.call_once(|| {
            eprintln!(
                "warning: panic unwinding is unsupported on this target; falling back to abort"
            );
        });
        abort_with_report("panic unwind unsupported");
    }
}

#[cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]
type UnwindReasonCode = i32;
#[cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]
type UnwindAction = i32;
#[cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]
const UA_END_OF_STACK: UnwindAction = 16;
#[cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]
const URC_NO_REASON: UnwindReasonCode = 0;

#[cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]
#[repr(C)]
struct UnwindException {
    exception_class: u64,
    exception_cleanup: Option<extern "C" fn(UnwindReasonCode, *mut UnwindException)>,
    private_1: usize,
    private_2: usize,
}

#[cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]
unsafe extern "C" {
    fn _Unwind_ForcedUnwind(
        exception_object: *mut UnwindException,
        stop_fn: extern "C" fn(
            version: i32,
            actions: UnwindAction,
            exception_class: u64,
            exception_object: *mut UnwindException,
            context: *mut std::ffi::c_void,
            stop_parameter: *mut std::ffi::c_void,
        ) -> UnwindReasonCode,
        stop_parameter: *mut std::ffi::c_void,
    ) -> UnwindReasonCode;
    fn _Unwind_DeleteException(exception_object: *mut UnwindException);
}

#[cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]
extern "C" fn unwind_exception_cleanup(_reason: UnwindReasonCode, exception: *mut UnwindException) {
    if exception.is_null() {
        return;
    }
    unsafe {
        drop(Box::from_raw(exception));
    }
}

#[cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]
extern "C" fn forced_unwind_stop(
    _version: i32,
    actions: UnwindAction,
    _exception_class: u64,
    exception_object: *mut UnwindException,
    _context: *mut std::ffi::c_void,
    _stop_parameter: *mut std::ffi::c_void,
) -> UnwindReasonCode {
    if (actions & UA_END_OF_STACK) != 0 {
        __rt__panic_abort_unwind(exception_object.cast::<u8>());
    }
    URC_NO_REASON
}
