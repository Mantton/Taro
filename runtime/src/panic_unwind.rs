//! Panic and unwind runtime support for Taro.
//!
//! # Two unwind mechanisms
//!
//! Taro needs panic unwinding to work in two distinct contexts:
//!
//! **Normal mode** (a regular binary): A panic should run every cleanup/defer
//! landing pad on the way up the stack, then terminate the program with an
//! error report.  This is done with `_Unwind_ForcedUnwind`, which visits every
//! frame unconditionally (running cleanup actions) and stops only when a custom
//! stop function signals end-of-stack.  The `taro_start` landing pad is NOT used
//! for catching — the stop function calls `__rt__panic_abort_unwind` directly.
//!
//! **Test mode** (a `@test` binary): A panic inside a test function must be
//! catchable so that `@expectPanic` tests pass and the harness can continue
//! to the next test.  `_Unwind_ForcedUnwind` cannot be caught by Rust's
//! `catch_unwind`, so instead we use `std::panic::panic_any`, which goes
//! through `_Unwind_RaiseException`.  Rust's `catch_unwind` in
//! `__rt__test_call_fn` intercepts it cleanly.
//!
//! # `IN_TEST_HARNESS` flag
//!
//! The `__rt__panic_unwind_at` function checks the `IN_TEST_HARNESS`
//! thread-local (set by `__rt__test_call_fn` around each test invocation) to
//! select the right mechanism.  Cleanup landing pads (defer blocks) still run
//! in test mode because `_Unwind_RaiseException` performs a normal
//! search-then-cleanup two-phase unwind, and `__gcc_personality_v0` runs
//! cleanup actions for any exception type.
//!
//! Grouped executor tasks also temporarily opt into the catchable
//! `_Unwind_RaiseException` path so the runtime can record child-task panics
//! without tearing down the whole scheduler.

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
    pub ptr: *const u8,
    pub len: usize,
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

#[derive(Clone)]
pub(crate) struct PanicReport {
    pub(crate) message: String,
    pub(crate) backtrace: String,
    pub(crate) location: Option<String>,
}

std::thread_local! {
    static PANIC_REPORT: RefCell<Option<PanicReport>> = const { RefCell::new(None) };
    static PANIC_ACTIVE: Cell<bool> = const { Cell::new(false) };
    /// Set to `true` by `__rt__test_call_fn` while a test function is running.
    /// When true, `__rt__panic_unwind_at` uses `panic_any` so `catch_unwind`
    /// can intercept it.  When false, it uses `_Unwind_ForcedUnwind` so that
    /// cleanup/defer landing pads execute correctly in normal mode.
    static IN_TEST_HARNESS: Cell<bool> = const { Cell::new(false) };
    /// Set temporarily while polling a grouped child task so the executor can
    /// capture its panic and apply task-group policy.
    static IN_EXECUTOR_CATCH: Cell<bool> = const { Cell::new(false) };
}

pub(crate) fn in_test_harness() -> bool {
    IN_TEST_HARNESS.with(Cell::get)
}

pub(crate) fn set_test_harness_active(active: bool) {
    IN_TEST_HARNESS.with(|flag| flag.set(active));
}

pub(crate) fn catch_executor_panic<R>(f: impl FnOnce() -> R) -> Result<R, PanicReport> {
    let previous = IN_EXECUTOR_CATCH.with(|flag| {
        let prev = flag.get();
        flag.set(true);
        prev
    });

    // Suppress Rust's built-in panic output; the executor owns reporting.
    let old_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));

    std::panic::set_hook(old_hook);
    IN_EXECUTOR_CATCH.with(|flag| flag.set(previous));

    match result {
        Ok(value) => Ok(value),
        Err(_) => {
            // Print the full backtrace to stderr immediately before consuming the report.
            write_report("spawned task panicked");
            let report = take_full_panic_report().unwrap_or_else(|| PanicReport {
                message: "task panicked on executor worker".into(),
                backtrace: String::new(),
                location: None,
            });
            Err(report)
        }
    }
}

/// Take the full panic report (message + backtrace + location) from the thread-local,
/// resetting the panic state. Returns `None` if no panic was recorded.
pub(crate) fn take_full_panic_report() -> Option<PanicReport> {
    let was_active = PANIC_ACTIVE.with(|flag| {
        let active = flag.get();
        flag.set(false);
        active
    });
    let report = PANIC_REPORT.with(|slot| slot.borrow_mut().take());
    if was_active {
        return report.or_else(|| {
            Some(PanicReport {
                message: String::new(),
                backtrace: String::new(),
                location: None,
            })
        });
    }
    report
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

pub(crate) fn take_thread_panic_report() -> Option<String> {
    let was_active = PANIC_ACTIVE.with(|flag| {
        let active = flag.get();
        flag.set(false);
        active
    });

    let report = PANIC_REPORT.with(|slot| slot.borrow_mut().take());
    if was_active {
        return report
            .map(|report| report.message)
            .or_else(|| Some(String::new()));
    }

    report.map(|report| report.message)
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

pub(crate) fn write_report(default_message: &str) {
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

/// FFI-safe result type for `__rt__panic_take_report`.
#[repr(C)]
pub struct PanicTakeReportResult {
    pub had_panic: bool,
    pub message_ptr: *const u8,
    pub message_len: usize,
}

/// Take the current panic report, reset panic state, and return whether
/// a panic was active along with the panic message.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__panic_take_report() -> PanicTakeReportResult {
    let was_active = PANIC_ACTIVE.with(|f| {
        let v = f.get();
        f.set(false);
        v
    });

    if !was_active {
        return PanicTakeReportResult {
            had_panic: false,
            message_ptr: std::ptr::null(),
            message_len: 0,
        };
    }

    let msg = PANIC_REPORT.with(|slot| {
        slot.borrow_mut()
            .take()
            .map(|r| r.message)
            .unwrap_or_default()
    });

    let ptr = msg.as_ptr();
    let len = msg.len();
    std::mem::forget(msg); // Small leak per failed test — acceptable
    PanicTakeReportResult {
        had_panic: was_active,
        message_ptr: ptr,
        message_len: len,
    }
}

/// Clears the panic state after a caught panic so the next test can run cleanly.
///
/// Called by the compiler-generated test harness in the `bb_panicked` branch.
/// Returns `void` to avoid ARM64 sret ABI complications.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__panic_clear() {
    PANIC_ACTIVE.with(|f| f.set(false));
    PANIC_REPORT.with(|slot| {
        slot.borrow_mut().take();
    });
    // The test harness calls this after each test. Clear any stray shadow-stack
    // link left behind by unwinding so later explicit collections don't walk a
    // stale frame chain from a prior test.
    crate::garbage_collector::GC_SHADOW_TOP.with(|top| top.set(std::ptr::null_mut()));
}

/// Zero-sized marker type used as the `panic_any` payload for Taro panics
/// in test mode. Lets `catch_unwind` identify and intercept them.
struct TaroPanicPayload;

/// Call a `void()` Taro function and return whether it panicked.
///
/// Sets `IN_TEST_HARNESS` for the duration of the call so that
/// `__rt__panic_unwind_at` uses `panic_any` (catchable by `catch_unwind`)
/// instead of `_Unwind_ForcedUnwind`.
///
/// Returns `true` if the function panicked, `false` if it returned normally.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__test_call_fn(fn_ptr: extern "C-unwind" fn()) -> bool {
    set_test_harness_active(true);

    // Suppress Rust's built-in panic output; Taro's test harness owns reporting.
    let old_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        fn_ptr();
    }))
    .is_err();

    std::panic::set_hook(old_hook);
    set_test_harness_active(false);
    panicked
}

/// Restore a previously captured `PanicReport` into the thread-local so that the
/// next unwind shows the original backtrace and message.
pub(crate) fn restore_panic_report(report: PanicReport) {
    PANIC_ACTIVE.with(|f| f.set(true));
    PANIC_REPORT.with(|slot| {
        *slot.borrow_mut() = Some(report);
    });
}

/// Re-raise the restored panic using the context-appropriate mechanism:
/// - Inside a test or executor catch context: catchable `panic_any`.
/// - Otherwise: forced unwind (crashes the program showing the original backtrace).
pub(crate) fn rethrow_restored_panic() -> ! {
    if IN_TEST_HARNESS.with(Cell::get) || IN_EXECUTOR_CATCH.with(Cell::get) {
        std::panic::panic_any(TaroPanicPayload)
    } else {
        panic_forced_unwind()
    }
}

pub(crate) fn resume_test_panic(message: String) -> ! {
    assert!(
        in_test_harness(),
        "ICE: resume_test_panic called outside test harness mode"
    );
    rethrow_panic_message(message)
}

pub(crate) fn rethrow_panic_message(message: String) -> ! {
    __rt__panic_unwind(RtString {
        ptr: message.as_ptr(),
        len: message.len(),
    })
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

/// The primary Taro panic entry point.
///
/// Records the panic message/location, then raises an unwind using the
/// appropriate mechanism:
///
/// - **Test mode** (`IN_TEST_HARNESS == true`): `panic_any(TaroPanicPayload)`
///   so `catch_unwind` in `__rt__test_call_fn` can intercept it.
/// - **Normal mode** (`IN_TEST_HARNESS == false`): `_Unwind_ForcedUnwind`
///   so cleanup/defer landing pads execute before the stack unwinds to
///   `taro_start`, which calls `__rt__panic_abort_unwind`.
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

    let in_test = IN_TEST_HARNESS.with(|f| f.get());
    let in_exec = IN_EXECUTOR_CATCH.with(|f| f.get());
    if in_test || in_exec {
        // Test mode: raise via Rust's panic so catch_unwind can intercept it.
        std::panic::panic_any(TaroPanicPayload)
    } else {
        // Normal mode: forced unwind runs defer/cleanup landing pads.
        panic_forced_unwind()
    }
}

/// Raises `_Unwind_ForcedUnwind`, which walks the stack running cleanup
/// landing pads (defer blocks) without being catchable by personality
/// functions. The `forced_unwind_stop` callback terminates the unwind at
/// the top of the stack by calling `__rt__panic_abort_unwind`.
#[cold]
fn panic_forced_unwind() -> ! {
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
        // If _Unwind_ForcedUnwind returns, unwinding failed.
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

// ── Platform-specific _Unwind_ForcedUnwind machinery ──────────────────────────

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
