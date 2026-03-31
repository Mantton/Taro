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
    pub(crate) logical_stack: Vec<String>,
}

#[derive(Clone, Copy)]
struct LogicalFrameRaw {
    ptr: *const u8,
    len: usize,
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
    /// Logical (language-level) call stack captured via compiler/runtime push/pop.
    /// Entries are symbol byte slices backed by static binary data.
    static LOGICAL_STACK: RefCell<Vec<LogicalFrameRaw>> = const { RefCell::new(Vec::new()) };
}

pub(crate) fn in_test_harness() -> bool {
    IN_TEST_HARNESS.with(Cell::get)
}

pub(crate) fn set_test_harness_active(active: bool) {
    IN_TEST_HARNESS.with(|flag| flag.set(active));
}

fn snapshot_logical_stack() -> Vec<String> {
    LOGICAL_STACK.with(|stack| {
        stack
            .borrow()
            .iter()
            .filter_map(|frame| {
                if frame.ptr.is_null() || frame.len == 0 {
                    return None;
                }
                let bytes = unsafe { std::slice::from_raw_parts(frame.ptr, frame.len) };
                Some(String::from_utf8_lossy(bytes).into_owned())
            })
            .collect()
    })
}

fn clear_logical_stack() {
    LOGICAL_STACK.with(|stack| stack.borrow_mut().clear());
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__logical_stack_push(symbol: RtString) {
    if symbol.ptr.is_null() || symbol.len == 0 {
        return;
    }
    LOGICAL_STACK.with(|stack| {
        stack.borrow_mut().push(LogicalFrameRaw {
            ptr: symbol.ptr,
            len: symbol.len,
        });
    });
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__logical_stack_pop() {
    LOGICAL_STACK.with(|stack| {
        let _ = stack.borrow_mut().pop();
    });
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
                logical_stack: Vec::new(),
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
    clear_logical_stack();
    if was_active {
        return report.or_else(|| {
            Some(PanicReport {
                message: String::new(),
                backtrace: String::new(),
                location: None,
                logical_stack: Vec::new(),
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
    let logical_stack = snapshot_logical_stack();
    PANIC_REPORT.with(|slot| {
        *slot.borrow_mut() = Some(PanicReport {
            message,
            backtrace,
            location,
            logical_stack,
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
    clear_logical_stack();
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BacktracePolicy {
    Compact,
    Full,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FrameKind {
    User,
    Std,
    Synthetic,
    Entry,
    Runtime,
    Toolchain,
    Native,
    Unknown,
}

#[derive(Clone, Debug)]
struct ParsedFrame {
    _index: usize,
    _symbol: String,
    lines: Vec<String>,
    kind: FrameKind,
}

fn parse_backtrace_policy(raw: Option<&str>) -> BacktracePolicy {
    if raw.is_some_and(|value| value.eq_ignore_ascii_case("full")) {
        BacktracePolicy::Full
    } else {
        BacktracePolicy::Compact
    }
}

fn backtrace_policy() -> BacktracePolicy {
    let value = std::env::var("TARO_BACKTRACE").ok();
    parse_backtrace_policy(value.as_deref())
}

fn parse_frame_header(line: &str) -> Option<(usize, &str)> {
    let trimmed = line.trim_start();
    let colon = trimmed.find(':')?;
    let (index_raw, rest_with_colon) = trimmed.split_at(colon);
    if index_raw.is_empty() || !index_raw.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    let index = index_raw.parse::<usize>().ok()?;
    let after_colon = rest_with_colon[1..].trim_start();
    let symbol = if let Some((_, symbol)) = after_colon.split_once(" - ") {
        symbol.trim()
    } else {
        after_colon.trim()
    };
    Some((index, symbol))
}

fn classify_frame(symbol: &str) -> FrameKind {
    let symbol = symbol.trim_start_matches('_');

    if symbol == "taro_start" {
        return FrameKind::Entry;
    }

    if symbol.contains("__bt_usr__") {
        return FrameKind::User;
    }
    if symbol.contains("__bt_std__") {
        return FrameKind::Std;
    }
    if symbol.contains("__bt_syn__") {
        return FrameKind::Synthetic;
    }

    if symbol.starts_with("taro_runtime::") || symbol.starts_with("rt__") || symbol.starts_with("gc__") {
        return FrameKind::Runtime;
    }

    if symbol.starts_with("std::")
        || symbol.starts_with("core::")
        || symbol.starts_with("alloc::")
        || symbol.starts_with("test::")
        || symbol.starts_with("backtrace_rs::")
        || symbol.starts_with("rust_begin_unwind")
        || symbol.starts_with("___rust_try")
    {
        return FrameKind::Toolchain;
    }

    if symbol.starts_with("__pthread")
        || symbol.starts_with("pthread_")
        || symbol.starts_with("libsystem_")
    {
        return FrameKind::Native;
    }

    if let Some((pkg, _)) = symbol.split_once("__") {
        if pkg == "std" {
            return FrameKind::Std;
        }
        if !pkg.is_empty() && pkg.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
            return FrameKind::User;
        }
    }

    FrameKind::Unknown
}

fn parse_backtrace_frames(backtrace: &str) -> Vec<ParsedFrame> {
    let mut frames = Vec::new();
    let mut current_index: Option<usize> = None;
    let mut current_symbol: Option<String> = None;
    let mut current_lines: Vec<String> = Vec::new();

    for line in backtrace.lines() {
        if let Some((index, symbol)) = parse_frame_header(line) {
            if let (Some(prev_index), Some(prev_symbol)) = (current_index.take(), current_symbol.take()) {
                frames.push(ParsedFrame {
                    _index: prev_index,
                    kind: classify_frame(&prev_symbol),
                    _symbol: prev_symbol,
                    lines: std::mem::take(&mut current_lines),
                });
            }
            current_index = Some(index);
            current_symbol = Some(symbol.to_string());
            current_lines.push(line.to_string());
        } else if current_index.is_some() {
            current_lines.push(line.to_string());
        }
    }

    if let (Some(last_index), Some(last_symbol)) = (current_index, current_symbol) {
        frames.push(ParsedFrame {
            _index: last_index,
            kind: classify_frame(&last_symbol),
            _symbol: last_symbol,
            lines: current_lines,
        });
    }

    frames
}

fn render_panic_backtrace_with_policy(backtrace: &str, policy: BacktracePolicy) -> String {
    if matches!(policy, BacktracePolicy::Full) {
        return backtrace.to_string();
    }

    let frames = parse_backtrace_frames(backtrace);

    let mut filtered = Vec::new();
    for frame in &frames {
        if matches!(
            frame.kind,
            FrameKind::User | FrameKind::Std | FrameKind::Synthetic | FrameKind::Entry
        ) {
            filtered.extend(frame.lines.iter().cloned());
        }
    }
    if !filtered.is_empty() {
        return filtered.join("\n");
    }

    let mut fallback = Vec::new();
    for frame in frames.iter().take(6) {
        fallback.extend(frame.lines.iter().cloned());
    }
    if !fallback.is_empty() {
        return fallback.join("\n");
    }

    let condensed: Vec<_> = backtrace.lines().take(12).collect();
    if !condensed.is_empty() {
        condensed.join("\n")
    } else {
        "<no backtrace available>".to_string()
    }
}

fn render_panic_backtrace(backtrace: &str) -> String {
    render_panic_backtrace_with_policy(backtrace, backtrace_policy())
}

fn format_logical_symbol(symbol: &str) -> String {
    let symbol = symbol.trim_start_matches('_');
    let Some((pkg, rest)) = symbol.split_once("__") else {
        return symbol.to_string();
    };
    let (kind_tag, rest) = if let Some(rest) = rest.strip_prefix("bt_usr__") {
        ("usr", rest)
    } else if let Some(rest) = rest.strip_prefix("bt_std__") {
        ("std", rest)
    } else if let Some(rest) = rest.strip_prefix("bt_syn__") {
        ("syn", rest)
    } else {
        ("", rest)
    };

    let mut display = format!("{pkg}::{}", rest.replace("__", "::"));
    if let Some(pos) = display.rfind("::h") {
        let hash = &display[pos + 3..];
        if hash.len() == 16 && hash.bytes().all(|b| b.is_ascii_hexdigit()) {
            display.truncate(pos);
        }
    }
    if kind_tag.is_empty() {
        display
    } else {
        format!("[{kind_tag}] {display}")
    }
}

fn render_logical_stack(frames: &[String]) -> String {
    if frames.is_empty() {
        return String::new();
    }
    const MAX_LOGICAL_FRAMES: usize = 64;
    let mut lines = Vec::new();
    for (idx, frame) in frames.iter().rev().take(MAX_LOGICAL_FRAMES).enumerate() {
        lines.push(format!("  {idx:>2}: {}", format_logical_symbol(frame)));
    }
    if frames.len() > MAX_LOGICAL_FRAMES {
        lines.push(format!(
            "  ... {} older frame(s) omitted",
            frames.len() - MAX_LOGICAL_FRAMES
        ));
    }
    lines.join("\n")
}

pub(crate) fn write_report(default_message: &str) {
    let mut stderr = std::io::stderr().lock();
    let mut had_report = false;
    let policy = backtrace_policy();

    PANIC_REPORT.with(|slot| {
        if let Some(report) = slot.borrow().as_ref() {
            had_report = true;
            let _ = writeln!(stderr, "panic: {}", report.message);
            if let Some(location) = report.location.as_ref() {
                let _ = writeln!(stderr, "  at {}", location);
            }
            if matches!(policy, BacktracePolicy::Compact) {
                let logical = render_logical_stack(&report.logical_stack);
                if !logical.is_empty() {
                    let _ = writeln!(stderr, "taro stack:");
                    let _ = writeln!(stderr, "{logical}");
                } else {
                    let _ = writeln!(stderr, "stack backtrace:");
                    let _ = writeln!(stderr, "{}", render_panic_backtrace(&report.backtrace));
                }
            } else {
                let _ = writeln!(stderr, "stack backtrace:");
                let _ = writeln!(stderr, "{}", render_panic_backtrace(&report.backtrace));
            }
        }
    });

    if !had_report {
        let raw_backtrace = format!("{:#}", Backtrace::force_capture());
        let _ = writeln!(stderr, "panic: {}", default_message);
        if matches!(policy, BacktracePolicy::Compact) {
            let logical = render_logical_stack(&snapshot_logical_stack());
            if !logical.is_empty() {
                let _ = writeln!(stderr, "taro stack:");
                let _ = writeln!(stderr, "{logical}");
            } else {
                let _ = writeln!(stderr, "stack backtrace:");
                let _ = writeln!(stderr, "{}", render_panic_backtrace(&raw_backtrace));
            }
        } else {
            let _ = writeln!(stderr, "stack backtrace:");
            let _ = writeln!(stderr, "{}", render_panic_backtrace(&raw_backtrace));
        }
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
    clear_logical_stack();

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
    clear_logical_stack();
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

#[cfg(test)]
mod tests {
    use super::{
        BacktracePolicy, FrameKind, parse_backtrace_frames, parse_backtrace_policy,
        render_panic_backtrace_with_policy,
    };

    #[test]
    fn parse_backtrace_frames_classifies_compiler_tagged_symbols() {
        let raw = r#"   0: 0x1000 - std::panicking::begin_panic
   1: 0x1001 - taro_runtime::panic_unwind::write_report
   2: 0x1002 - ___rt__panic_unwind_at
   3: 0x1003 - ___rust_try
   4: 0x1004 - _app__bt_usr__mod__boom
   5: 0x1005 - _std__bt_std__task__join
   6: 0x1006 - _std__bt_syn__missing_p1_d7_poll
   7: 0x1007 - _taro_start
   8: 0x1008 - __pthread_kill"#;
        let frames = parse_backtrace_frames(raw);
        let kinds: Vec<_> = frames.iter().map(|f| f.kind).collect();
        assert!(kinds.contains(&FrameKind::User));
        assert!(kinds.contains(&FrameKind::Std));
        assert!(kinds.contains(&FrameKind::Synthetic));
        assert!(kinds.contains(&FrameKind::Entry));
        assert!(kinds.contains(&FrameKind::Runtime));
        assert!(kinds.contains(&FrameKind::Toolchain));
        assert!(kinds.contains(&FrameKind::Native));
    }

    #[test]
    fn render_panic_backtrace_compact_keeps_taro_frames_and_drops_runtime_noise() {
        let raw = r#"   0: 0x1000 - std::panicking::begin_panic
   1: 0x1001 - taro_runtime::panic_unwind::write_report
   2: 0x1002 - ___rt__panic_unwind_at
   3: 0x1003 - ___rust_try
   4: 0x1004 - _app__bt_usr__mod__boom
   5: 0x1005 - _std__bt_std__task__join
   6: 0x1006 - _std__bt_syn__missing_p1_d7_poll
   7: 0x1007 - _taro_start
   8: 0x1008 - __pthread_kill"#;
        let rendered = render_panic_backtrace_with_policy(raw, BacktracePolicy::Compact);
        assert!(rendered.contains("_app__bt_usr__mod__boom"));
        assert!(rendered.contains("_std__bt_std__task__join"));
        assert!(rendered.contains("_std__bt_syn__missing_p1_d7_poll"));
        assert!(rendered.contains("_taro_start"));
        assert!(!rendered.contains("std::panicking::begin_panic"));
        assert!(!rendered.contains("taro_runtime::panic_unwind::write_report"));
        assert!(!rendered.contains("___rt__panic_unwind_at"));
        assert!(!rendered.contains("___rust_try"));
        assert!(!rendered.contains("__pthread_kill"));
    }

    #[test]
    fn render_panic_backtrace_falls_back_to_short_raw_when_no_taro_frames() {
        let raw = r#"   0: 0x2000 - std::panicking::begin_panic
   1: 0x2001 - taro_runtime::panic_unwind::write_report
   2: 0x2002 - ___rust_try
   3: 0x2003 - __pthread_kill"#;
        let rendered = render_panic_backtrace_with_policy(raw, BacktracePolicy::Compact);
        assert!(!rendered.is_empty());
        assert!(rendered.contains("std::panicking::begin_panic"));
    }

    #[test]
    fn render_panic_backtrace_full_policy_keeps_original_text() {
        let raw = r#"   0: 0x3000 - std::panicking::begin_panic
   1: 0x3001 - _app__bt_usr__mod__boom"#;
        let rendered = render_panic_backtrace_with_policy(raw, BacktracePolicy::Full);
        assert_eq!(rendered, raw);
    }

    #[test]
    fn parse_backtrace_policy_defaults_to_compact() {
        assert_eq!(parse_backtrace_policy(None), BacktracePolicy::Compact);
        assert_eq!(
            parse_backtrace_policy(Some("compact")),
            BacktracePolicy::Compact
        );
        assert_eq!(parse_backtrace_policy(Some("full")), BacktracePolicy::Full);
        assert_eq!(parse_backtrace_policy(Some("FuLl")), BacktracePolicy::Full);
    }
}
