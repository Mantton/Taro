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
const TEST_PANIC_PASSED: u8 = 0;
const TEST_PANIC_UNEXPECTED: u8 = 1;
const TEST_PANIC_MISSING: u8 = 2;
const TEST_PANIC_MESSAGE_MISMATCH: u8 = 3;
#[cfg(all(unix, any(target_arch = "x86_64", target_arch = "aarch64")))]
const TARO_EXCEPTION_CLASS: u64 = u64::from_be_bytes(*b"TAROPAN!");

#[repr(C)]
#[derive(Clone, Copy)]
pub struct RtString {
    pub ptr: *const u8,
    pub len: usize,
}

impl RtString {
    pub(crate) fn to_owned_lossy(self) -> String {
        if self.ptr.is_null() || self.len == 0 {
            return String::new();
        }
        let bytes = unsafe { std::slice::from_raw_parts(self.ptr, self.len) };
        String::from_utf8_lossy(bytes).into_owned()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TaskTraceFrame {
    pub(crate) name: String,
    pub(crate) file: String,
    pub(crate) line: usize,
    pub(crate) column: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PanicReport {
    pub(crate) message: String,
    pub(crate) backtrace: String,
    pub(crate) location: Option<String>,
    pub(crate) logical_stack: Vec<String>,
    pub(crate) task_trace: Vec<TaskTraceFrame>,
}

const PANIC_PAYLOAD_MAGIC: &[u8; 8] = b"TAROPN\0\x02";

fn append_payload_bytes(output: &mut Vec<u8>, bytes: &[u8]) {
    let len = u64::try_from(bytes.len()).expect("panic payload field exceeds u64::MAX bytes");
    output.extend_from_slice(&len.to_le_bytes());
    output.extend_from_slice(bytes);
}

fn read_payload_bytes<'a>(payload: &'a [u8], cursor: &mut usize) -> Option<&'a [u8]> {
    let len_end = cursor.checked_add(std::mem::size_of::<u64>())?;
    let len_bytes: [u8; 8] = payload.get(*cursor..len_end)?.try_into().ok()?;
    *cursor = len_end;
    let len = usize::try_from(u64::from_le_bytes(len_bytes)).ok()?;
    let end = cursor.checked_add(len)?;
    let bytes = payload.get(*cursor..end)?;
    *cursor = end;
    Some(bytes)
}

pub(crate) fn serialize_panic_report(report: &PanicReport) -> Vec<u8> {
    let mut output = Vec::new();
    output.extend_from_slice(PANIC_PAYLOAD_MAGIC);
    append_payload_bytes(&mut output, report.message.as_bytes());
    append_payload_bytes(&mut output, report.backtrace.as_bytes());
    match report.location.as_deref() {
        Some(location) => {
            output.push(1);
            append_payload_bytes(&mut output, location.as_bytes());
        }
        None => output.push(0),
    }
    let frame_count =
        u64::try_from(report.logical_stack.len()).expect("panic logical stack is too large");
    output.extend_from_slice(&frame_count.to_le_bytes());
    for frame in &report.logical_stack {
        append_payload_bytes(&mut output, frame.as_bytes());
    }
    let task_frame_count =
        u64::try_from(report.task_trace.len()).expect("panic task trace is too large");
    output.extend_from_slice(&task_frame_count.to_le_bytes());
    for frame in &report.task_trace {
        append_payload_bytes(&mut output, frame.name.as_bytes());
        append_payload_bytes(&mut output, frame.file.as_bytes());
        output.extend_from_slice(
            &u64::try_from(frame.line)
                .expect("task trace line exceeds u64::MAX")
                .to_le_bytes(),
        );
        output.extend_from_slice(
            &u64::try_from(frame.column)
                .expect("task trace column exceeds u64::MAX")
                .to_le_bytes(),
        );
    }
    output
}

pub(crate) fn deserialize_panic_report(payload: &[u8]) -> Option<PanicReport> {
    if !payload.starts_with(PANIC_PAYLOAD_MAGIC) {
        return None;
    }
    let mut cursor = PANIC_PAYLOAD_MAGIC.len();
    let message = String::from_utf8(read_payload_bytes(payload, &mut cursor)?.to_vec()).ok()?;
    let backtrace = String::from_utf8(read_payload_bytes(payload, &mut cursor)?.to_vec()).ok()?;
    let location = match *payload.get(cursor)? {
        0 => {
            cursor += 1;
            None
        }
        1 => {
            cursor += 1;
            Some(String::from_utf8(read_payload_bytes(payload, &mut cursor)?.to_vec()).ok()?)
        }
        _ => return None,
    };
    let count_end = cursor.checked_add(std::mem::size_of::<u64>())?;
    let count_bytes: [u8; 8] = payload.get(cursor..count_end)?.try_into().ok()?;
    cursor = count_end;
    let frame_count = usize::try_from(u64::from_le_bytes(count_bytes)).ok()?;
    // Every encoded frame needs at least its eight-byte length prefix. Reject
    // impossible counts before reserving attacker- or corruption-controlled
    // capacity, even though payloads are normally private runtime values.
    if frame_count > payload.len().saturating_sub(cursor) / std::mem::size_of::<u64>() {
        return None;
    }
    let mut logical_stack = Vec::with_capacity(frame_count);
    for _ in 0..frame_count {
        logical_stack
            .push(String::from_utf8(read_payload_bytes(payload, &mut cursor)?.to_vec()).ok()?);
    }
    let task_count_end = cursor.checked_add(std::mem::size_of::<u64>())?;
    let task_count_bytes: [u8; 8] = payload.get(cursor..task_count_end)?.try_into().ok()?;
    cursor = task_count_end;
    let task_frame_count = usize::try_from(u64::from_le_bytes(task_count_bytes)).ok()?;
    let minimum_task_frame_size = 4 * std::mem::size_of::<u64>();
    if task_frame_count > payload.len().saturating_sub(cursor) / minimum_task_frame_size {
        return None;
    }
    let mut task_trace = Vec::with_capacity(task_frame_count);
    for _ in 0..task_frame_count {
        let name = String::from_utf8(read_payload_bytes(payload, &mut cursor)?.to_vec()).ok()?;
        let file = String::from_utf8(read_payload_bytes(payload, &mut cursor)?.to_vec()).ok()?;
        let line_end = cursor.checked_add(std::mem::size_of::<u64>())?;
        let line_bytes: [u8; 8] = payload.get(cursor..line_end)?.try_into().ok()?;
        cursor = line_end;
        let column_end = cursor.checked_add(std::mem::size_of::<u64>())?;
        let column_bytes: [u8; 8] = payload.get(cursor..column_end)?.try_into().ok()?;
        cursor = column_end;
        task_trace.push(TaskTraceFrame {
            name,
            file,
            line: usize::try_from(u64::from_le_bytes(line_bytes)).ok()?,
            column: usize::try_from(u64::from_le_bytes(column_bytes)).ok()?,
        });
    }
    if cursor != payload.len() {
        return None;
    }
    Some(PanicReport {
        message,
        backtrace,
        location,
        logical_stack,
        task_trace,
    })
}

pub(crate) fn serialized_panic_message(payload: &[u8]) -> Option<&[u8]> {
    if !payload.starts_with(PANIC_PAYLOAD_MAGIC) {
        return None;
    }
    let mut cursor = PANIC_PAYLOAD_MAGIC.len();
    read_payload_bytes(payload, &mut cursor)
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

    install_taro_panic_hook();

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));

    IN_EXECUTOR_CATCH.with(|flag| flag.set(previous));

    match result {
        Ok(value) => Ok(value),
        Err(_) => {
            let report = take_full_panic_report().unwrap_or_else(|| PanicReport {
                message: "task panicked on executor worker".into(),
                backtrace: String::new(),
                location: None,
                logical_stack: Vec::new(),
                task_trace: Vec::new(),
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
                task_trace: Vec::new(),
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
            task_trace: Vec::new(),
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

    if symbol.starts_with("taro_runtime::")
        || symbol.starts_with("rt__")
        || symbol.starts_with("gc__")
    {
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
            if let (Some(prev_index), Some(prev_symbol)) =
                (current_index.take(), current_symbol.take())
            {
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

fn render_task_trace(frames: &[TaskTraceFrame]) -> String {
    if frames.is_empty() {
        return String::new();
    }
    const MAX_TASK_FRAMES: usize = 32;
    let mut lines = Vec::new();
    for (idx, frame) in frames.iter().rev().take(MAX_TASK_FRAMES).enumerate() {
        let file = if frame.file.is_empty() {
            "<unknown>"
        } else {
            &frame.file
        };
        let location = match (frame.line, frame.column) {
            (0, _) => file.to_string(),
            (line, 0) => format!("{file}:{line}"),
            (line, column) => format!("{file}:{line}:{column}"),
        };
        lines.push(format!(
            "  {idx:>2}: spawned `{}` at {location}",
            frame.name
        ));
    }
    if frames.len() > MAX_TASK_FRAMES {
        lines.push(format!(
            "  ... {} older spawn(s) omitted",
            frames.len() - MAX_TASK_FRAMES
        ));
    }
    lines.join("\n")
}

fn write_captured_report(
    output: &mut impl Write,
    headline: &str,
    report: &PanicReport,
    policy: BacktracePolicy,
) {
    let _ = writeln!(output, "{headline}: {}", report.message);
    if let Some(location) = report.location.as_ref() {
        let _ = writeln!(output, "  at {location}");
    }
    if matches!(policy, BacktracePolicy::Compact) {
        let logical = render_logical_stack(&report.logical_stack);
        if !logical.is_empty() {
            let _ = writeln!(output, "taro stack:");
            let _ = writeln!(output, "{logical}");
        } else {
            let _ = writeln!(output, "stack backtrace:");
            let _ = writeln!(output, "{}", render_panic_backtrace(&report.backtrace));
        }
    } else {
        let _ = writeln!(output, "stack backtrace:");
        let _ = writeln!(output, "{}", render_panic_backtrace(&report.backtrace));
    }
    let task_trace = render_task_trace(&report.task_trace);
    if !task_trace.is_empty() {
        let _ = writeln!(output, "async task trace:");
        let _ = writeln!(output, "{task_trace}");
    }
}

pub(crate) fn write_unobserved_task_panic(report: &PanicReport) {
    let mut stderr = std::io::stderr().lock();
    write_captured_report(
        &mut stderr,
        "unobserved task panic",
        report,
        backtrace_policy(),
    );
    let _ = stderr.flush();
}

pub(crate) fn write_report(default_message: &str) {
    let mut stderr = std::io::stderr().lock();
    let policy = backtrace_policy();
    let report = PANIC_REPORT.with(|slot| slot.borrow().clone());

    if let Some(report) = report.as_ref() {
        write_captured_report(&mut stderr, "panic", report, policy);
    } else {
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

fn classify_test_panic(
    panicked: bool,
    expect_panic: bool,
    expected_message: &str,
    actual_message: Option<&str>,
) -> u8 {
    match (panicked, expect_panic) {
        (false, false) => TEST_PANIC_PASSED,
        (false, true) => TEST_PANIC_MISSING,
        (true, false) => TEST_PANIC_UNEXPECTED,
        (true, true)
            if !expected_message.is_empty()
                && !actual_message
                    .unwrap_or_default()
                    .contains(expected_message) =>
        {
            TEST_PANIC_MESSAGE_MISMATCH
        }
        (true, true) => TEST_PANIC_PASSED,
    }
}

/// Classify one test's panic outcome without consuming the report. A non-empty
/// expected message uses substring matching so callers can assert the stable,
/// relevant portion of a panic without coupling tests to incidental context.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__test_panic_status(
    panicked: bool,
    expect_panic: bool,
    expected_message_ptr: *const u8,
    expected_message_len: usize,
) -> u8 {
    let expected_message = if expected_message_ptr.is_null() || expected_message_len == 0 {
        String::new()
    } else {
        let bytes =
            unsafe { std::slice::from_raw_parts(expected_message_ptr, expected_message_len) };
        String::from_utf8_lossy(bytes).into_owned()
    };
    PANIC_REPORT.with(|slot| {
        let report = slot.borrow();
        classify_test_panic(
            panicked,
            expect_panic,
            &expected_message,
            report.as_ref().map(|report| report.message.as_str()),
        )
    })
}

/// Emit actionable details for a failed test panic classification, then reset
/// all per-test panic and shadow-stack state. The harness prints its one-line
/// result before calling this function, so flush C stdio before writing the
/// multi-line diagnostic through Rust's stderr handle.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__test_panic_finish(
    status: u8,
    expected_message_ptr: *const u8,
    expected_message_len: usize,
) {
    if matches!(status, TEST_PANIC_UNEXPECTED | TEST_PANIC_MESSAGE_MISMATCH) {
        unsafe {
            libc::fflush(std::ptr::null_mut());
        }
    }

    if status == TEST_PANIC_MESSAGE_MISMATCH {
        let expected_message = if expected_message_ptr.is_null() || expected_message_len == 0 {
            String::new()
        } else {
            let bytes =
                unsafe { std::slice::from_raw_parts(expected_message_ptr, expected_message_len) };
            String::from_utf8_lossy(bytes).into_owned()
        };
        let mut stderr = std::io::stderr().lock();
        let _ = writeln!(
            stderr,
            "  expected panic message containing: {expected_message:?}"
        );
        let _ = stderr.flush();
        drop(stderr);
        write_report("test panicked without a recorded message");
    } else if status == TEST_PANIC_UNEXPECTED {
        write_report("test panicked without a recorded message");
    }

    __rt__panic_clear();
}

/// Clears the panic state after a caught panic so the next test can run cleanly.
///
/// Called by `__rt__test_panic_finish` and kept as a small public runtime ABI
/// helper. Returning `void` avoids ARM64 sret ABI complications.
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

fn install_taro_panic_hook() {
    static INSTALL: std::sync::Once = std::sync::Once::new();
    INSTALL.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if info.payload().is::<TaroPanicPayload>() {
                return;
            }
            previous(info);
        }));
    });
}

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
    install_taro_panic_hook();

    let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        fn_ptr();
    }))
    .is_err();

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
        BacktracePolicy, FrameKind, PanicReport, TEST_PANIC_MESSAGE_MISMATCH, TEST_PANIC_MISSING,
        TEST_PANIC_PASSED, TEST_PANIC_UNEXPECTED, TaskTraceFrame, classify_test_panic,
        deserialize_panic_report, parse_backtrace_frames, parse_backtrace_policy,
        render_panic_backtrace_with_policy, serialize_panic_report, serialized_panic_message,
        write_captured_report,
    };

    #[test]
    fn panic_payload_serialization_round_trips_every_report_field() {
        let report = PanicReport {
            message: "child failed".into(),
            backtrace: "frame one\nframe two".into(),
            location: Some("src/main.tr:12:7".into()),
            logical_stack: vec!["app__bt_usr__main".into(), "std__bt_std__task".into()],
            task_trace: vec![TaskTraceFrame {
                name: "worker".into(),
                file: "src/main.tr".into(),
                line: 8,
                column: 3,
            }],
        };

        let encoded = serialize_panic_report(&report);
        assert_eq!(
            serialized_panic_message(&encoded),
            Some(b"child failed".as_slice())
        );
        assert_eq!(deserialize_panic_report(&encoded), Some(report));
    }

    #[test]
    fn panic_payload_deserialization_rejects_corrupt_data() {
        let report = PanicReport {
            message: "child failed".into(),
            backtrace: String::new(),
            location: None,
            logical_stack: Vec::new(),
            task_trace: Vec::new(),
        };
        let mut encoded = serialize_panic_report(&report);
        encoded.push(0xff);
        assert!(deserialize_panic_report(&encoded).is_none());

        let mut impossible_count = serialize_panic_report(&report);
        let count_offset = impossible_count.len() - std::mem::size_of::<u64>();
        impossible_count[count_offset..].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(deserialize_panic_report(&impossible_count).is_none());
        assert!(serialized_panic_message(b"not a panic payload").is_none());
    }

    #[test]
    fn captured_task_reports_use_unobserved_headline() {
        let report = PanicReport {
            message: "detached child failed".into(),
            backtrace: String::new(),
            location: Some("src/main.tr:4:5".into()),
            logical_stack: vec!["app__bt_usr__child".into()],
            task_trace: vec![TaskTraceFrame {
                name: "child".into(),
                file: "src/main.tr".into(),
                line: 3,
                column: 9,
            }],
        };
        let mut rendered = Vec::new();
        write_captured_report(
            &mut rendered,
            "unobserved task panic",
            &report,
            BacktracePolicy::Compact,
        );
        let rendered = String::from_utf8(rendered).unwrap();
        assert!(rendered.starts_with("unobserved task panic: detached child failed\n"));
        assert!(rendered.contains("  at src/main.tr:4:5"));
        assert!(rendered.contains("taro stack:"));
        assert!(rendered.contains("async task trace:"));
        assert!(rendered.contains("spawned `child` at src/main.tr:3:9"));
    }

    #[test]
    fn test_panic_classification_enforces_expected_message_substrings() {
        assert_eq!(
            classify_test_panic(
                true,
                true,
                "stable detail",
                Some("prefix stable detail suffix")
            ),
            TEST_PANIC_PASSED
        );
        assert_eq!(
            classify_test_panic(true, true, "different detail", Some("actual panic")),
            TEST_PANIC_MESSAGE_MISMATCH
        );
        assert_eq!(
            classify_test_panic(true, true, "", Some("any panic")),
            TEST_PANIC_PASSED
        );
        assert_eq!(
            classify_test_panic(false, true, "expected", None),
            TEST_PANIC_MISSING
        );
        assert_eq!(
            classify_test_panic(true, false, "", Some("unexpected")),
            TEST_PANIC_UNEXPECTED
        );
        assert_eq!(
            classify_test_panic(false, false, "", None),
            TEST_PANIC_PASSED
        );
    }

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
