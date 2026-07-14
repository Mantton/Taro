//! Stable Unix subprocess shims for the Taro standard library.
//!
//! Process creation stays in Rust's standard library instead of exposing
//! `fork` to Taro. The runtime already owns worker, cleanup, and collector
//! threads; running arbitrary managed code between `fork` and `exec` would be
//! unsound in that environment. The ABI below copies raw Unix bytes, executes
//! argv directly, and keeps child ownership in a registry so abandoned
//! children can be reaped without killing them.

use crate::env::lock_process_state;
use crate::panic_unwind::RtString;
use std::collections::{HashMap, VecDeque};
use std::ffi::OsString;
use std::io::{self, Read};
use std::os::fd::IntoRawFd;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::os::unix::process::ExitStatusExt;
use std::path::PathBuf;
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, LazyLock, Mutex, MutexGuard, OnceLock};

const STDIO_NULL: u8 = 0;
const STDIO_INHERIT: u8 = 1;
const STDIO_PIPED: u8 = 2;

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

fn input_program(value: RtString) -> Result<OsString, i32> {
    let bytes = input_bytes(value)?;
    if bytes.is_empty() {
        return Err(libc::EINVAL);
    }
    Ok(OsString::from_vec(bytes))
}

fn input_os_string(value: RtString) -> Result<OsString, i32> {
    Ok(OsString::from_vec(input_bytes(value)?))
}

fn input_env_name(value: RtString) -> Result<OsString, i32> {
    let bytes = input_bytes(value)?;
    if bytes.is_empty() || bytes.contains(&b'=') {
        return Err(libc::EINVAL);
    }
    Ok(OsString::from_vec(bytes))
}

#[derive(Clone, Copy)]
struct StdioConfig {
    stdin: u8,
    stdout: u8,
    stderr: u8,
}

struct CommandConfig {
    program: OsString,
    arguments: Vec<OsString>,
    environment: Vec<(OsString, OsString)>,
    current_dir: Option<PathBuf>,
    stdio: StdioConfig,
}

impl CommandConfig {
    fn new(program: OsString) -> Self {
        Self {
            program,
            arguments: Vec::new(),
            environment: Vec::new(),
            current_dir: None,
            // Go's nil Cmd streams use the null device. Requiring an explicit
            // `.inherit` avoids accidental terminal access in libraries and
            // test runners while retaining a concise opt-in for CLI tools.
            stdio: StdioConfig {
                stdin: STDIO_NULL,
                stdout: STDIO_NULL,
                stderr: STDIO_NULL,
            },
        }
    }

    fn make_command(&self, capture_output: bool) -> Command {
        let mut command = Command::new(&self.program);
        command.args(&self.arguments);
        for (name, value) in &self.environment {
            // Repeated calls intentionally preserve "last value wins", the
            // same rule used by Go and by ordinary environment maps.
            command.env(name, value);
        }

        if let Some(directory) = &self.current_dir {
            command.current_dir(directory);
            if !self
                .environment
                .iter()
                .any(|(name, _)| name.as_bytes() == b"PWD")
            {
                // On Unix the kernel stores a directory identity, not its
                // spelling. Supplying PWD preserves an explicitly selected
                // symlink spelling for programs that honor it, matching Go.
                command.env("PWD", directory.as_os_str());
            }
        }

        command.stdin(stdio(self.stdio.stdin));
        if capture_output {
            command.stdout(Stdio::piped());
            command.stderr(Stdio::piped());
        } else {
            command.stdout(stdio(self.stdio.stdout));
            command.stderr(stdio(self.stdio.stderr));
        }
        command
    }
}

fn stdio(mode: u8) -> Stdio {
    match mode {
        STDIO_INHERIT => Stdio::inherit(),
        STDIO_PIPED => Stdio::piped(),
        // Invalid values are rejected at the ABI setter. Keeping null as the
        // defensive fallback prevents a malformed foreign caller from gaining
        // access to the parent's terminal.
        _ => Stdio::null(),
    }
}

fn valid_stdio(mode: u8) -> bool {
    matches!(mode, STDIO_NULL | STDIO_INHERIT | STDIO_PIPED)
}

fn command_config_mut(handle: usize) -> Result<&'static mut CommandConfig, i32> {
    if handle == 0 {
        return Err(libc::EBADF);
    }
    Ok(unsafe { &mut *(handle as *mut CommandConfig) })
}

fn command_config(handle: usize) -> Result<&'static CommandConfig, i32> {
    if handle == 0 {
        return Err(libc::EBADF);
    }
    Ok(unsafe { &*(handle as *const CommandConfig) })
}

fn spawn_locked(command: &mut Command) -> io::Result<Child> {
    // Spawning snapshots both inherited environment and (when no explicit
    // child directory was supplied) the process cwd. Use the same lock as
    // std.env so a Taro mutation cannot split that snapshot in two.
    let _guard = lock_process_state();
    command.spawn()
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_command_open(program: RtString, error_out: *mut i32) -> usize {
    if error_out.is_null() {
        return 0;
    }
    unsafe { error_out.write(0) };

    let program = match input_program(program) {
        Ok(program) => program,
        Err(code) => {
            unsafe { error_out.write(code) };
            return 0;
        }
    };
    Box::into_raw(Box::new(CommandConfig::new(program))) as usize
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_command_arg(handle: usize, argument: RtString) -> i32 {
    let config = match command_config_mut(handle) {
        Ok(config) => config,
        Err(code) => return code,
    };
    let argument = match input_os_string(argument) {
        Ok(argument) => argument,
        Err(code) => return code,
    };
    config.arguments.push(argument);
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_command_env(handle: usize, name: RtString, value: RtString) -> i32 {
    let config = match command_config_mut(handle) {
        Ok(config) => config,
        Err(code) => return code,
    };
    let name = match input_env_name(name) {
        Ok(name) => name,
        Err(code) => return code,
    };
    let value = match input_os_string(value) {
        Ok(value) => value,
        Err(code) => return code,
    };
    config.environment.push((name, value));
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_command_current_dir(handle: usize, path: RtString) -> i32 {
    let config = match command_config_mut(handle) {
        Ok(config) => config,
        Err(code) => return code,
    };
    let path = match input_os_string(path) {
        Ok(path) => path,
        Err(code) => return code,
    };
    if path.is_empty() {
        return libc::EINVAL;
    }
    config.current_dir = Some(PathBuf::from(path));
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_command_stdio(
    handle: usize,
    stdin_mode: u8,
    stdout_mode: u8,
    stderr_mode: u8,
) -> i32 {
    if !valid_stdio(stdin_mode) || !valid_stdio(stdout_mode) || !valid_stdio(stderr_mode) {
        return libc::EINVAL;
    }
    let config = match command_config_mut(handle) {
        Ok(config) => config,
        Err(code) => return code,
    };
    config.stdio = StdioConfig {
        stdin: stdin_mode,
        stdout: stdout_mode,
        stderr: stderr_mode,
    };
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_command_close(handle: usize) {
    if handle != 0 {
        unsafe { drop(Box::from_raw(handle as *mut CommandConfig)) };
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ExitStatusWire {
    code: i32,
    signal: i32,
}

fn exit_status_wire(status: std::process::ExitStatus) -> ExitStatusWire {
    ExitStatusWire {
        code: status.code().unwrap_or(-1),
        signal: status.signal().unwrap_or(-1),
    }
}

fn wait_until_exited_without_reaping(pid: u32) -> io::Result<()> {
    let mut status = std::mem::MaybeUninit::<libc::siginfo_t>::uninit();
    loop {
        let result = unsafe {
            libc::waitid(
                libc::P_PID,
                pid as libc::id_t,
                status.as_mut_ptr(),
                libc::WEXITED | libc::WNOWAIT,
            )
        };
        if result == 0 {
            return Ok(());
        }
        let error = io::Error::last_os_error();
        if error.kind() != io::ErrorKind::Interrupted {
            return Err(error);
        }
    }
}

enum ChildPhase {
    Running(Child),
    Waiting,
    Exited(ExitStatusWire),
}

struct ChildEntry {
    pid: u32,
    phase: Mutex<ChildPhase>,
    changed: Condvar,
}

impl ChildEntry {
    fn new(child: Child) -> Self {
        Self {
            pid: child.id(),
            phase: Mutex::new(ChildPhase::Running(child)),
            changed: Condvar::new(),
        }
    }

    fn lock_phase(&self) -> MutexGuard<'_, ChildPhase> {
        self.phase
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    fn wait(&self) -> Result<ExitStatusWire, i32> {
        loop {
            let mut phase = self.lock_phase();
            match &*phase {
                ChildPhase::Exited(status) => return Ok(*status),
                ChildPhase::Waiting => {
                    phase = self
                        .changed
                        .wait(phase)
                        .unwrap_or_else(|poisoned| poisoned.into_inner());
                    drop(phase);
                    continue;
                }
                ChildPhase::Running(_) => {}
            }

            let ChildPhase::Running(mut child) =
                std::mem::replace(&mut *phase, ChildPhase::Waiting)
            else {
                unreachable!("running child phase changed while locked")
            };
            drop(phase);

            // Observe exit without reaping first. The zombie retains its PID,
            // so a concurrent kill can safely use the recorded PID while the
            // phase is Waiting. Reap only after reacquiring the phase lock and
            // publish Exited before releasing it; this closes the otherwise
            // dangerous PID-reuse window between wait(2) and cached status.
            let observed = wait_until_exited_without_reaping(self.pid);
            let mut phase = self.lock_phase();
            if let Err(error) = observed {
                *phase = ChildPhase::Running(child);
                self.changed.notify_all();
                return Err(error_code(error));
            }

            match child.wait() {
                Ok(status) => {
                    let status = exit_status_wire(status);
                    *phase = ChildPhase::Exited(status);
                    self.changed.notify_all();
                    return Ok(status);
                }
                Err(error) => {
                    // A transient wait failure must not discard the only child
                    // handle. Restore it so a later wait or the reaper can try
                    // again instead of leaking a zombie.
                    *phase = ChildPhase::Running(child);
                    self.changed.notify_all();
                    return Err(error_code(error));
                }
            }
        }
    }

    fn try_wait(&self) -> Result<Option<ExitStatusWire>, i32> {
        let mut phase = self.lock_phase();
        match &mut *phase {
            ChildPhase::Exited(status) => Ok(Some(*status)),
            // Another thread owns the blocking wait. tryWait remains
            // non-blocking and will observe the cached result on a later call.
            ChildPhase::Waiting => Ok(None),
            ChildPhase::Running(child) => match child.try_wait() {
                Ok(Some(status)) => {
                    let status = exit_status_wire(status);
                    *phase = ChildPhase::Exited(status);
                    self.changed.notify_all();
                    Ok(Some(status))
                }
                Ok(None) => Ok(None),
                Err(error) => Err(error_code(error)),
            },
        }
    }

    fn kill(&self) -> Result<(), i32> {
        let mut phase = self.lock_phase();
        match &mut *phase {
            ChildPhase::Exited(_) => Err(libc::EBADF),
            ChildPhase::Waiting => {
                // Waiting uses waitid(WNOWAIT), so even an already-exited
                // child remains an unreaped zombie with an unreusable PID
                // until Exited is published under this same lock.
                let result = unsafe { libc::kill(self.pid as libc::pid_t, libc::SIGKILL) };
                if result == 0 {
                    Ok(())
                } else {
                    Err(error_code(io::Error::last_os_error()))
                }
            }
            ChildPhase::Running(child) => match child.try_wait() {
                Ok(Some(status)) => {
                    *phase = ChildPhase::Exited(exit_status_wire(status));
                    self.changed.notify_all();
                    Err(libc::EBADF)
                }
                Ok(None) => child.kill().map_err(error_code),
                Err(error) => Err(error_code(error)),
            },
        }
    }
}

static NEXT_CHILD_ID: AtomicUsize = AtomicUsize::new(1);
static CHILDREN: LazyLock<Mutex<HashMap<usize, Arc<ChildEntry>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

fn lock_children() -> MutexGuard<'static, HashMap<usize, Arc<ChildEntry>>> {
    CHILDREN
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn register_child(child: Child) -> usize {
    let entry = Arc::new(ChildEntry::new(child));
    let mut children = lock_children();
    loop {
        let id = NEXT_CHILD_ID.fetch_add(1, Ordering::Relaxed);
        if id != 0 && !children.contains_key(&id) {
            children.insert(id, Arc::clone(&entry));
            return id;
        }
    }
}

fn child_entry(handle: usize) -> Result<Arc<ChildEntry>, i32> {
    if handle == 0 {
        return Err(libc::EBADF);
    }
    lock_children().get(&handle).cloned().ok_or(libc::EBADF)
}

struct ReaperQueue {
    entries: Mutex<VecDeque<Arc<ChildEntry>>>,
    available: Condvar,
}

static REAPER_QUEUE: LazyLock<ReaperQueue> = LazyLock::new(|| ReaperQueue {
    entries: Mutex::new(VecDeque::new()),
    available: Condvar::new(),
});
static REAPER_STARTED: OnceLock<Result<(), i32>> = OnceLock::new();

fn reaper_loop() {
    loop {
        let entry = {
            let mut entries = REAPER_QUEUE
                .entries
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner());
            while entries.is_empty() {
                entries = REAPER_QUEUE
                    .available
                    .wait(entries)
                    .unwrap_or_else(|poisoned| poisoned.into_inner());
            }
            entries.pop_front()
        };
        if let Some(entry) = entry {
            let _ = entry.wait();
        }
    }
}

fn ensure_reaper() -> Result<(), i32> {
    *REAPER_STARTED.get_or_init(|| {
        std::thread::Builder::new()
            .name("taro-process-reaper".to_owned())
            .spawn(reaper_loop)
            .map(|_| ())
            .map_err(error_code)
    })
}

fn enqueue_for_reaping(entry: Arc<ChildEntry>) {
    if ensure_reaper().is_err() {
        // Native thread exhaustion is exceptional. Waiting on the cleanup
        // worker is slower, but it is the only correctness-preserving fallback:
        // dropping std::process::Child alone would leave a zombie on Unix.
        let _ = entry.wait();
        return;
    }

    let mut entries = REAPER_QUEUE
        .entries
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    entries.push_back(entry);
    REAPER_QUEUE.available.notify_one();
}

fn write_status(
    status: ExitStatusWire,
    code_out: *mut i32,
    signal_out: *mut i32,
) -> Result<(), i32> {
    if code_out.is_null() || signal_out.is_null() {
        return Err(libc::EINVAL);
    }
    unsafe {
        code_out.write(status.code);
        signal_out.write(status.signal);
    }
    Ok(())
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_command_spawn(
    handle: usize,
    child_out: *mut usize,
    stdin_fd_out: *mut i32,
    stdout_fd_out: *mut i32,
    stderr_fd_out: *mut i32,
) -> i32 {
    if child_out.is_null()
        || stdin_fd_out.is_null()
        || stdout_fd_out.is_null()
        || stderr_fd_out.is_null()
    {
        return libc::EINVAL;
    }
    unsafe {
        child_out.write(0);
        stdin_fd_out.write(-1);
        stdout_fd_out.write(-1);
        stderr_fd_out.write(-1);
    }

    let config = match command_config(handle) {
        Ok(config) => config,
        Err(code) => return code,
    };
    let mut command = config.make_command(false);
    let mut child = match spawn_locked(&mut command) {
        Ok(child) => child,
        Err(error) => return error_code(error),
    };

    let stdin_fd = child.stdin.take().map(IntoRawFd::into_raw_fd);
    let stdout_fd = child.stdout.take().map(IntoRawFd::into_raw_fd);
    let stderr_fd = child.stderr.take().map(IntoRawFd::into_raw_fd);
    let child_handle = register_child(child);
    unsafe {
        child_out.write(child_handle);
        stdin_fd_out.write(stdin_fd.unwrap_or(-1));
        stdout_fd_out.write(stdout_fd.unwrap_or(-1));
        stderr_fd_out.write(stderr_fd.unwrap_or(-1));
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_command_status(
    handle: usize,
    code_out: *mut i32,
    signal_out: *mut i32,
) -> i32 {
    if code_out.is_null() || signal_out.is_null() {
        return libc::EINVAL;
    }
    let config = match command_config(handle) {
        Ok(config) => config,
        Err(code) => return code,
    };
    // status has nowhere to return pipes. Rejecting this configuration avoids
    // the classic deadlock where a child fills stdout while its parent waits.
    if config.stdio.stdin == STDIO_PIPED
        || config.stdio.stdout == STDIO_PIPED
        || config.stdio.stderr == STDIO_PIPED
    {
        return libc::EINVAL;
    }

    let mut command = config.make_command(false);
    let mut child = match spawn_locked(&mut command) {
        Ok(child) => child,
        Err(error) => return error_code(error),
    };
    match child.wait() {
        Ok(status) => match write_status(exit_status_wire(status), code_out, signal_out) {
            Ok(()) => 0,
            Err(code) => code,
        },
        Err(error) => error_code(error),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_child_pid(handle: usize, pid_out: *mut u32) -> i32 {
    if pid_out.is_null() {
        return libc::EINVAL;
    }
    let entry = match child_entry(handle) {
        Ok(entry) => entry,
        Err(code) => return code,
    };
    unsafe { pid_out.write(entry.pid) };
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_child_wait(
    handle: usize,
    code_out: *mut i32,
    signal_out: *mut i32,
) -> i32 {
    let entry = match child_entry(handle) {
        Ok(entry) => entry,
        Err(code) => return code,
    };
    match entry.wait() {
        Ok(status) => match write_status(status, code_out, signal_out) {
            Ok(()) => 0,
            Err(code) => code,
        },
        Err(code) => code,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_child_try_wait(
    handle: usize,
    ready_out: *mut bool,
    code_out: *mut i32,
    signal_out: *mut i32,
) -> i32 {
    if ready_out.is_null() || code_out.is_null() || signal_out.is_null() {
        return libc::EINVAL;
    }
    unsafe {
        ready_out.write(false);
        code_out.write(-1);
        signal_out.write(-1);
    }
    let entry = match child_entry(handle) {
        Ok(entry) => entry,
        Err(code) => return code,
    };
    match entry.try_wait() {
        Ok(Some(status)) => {
            if let Err(code) = write_status(status, code_out, signal_out) {
                return code;
            }
            unsafe { ready_out.write(true) };
            0
        }
        Ok(None) => 0,
        Err(code) => code,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_child_kill(handle: usize) -> i32 {
    let entry = match child_entry(handle) {
        Ok(entry) => entry,
        Err(code) => return code,
    };
    match entry.kill() {
        Ok(()) => 0,
        Err(code) => code,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_child_abandon(handle: usize) {
    if handle == 0 {
        return;
    }
    if let Some(entry) = lock_children().remove(&handle) {
        // Abandonment deliberately transfers only wait ownership. It does not
        // signal the process, so dropping a Child never changes program logic.
        enqueue_for_reaping(entry);
    }
}

struct CaptureBudget {
    limit: Option<usize>,
    used: AtomicUsize,
    pid: u32,
}

impl CaptureBudget {
    fn claim(&self, count: usize) -> bool {
        let Some(limit) = self.limit else {
            return true;
        };

        let mut current = self.used.load(Ordering::Relaxed);
        loop {
            let Some(next) = current.checked_add(count) else {
                return false;
            };
            if next > limit {
                return false;
            }
            match self.used.compare_exchange_weak(
                current,
                next,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(observed) => current = observed,
            }
        }
    }

    fn stop_child(&self) {
        // A capture failure cannot return while leaving a child blocked on the
        // pipe we stopped reading. SIGKILL is scoped to this explicit output
        // operation; ordinary Child abandonment follows the non-killing path.
        unsafe {
            libc::kill(self.pid as libc::pid_t, libc::SIGKILL);
        }
    }
}

enum CaptureFailure {
    Io(io::Error),
    LimitExceeded,
}

fn capture_stream<R: Read>(
    mut stream: R,
    budget: &CaptureBudget,
) -> Result<Vec<u8>, CaptureFailure> {
    let mut output = Vec::new();
    let mut chunk = [0_u8; 8192];
    loop {
        let count = match stream.read(&mut chunk) {
            Ok(0) => break,
            Ok(count) => count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => {
                budget.stop_child();
                return Err(CaptureFailure::Io(error));
            }
        };
        if !budget.claim(count) {
            budget.stop_child();
            return Err(CaptureFailure::LimitExceeded);
        }
        output.extend_from_slice(&chunk[..count]);
    }
    Ok(output)
}

struct ProcessOutputSnapshot {
    status: ExitStatusWire,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

#[derive(Debug)]
enum OutputFailure {
    Io(io::Error),
    LimitExceeded,
}

fn run_output(
    config: &CommandConfig,
    limit: Option<usize>,
) -> Result<ProcessOutputSnapshot, OutputFailure> {
    if config.stdio.stdin == STDIO_PIPED {
        // output cannot return a live stdin writer. Treating it as null would
        // silently change an explicit request and could hide protocol bugs.
        return Err(OutputFailure::Io(io::Error::from_raw_os_error(
            libc::EINVAL,
        )));
    }

    let mut command = config.make_command(true);
    let mut child = spawn_locked(&mut command).map_err(OutputFailure::Io)?;
    let pid = child.id();
    let Some(stdout) = child.stdout.take() else {
        // make_command(true) always requests pipes, but preserve lifecycle
        // correctness if a future platform adapter violates that invariant.
        let _ = child.kill();
        let _ = child.wait();
        return Err(OutputFailure::Io(io::Error::from_raw_os_error(libc::EIO)));
    };
    let Some(stderr) = child.stderr.take() else {
        let _ = child.kill();
        let _ = child.wait();
        return Err(OutputFailure::Io(io::Error::from_raw_os_error(libc::EIO)));
    };
    let budget = CaptureBudget {
        limit,
        used: AtomicUsize::new(0),
        pid,
    };

    let (stdout_result, stderr_result, wait_result) = std::thread::scope(|scope| {
        let stdout_reader = scope.spawn(|| capture_stream(stdout, &budget));
        let stderr_reader = scope.spawn(|| capture_stream(stderr, &budget));
        let wait_result = child.wait();
        (stdout_reader.join(), stderr_reader.join(), wait_result)
    });

    let stdout_result = stdout_result
        .map_err(|_| OutputFailure::Io(io::Error::other("stdout capture worker panicked")))?;
    let stderr_result = stderr_result
        .map_err(|_| OutputFailure::Io(io::Error::other("stderr capture worker panicked")))?;

    if matches!(stdout_result, Err(CaptureFailure::LimitExceeded))
        || matches!(stderr_result, Err(CaptureFailure::LimitExceeded))
    {
        return Err(OutputFailure::LimitExceeded);
    }
    let stdout = stdout_result.map_err(|failure| match failure {
        CaptureFailure::Io(error) => OutputFailure::Io(error),
        CaptureFailure::LimitExceeded => OutputFailure::LimitExceeded,
    })?;
    let stderr = stderr_result.map_err(|failure| match failure {
        CaptureFailure::Io(error) => OutputFailure::Io(error),
        CaptureFailure::LimitExceeded => OutputFailure::LimitExceeded,
    })?;
    let status = wait_result
        .map(exit_status_wire)
        .map_err(OutputFailure::Io)?;
    Ok(ProcessOutputSnapshot {
        status,
        stdout,
        stderr,
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_command_output(
    handle: usize,
    limited: bool,
    limit: usize,
    error_out: *mut i32,
    limit_exceeded_out: *mut bool,
) -> usize {
    if error_out.is_null() || limit_exceeded_out.is_null() {
        return 0;
    }
    unsafe {
        error_out.write(0);
        limit_exceeded_out.write(false);
    }
    let config = match command_config(handle) {
        Ok(config) => config,
        Err(code) => {
            unsafe { error_out.write(code) };
            return 0;
        }
    };

    match run_output(config, limited.then_some(limit)) {
        Ok(output) => Box::into_raw(Box::new(output)) as usize,
        Err(OutputFailure::Io(error)) => {
            unsafe { error_out.write(error_code(error)) };
            0
        }
        Err(OutputFailure::LimitExceeded) => {
            unsafe { limit_exceeded_out.write(true) };
            0
        }
    }
}

fn output_snapshot(handle: usize) -> Result<&'static ProcessOutputSnapshot, i32> {
    if handle == 0 {
        return Err(libc::EBADF);
    }
    Ok(unsafe { &*(handle as *const ProcessOutputSnapshot) })
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_output_status(
    handle: usize,
    code_out: *mut i32,
    signal_out: *mut i32,
) -> i32 {
    let output = match output_snapshot(handle) {
        Ok(output) => output,
        Err(code) => return code,
    };
    match write_status(output.status, code_out, signal_out) {
        Ok(()) => 0,
        Err(code) => code,
    }
}

fn write_output_bytes(bytes: &[u8], data_out: *mut *const u8, len_out: *mut usize) -> i32 {
    if data_out.is_null() || len_out.is_null() {
        return libc::EINVAL;
    }
    unsafe {
        data_out.write(bytes.as_ptr());
        len_out.write(bytes.len());
    }
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_output_stdout(
    handle: usize,
    data_out: *mut *const u8,
    len_out: *mut usize,
) -> i32 {
    let output = match output_snapshot(handle) {
        Ok(output) => output,
        Err(code) => return code,
    };
    write_output_bytes(&output.stdout, data_out, len_out)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_output_stderr(
    handle: usize,
    data_out: *mut *const u8,
    len_out: *mut usize,
) -> i32 {
    let output = match output_snapshot(handle) {
        Ok(output) => output,
        Err(code) => return code,
    };
    write_output_bytes(&output.stderr, data_out, len_out)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__process_output_close(handle: usize) {
    if handle != 0 {
        unsafe { drop(Box::from_raw(handle as *mut ProcessOutputSnapshot)) };
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ptr;
    use std::time::{Duration, Instant};

    fn config(program: &str, arguments: &[&str]) -> CommandConfig {
        CommandConfig {
            program: OsString::from(program),
            arguments: arguments.iter().map(OsString::from).collect(),
            environment: Vec::new(),
            current_dir: None,
            stdio: StdioConfig {
                stdin: STDIO_NULL,
                stdout: STDIO_NULL,
                stderr: STDIO_NULL,
            },
        }
    }

    #[test]
    fn output_preserves_direct_arguments_and_both_streams() {
        let config = config(
            "/bin/sh",
            &[
                "-c",
                "printf '%s' \"$1\"; printf '%s' \"$2\" >&2",
                "taro-test",
                "$HOME; not shell syntax",
                "stderr-bytes",
            ],
        );
        let output = run_output(&config, None).expect("command output");
        assert_eq!(output.stdout, b"$HOME; not shell syntax");
        assert_eq!(output.stderr, b"stderr-bytes");
        assert_eq!(output.status.code, 0);
    }

    #[test]
    fn child_wait_and_try_wait_cache_one_status() {
        let mut command = Command::new("/bin/sh");
        command.args(["-c", "exit 7"]);
        command
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let handle = register_child(command.spawn().expect("spawn child"));
        let entry = child_entry(handle).expect("registered child");
        let first = entry.wait().expect("first wait");
        let second = entry.wait().expect("cached wait");
        let observed = entry.try_wait().expect("cached try wait");
        assert_eq!(first.code, 7);
        assert_eq!(first, second);
        assert_eq!(observed, Some(first));
        __rt__process_child_abandon(handle);
    }

    #[test]
    fn kill_can_race_wait_without_a_pid_reuse_window() {
        let mut command = Command::new("/bin/sleep");
        command.arg("5");
        command
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let entry = Arc::new(ChildEntry::new(command.spawn().expect("spawn child")));
        let waiter = Arc::clone(&entry);
        let wait_thread = std::thread::spawn(move || waiter.wait());

        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            if matches!(*entry.lock_phase(), ChildPhase::Waiting) {
                break;
            }
            assert!(Instant::now() < deadline, "wait did not enter Waiting");
            std::thread::yield_now();
        }

        entry.kill().expect("kill child while wait owns handle");
        let status = wait_thread
            .join()
            .expect("wait thread")
            .expect("wait status");
        assert_eq!(status.signal, libc::SIGKILL);
        assert_eq!(entry.try_wait().expect("cached try wait"), Some(status));
    }

    #[test]
    fn bounded_output_kills_and_reaps_a_producer() {
        let config = config("/bin/sh", &["-c", "while :; do printf 0123456789; done"]);
        let started = Instant::now();
        assert!(matches!(
            run_output(&config, Some(1024)),
            Err(OutputFailure::LimitExceeded)
        ));
        assert!(started.elapsed() < Duration::from_secs(5));
    }

    #[test]
    fn abandoned_children_are_reaped_without_being_killed() {
        let mut command = Command::new("/bin/sh");
        command.args(["-c", "sleep 0.05; exit 23"]);
        command
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        let handle = register_child(command.spawn().expect("spawn child"));
        let entry = child_entry(handle).expect("registered child");
        __rt__process_child_abandon(handle);
        assert!(!lock_children().contains_key(&handle));

        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            if let Some(status) = entry.try_wait().expect("observe reaper") {
                assert_eq!(status.code, 23, "abandonment must not kill the child");
                break;
            }
            assert!(Instant::now() < deadline, "reaper did not collect child");
            std::thread::sleep(Duration::from_millis(5));
        }
    }

    #[test]
    fn command_inputs_reject_nul_and_invalid_environment_names() {
        let invalid = RtString {
            ptr: b"bad\0value".as_ptr(),
            len: b"bad\0value".len(),
        };
        assert_eq!(input_os_string(invalid), Err(libc::EINVAL));

        let empty = RtString {
            ptr: ptr::null(),
            len: 0,
        };
        assert_eq!(input_env_name(empty), Err(libc::EINVAL));
        let equals = RtString {
            ptr: b"BAD=NAME".as_ptr(),
            len: b"BAD=NAME".len(),
        };
        assert_eq!(input_env_name(equals), Err(libc::EINVAL));
    }
}
