//! Stack exhaustion reporting.
//!
//! A thread that runs out of stack writes into the guard region the kernel keeps
//! below it, which raises `SIGSEGV` (`SIGBUS` on some platforms). With no handler
//! installed the default action kills the process outright: no message, no exit
//! status beyond the signal number. Unbounded recursion — the overwhelmingly
//! common cause — is then indistinguishable from memory corruption.
//!
//! Rust's standard library installs exactly this handler from `std::rt::init`,
//! but a Taro binary's `main` is emitted by codegen and calls `taro_start`
//! directly, so `lang_start` never runs and none of that setup happens. This
//! module does it explicitly.
//!
//! The handler cannot unwind: turning the fault into a Taro panic would need
//! stack to run on, which is precisely what has run out. It reports and exits,
//! matching the panic path's exit code so callers see a consistent failure.
//!
//! Everything the handler touches must be async-signal-safe. It reads a cached
//! stack bound out of thread-local storage and calls `write` and `_exit`; it does
//! not allocate, take locks, or format.

#[cfg(unix)]
use core::cell::Cell;

// Lowest address the running thread's stack may reach.
//
// Cached when the guard is installed, because the calls that report it are not
// safe to make from a signal handler. Zero means "not recorded", which makes the
// handler decline rather than guess. The `const` initialiser matters: it makes
// each access a plain thread-local read, with no lazy setup to run at a point
// where running anything is unsafe.
#[cfg(unix)]
thread_local! {
    static STACK_LOW: Cell<usize> = const { Cell::new(0) };
}

/// Size of the alternate stack the handler runs on.
///
/// It has to be a separate region: the thread's own stack is exhausted, so the
/// handler could not push a frame onto it.
#[cfg(unix)]
const SIGNAL_STACK_SIZE: usize = 64 * 1024;

/// How far below the stack a fault may land and still be treated as overflow.
///
/// A frame larger than a single guard page can step past the guard before
/// touching anything, so the window is wider than one page. It stays well short
/// of the whole guard region, which on macOS spans megabytes and would swallow
/// genuinely wild pointers.
#[cfg(unix)]
const OVERFLOW_WINDOW: usize = 1024 * 1024;

#[cfg(unix)]
const PANIC_EXIT_CODE: i32 = 101;

#[cfg(unix)]
static MESSAGE: &[u8] =
    b"panic: stack overflow\n  a thread exhausted its stack, which usually means unbounded recursion\n";

/// Installs the process-wide handler and guards the calling thread.
///
/// Called once from the entry shim, before any user code runs.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__install_stack_guard() {
    #[cfg(unix)]
    unsafe {
        install_signal_handlers();
        install_thread_guard();
    }
}

/// Guards the calling thread, assuming the handler is already installed.
///
/// The `sigaction` is process-wide but the alternate stack is per-thread, so
/// every thread that runs Taro code needs this.
#[cfg(unix)]
pub(crate) fn guard_current_thread() {
    unsafe { install_thread_guard() };
}

#[cfg(not(unix))]
pub(crate) fn guard_current_thread() {}

#[cfg(unix)]
unsafe fn install_signal_handlers() {
    use std::sync::Once;

    static INSTALLED: Once = Once::new();

    INSTALLED.call_once(|| unsafe {
        let mut action: libc::sigaction = core::mem::zeroed();
        action.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;
        action.sa_sigaction = handler as *const () as usize;
        libc::sigemptyset(&mut action.sa_mask);

        // `SIGBUS` matters on macOS, where an unmapped-page write can surface as
        // a bus error rather than a segmentation fault.
        libc::sigaction(libc::SIGSEGV, &action, core::ptr::null_mut());
        libc::sigaction(libc::SIGBUS, &action, core::ptr::null_mut());
    });
}

#[cfg(unix)]
unsafe fn install_thread_guard() {
    unsafe {
        // An already-installed alternate stack means this thread is guarded.
        let mut current: libc::stack_t = core::mem::zeroed();
        if libc::sigaltstack(core::ptr::null(), &mut current) == 0
            && !current.ss_sp.is_null()
            && current.ss_flags & libc::SS_DISABLE == 0
        {
            record_stack_bounds();
            return;
        }

        let size = SIGNAL_STACK_SIZE.max(libc::SIGSTKSZ);
        let memory = libc::mmap(
            core::ptr::null_mut(),
            size,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANON,
            -1,
            0,
        );
        if memory == libc::MAP_FAILED {
            return;
        }

        let stack = libc::stack_t {
            ss_sp: memory,
            ss_flags: 0,
            ss_size: size,
        };
        if libc::sigaltstack(&stack, core::ptr::null_mut()) != 0 {
            libc::munmap(memory, size);
            return;
        }

        // Deliberately never unmapped after installation: the stack has to stay
        // valid for as long as the thread can fault, including thread teardown.
        record_stack_bounds();
    }
}

/// Records where the calling thread's stack ends, for the handler to compare
/// against.
#[cfg(unix)]
unsafe fn record_stack_bounds() {
    let low = unsafe { current_stack_low() };
    if low != 0 {
        let _ = STACK_LOW.try_with(|cell| cell.set(low));
    }
}

#[cfg(all(unix, target_os = "macos"))]
unsafe fn current_stack_low() -> usize {
    unsafe {
        let this = libc::pthread_self();
        // `pthread_get_stackaddr_np` reports the high end of the stack.
        let top = libc::pthread_get_stackaddr_np(this) as usize;
        let size = libc::pthread_get_stacksize_np(this);
        top.saturating_sub(size)
    }
}

#[cfg(all(unix, not(target_os = "macos")))]
unsafe fn current_stack_low() -> usize {
    unsafe {
        let mut attr: libc::pthread_attr_t = core::mem::zeroed();
        if libc::pthread_getattr_np(libc::pthread_self(), &mut attr) != 0 {
            return 0;
        }
        let mut base: *mut libc::c_void = core::ptr::null_mut();
        let mut size: libc::size_t = 0;
        let ok = libc::pthread_attr_getstack(&attr, &mut base, &mut size) == 0;
        libc::pthread_attr_destroy(&mut attr);
        if ok { base as usize } else { 0 }
    }
}

/// Reports and exits when the fault looks like stack exhaustion, and restores
/// the default action otherwise so a real memory error still crashes normally.
#[cfg(unix)]
extern "C" fn handler(
    signal: libc::c_int,
    info: *mut libc::siginfo_t,
    _context: *mut libc::c_void,
) {
    let fault = if info.is_null() {
        0
    } else {
        unsafe { (*info).si_addr() as usize }
    };

    if is_stack_overflow(fault) {
        unsafe {
            let _ = libc::write(
                libc::STDERR_FILENO,
                MESSAGE.as_ptr() as *const libc::c_void,
                MESSAGE.len(),
            );
            // `_exit` rather than `exit`: at-exit handlers would run user code on
            // a stack that has nothing left.
            libc::_exit(PANIC_EXIT_CODE);
        }
    }

    // Not ours. Put the default action back and return, so the same access
    // faults again and produces the crash it would have without this handler.
    unsafe {
        let mut action: libc::sigaction = core::mem::zeroed();
        action.sa_sigaction = libc::SIG_DFL;
        libc::sigemptyset(&mut action.sa_mask);
        libc::sigaction(signal, &action, core::ptr::null_mut());
    }
}

#[cfg(unix)]
fn is_stack_overflow(fault: usize) -> bool {
    let Ok(low) = STACK_LOW.try_with(|cell| cell.get()) else {
        return false;
    };
    if low == 0 || fault == 0 {
        return false;
    }
    // Below the stack, but close enough to be the guard rather than a stray
    // pointer into unrelated address space.
    fault < low && low - fault <= OVERFLOW_WINDOW
}
