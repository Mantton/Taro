use crate::executor::{TaskIdentity, TaskWake};
use std::time::Duration as StdDuration;

type TaskToken = TaskIdentity;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Interest {
    Read,
    Write,
}

#[cfg(unix)]
mod imp {
    use super::{Interest, StdDuration, TaskToken, TaskWake};
    use crate::hot_mutex::HotMutex;
    use libc::{self, c_int};
    use rustc_hash::{FxHashMap, FxHashSet};
    use std::os::fd::RawFd;
    #[cfg(target_os = "macos")]
    use std::ptr;

    static REACTOR: HotMutex<Option<Reactor>> = HotMutex::new(None);

    struct SourceEntry {
        fd: RawFd,
        read_waiters: Vec<TaskToken>,
        write_waiters: Vec<TaskToken>,
        #[cfg(target_os = "linux")]
        registered: bool,
    }

    /// A task that has waited on I/O. Finishing it visits just its own sources,
    /// however many connections the process has open.
    struct WaitingTask {
        wake: TaskWake,
        sources: FxHashSet<usize>,
        // Size at which to drop sources closed since: a long-lived task would
        // otherwise remember every short-lived socket it ever waited on.
        prune_at: usize,
    }
    const MIN_WAITING_TASK_PRUNE: usize = 16;

    struct Reactor {
        poll_fd: RawFd,
        #[cfg(target_os = "linux")]
        control_fd: RawFd,
        #[cfg(target_os = "macos")]
        control_read_fd: RawFd,
        #[cfg(target_os = "macos")]
        control_write_fd: RawFd,
        sources: FxHashMap<usize, SourceEntry>,
        // External close may run from another (even expired) native session.
        wake_targets: FxHashMap<TaskToken, WaitingTask>,
    }

    impl Reactor {
        fn new() -> Result<Self, i32> {
            #[cfg(target_os = "linux")]
            let poll_fd = unsafe { libc::epoll_create1(libc::EPOLL_CLOEXEC) };
            #[cfg(target_os = "macos")]
            let poll_fd = unsafe { libc::kqueue() };

            if poll_fd < 0 {
                return Err(last_errno());
            }

            #[cfg(target_os = "linux")]
            let control_fd = unsafe { libc::eventfd(0, libc::EFD_CLOEXEC | libc::EFD_NONBLOCK) };
            #[cfg(target_os = "linux")]
            if control_fd < 0 {
                let err = last_errno();
                let _ = unsafe { libc::close(poll_fd) };
                return Err(err);
            }

            #[cfg(target_os = "macos")]
            let (control_read_fd, control_write_fd) = {
                let mut fds = [0; 2];
                if cloexec_pipe(&mut fds) < 0 {
                    let err = last_errno();
                    let _ = unsafe { libc::close(poll_fd) };
                    return Err(err);
                }
                if let Err(err) = set_nonblocking(fds[0]).and_then(|_| set_nonblocking(fds[1])) {
                    let _ = unsafe { libc::close(fds[0]) };
                    let _ = unsafe { libc::close(fds[1]) };
                    let _ = unsafe { libc::close(poll_fd) };
                    return Err(err);
                }
                (fds[0], fds[1])
            };

            let mut reactor = Self {
                poll_fd,
                #[cfg(target_os = "linux")]
                control_fd,
                #[cfg(target_os = "macos")]
                control_read_fd,
                #[cfg(target_os = "macos")]
                control_write_fd,
                sources: FxHashMap::default(),
                wake_targets: FxHashMap::default(),
            };
            reactor.register_control_source()?;
            Ok(reactor)
        }

        #[cfg(target_os = "linux")]
        fn register_control_source(&mut self) -> Result<(), i32> {
            let mut event = libc::epoll_event {
                events: libc::EPOLLIN as u32,
                u64: 0,
            };
            if unsafe {
                libc::epoll_ctl(
                    self.poll_fd,
                    libc::EPOLL_CTL_ADD,
                    self.control_fd,
                    &mut event,
                )
            } < 0
            {
                return Err(last_errno());
            }
            Ok(())
        }

        #[cfg(target_os = "macos")]
        fn register_control_source(&mut self) -> Result<(), i32> {
            self.change_kqueue(self.control_read_fd, libc::EVFILT_READ, libc::EV_ADD | libc::EV_ENABLE, 0)
        }

        #[cfg(target_os = "linux")]
        fn notify(&self) {
            let value: u64 = 1;
            let bytes = value.to_ne_bytes();
            let mut offset = 0;
            while offset < bytes.len() {
                let result = unsafe {
                    libc::write(
                        self.control_fd,
                        bytes[offset..].as_ptr().cast(),
                        bytes.len() - offset,
                    )
                };
                if result > 0 {
                    offset += result as usize;
                    continue;
                }

                let err = last_errno();
                if err == libc::EINTR {
                    continue;
                }
                if err == libc::EAGAIN {
                    break;
                }
                break;
            }
        }

        #[cfg(target_os = "macos")]
        fn notify(&self) {
            let byte = [1u8];
            loop {
                let result =
                    unsafe { libc::write(self.control_write_fd, byte.as_ptr().cast(), byte.len()) };
                if result >= 0 {
                    break;
                }

                let err = last_errno();
                if err == libc::EINTR {
                    continue;
                }
                if err == libc::EAGAIN {
                    break;
                }
                break;
            }
        }

        #[cfg(target_os = "linux")]
        fn drain_control(&self) {
            let mut value = 0u64;
            // eventfd read atomically clears the entire counter in a single
            // 8-byte read. One successful read is all we need; looping would
            // spin until EAGAIN.
            loop {
                let result = unsafe {
                    libc::read(
                        self.control_fd,
                        (&mut value as *mut u64).cast(),
                        std::mem::size_of::<u64>(),
                    )
                };
                if result > 0 {
                    break; // counter cleared; done
                }

                if result == 0 {
                    break; // shouldn't happen for eventfd, but be safe
                }

                let err = last_errno();
                if err == libc::EINTR {
                    continue;
                }
                // EAGAIN or any other error: nothing left to read
                break;
            }
        }

        #[cfg(target_os = "macos")]
        fn drain_control(&self) {
            // Drain all bytes currently in the pipe so it resets to non-ready.
            let mut buf = [0u8; 64];
            loop {
                let result =
                    unsafe { libc::read(self.control_read_fd, buf.as_mut_ptr().cast(), buf.len()) };
                if result > 0 {
                    // Read some bytes; keep draining in case more are buffered.
                    continue;
                }

                if result == 0 {
                    // EOF — pipe write end was closed; stop.
                    break;
                }

                let err = last_errno();
                if err == libc::EINTR {
                    continue;
                }
                // EAGAIN: pipe is empty; done.
                break;
            }
        }

        // The source id is the descriptor's lease id, so every operation
        // reaches the descriptor through a lease and close defers until the
        // last in-flight operation has released it.
        fn register_source(&mut self, fd: RawFd) -> usize {
            let source_id = crate::fd_lease::open(fd) as usize;
            self.sources.insert(
                source_id,
                SourceEntry {
                    fd,
                    read_waiters: Vec::new(),
                    write_waiters: Vec::new(),
                    #[cfg(target_os = "linux")]
                    registered: false,
                },
            );
            source_id
        }

        fn register_wait(
            &mut self,
            source_id: usize,
            target: TaskWake,
            interest: Interest,
        ) -> Result<(), i32> {
            let task_token = target.identity();
            let Some(source) = self.sources.get_mut(&source_id) else {
                return Err(libc::EBADF);
            };

            let waiters = match interest {
                Interest::Read => &mut source.read_waiters,
                Interest::Write => &mut source.write_waiters,
            };

            if !waiters.contains(&task_token) {
                waiters.push(task_token);
            }
            debug_assert!(
                waiters
                    .iter()
                    .filter(|waiter| **waiter == task_token)
                    .count()
                    == 1,
                "async io waiter registered more than once for one interest"
            );

            // A failure to arm below leaves the waiter listed, so the task must
            // already know this source to remove it again when it finishes.
            let task = self
                .wake_targets
                .entry(task_token)
                .or_insert_with(|| WaitingTask {
                    wake: target,
                    sources: FxHashSet::default(),
                    prune_at: MIN_WAITING_TASK_PRUNE,
                });
            task.sources.insert(source_id);
            if task.sources.len() >= task.prune_at {
                let open = &self.sources;
                task.sources.retain(|source| open.contains_key(source));
                task.prune_at = (task.sources.len() * 2).max(MIN_WAITING_TASK_PRUNE);
            }

            // The source is armed only after the waiter is visible, so readiness
            // that arrives immediately after arming has a task token to wake.
            self.arm_wait(source_id, interest)
        }

        fn cancel_task(&mut self, task_token: TaskToken) {
            let Some(task) = self.wake_targets.remove(&task_token) else {
                return;
            };
            // Cancellation/finalization must remove the task from every source.
            // Any remaining waiters are rearmed on Linux so one-shot readiness
            // is not lost for other tasks.
            for source_id in task.sources {
                let Some(source) = self.sources.get_mut(&source_id) else {
                    continue;
                };
                let before = source.read_waiters.len() + source.write_waiters.len();
                source.read_waiters.retain(|waiter| *waiter != task_token);
                source.write_waiters.retain(|waiter| *waiter != task_token);
                let remaining = source.read_waiters.len() + source.write_waiters.len();

                #[cfg(target_os = "linux")]
                if remaining != before && remaining != 0 {
                    let _ = self.rearm_linux_source(source_id);
                }
                #[cfg(not(target_os = "linux"))]
                let _ = (before, remaining);
            }
        }

        fn wake_target(&self, task_token: &TaskToken) -> Option<TaskWake> {
            self.wake_targets
                .get(task_token)
                .map(|task| task.wake.clone())
        }

        fn close_source(&mut self, source_id: usize) -> (c_int, Vec<TaskToken>) {
            let Some(source) = self.sources.remove(&source_id) else {
                return (0, Vec::new());
            };

            let mut wake = Vec::new();
            extend_unique(&mut wake, &source.read_waiters);
            extend_unique(&mut wake, &source.write_waiters);
            debug_assert_unique_tasks(&wake);
            (crate::fd_lease::close(source_id as u64), wake)
        }

        #[cfg(target_os = "linux")]
        fn process_epoll_events(&mut self, events: &[libc::epoll_event]) -> Vec<TaskToken> {
            let mut wake = Vec::new();
            let mut rearm = Vec::new();
            for event in events {
                let source_id = event.u64 as usize;
                if source_id == 0 {
                    self.drain_control();
                    continue;
                }
                let mut needs_rearm = false;

                if let Some(source) = self.sources.get_mut(&source_id) {
                    let flags = event.events as c_int;
                    let read_ready = (flags
                        & (libc::EPOLLIN | libc::EPOLLHUP | libc::EPOLLERR | libc::EPOLLRDHUP))
                        != 0;
                    let write_ready =
                        (flags & (libc::EPOLLOUT | libc::EPOLLHUP | libc::EPOLLERR)) != 0;

                    if read_ready {
                        drain_unique(&mut wake, &mut source.read_waiters);
                    }
                    if write_ready {
                        drain_unique(&mut wake, &mut source.write_waiters);
                    }

                    needs_rearm =
                        !source.read_waiters.is_empty() || !source.write_waiters.is_empty();
                }

                if needs_rearm {
                    rearm.push(source_id);
                }
            }

            for source_id in rearm {
                if let Err(err) = self.rearm_linux_source(source_id) {
                    panic!("async io re-arm failed with errno {err}");
                }
            }

            debug_assert_unique_tasks(&wake);
            wake
        }

        #[cfg(target_os = "macos")]
        fn process_kqueue_events(&mut self, events: &[libc::kevent64_s]) -> Vec<TaskToken> {
            let mut wake = Vec::new();
            for event in events {
                let source_id = event.udata as usize;
                if source_id == 0 {
                    self.drain_control();
                    continue;
                }
                let Some(source) = self.sources.get_mut(&source_id) else {
                    continue;
                };

                match event.filter {
                    libc::EVFILT_READ => {
                        drain_unique(&mut wake, &mut source.read_waiters);
                    }
                    libc::EVFILT_WRITE => {
                        drain_unique(&mut wake, &mut source.write_waiters);
                    }
                    _ => {}
                }
            }

            debug_assert_unique_tasks(&wake);
            wake
        }

        #[cfg(target_os = "linux")]
        fn rearm_linux_source(&mut self, source_id: usize) -> Result<(), i32> {
            let Some(source) = self.sources.get_mut(&source_id) else {
                return Err(libc::EBADF);
            };

            let mut mask: u32 = 0;
            if !source.read_waiters.is_empty() {
                mask |= (libc::EPOLLIN | libc::EPOLLHUP | libc::EPOLLERR | libc::EPOLLRDHUP) as u32;
            }
            if !source.write_waiters.is_empty() {
                mask |= (libc::EPOLLOUT | libc::EPOLLHUP | libc::EPOLLERR) as u32;
            }

            if mask == 0 {
                return Ok(());
            }

            let mut event = libc::epoll_event {
                events: mask | (libc::EPOLLONESHOT as u32),
                u64: source_id as u64,
            };
            let op = if source.registered {
                libc::EPOLL_CTL_MOD
            } else {
                libc::EPOLL_CTL_ADD
            };

            if unsafe { libc::epoll_ctl(self.poll_fd, op, source.fd, &mut event) } < 0 {
                return Err(last_errno());
            }

            source.registered = true;
            Ok(())
        }

        #[cfg(target_os = "macos")]
        fn arm_wait(&mut self, source_id: usize, interest: Interest) -> Result<(), i32> {
            let Some(source) = self.sources.get(&source_id) else {
                return Err(libc::EBADF);
            };

            let filter = match interest {
                Interest::Read => libc::EVFILT_READ,
                Interest::Write => libc::EVFILT_WRITE,
            };
            self.change_kqueue(
                source.fd,
                filter,
                libc::EV_ADD | libc::EV_ENABLE | libc::EV_ONESHOT,
                source_id as u64,
            )
        }

        #[cfg(target_os = "macos")]
        fn change_kqueue(&self, fd: RawFd, filter: i16, flags: u16, udata: u64) -> Result<(), i32> {
            let change = libc::kevent64_s {
                ident: fd as u64,
                filter,
                flags,
                fflags: 0,
                data: 0,
                udata,
                ext: [0; 2],
            };
            if unsafe {
                libc::kevent64(
                    self.poll_fd,
                    &change,
                    1,
                    ptr::null_mut(),
                    0,
                    libc::KEVENT_FLAG_IMMEDIATE,
                    ptr::null(),
                )
            } < 0
            {
                return Err(last_errno());
            }
            Ok(())
        }

        #[cfg(target_os = "linux")]
        fn arm_wait(&mut self, source_id: usize, _interest: Interest) -> Result<(), i32> {
            self.rearm_linux_source(source_id)
        }

        // wait methods replaced by process_*_events
    }

    impl Drop for Reactor {
        fn drop(&mut self) {
            let _ = unsafe { libc::close(self.poll_fd) };
            #[cfg(target_os = "linux")]
            let _ = unsafe { libc::close(self.control_fd) };
            #[cfg(target_os = "macos")]
            {
                let _ = unsafe { libc::close(self.control_read_fd) };
                let _ = unsafe { libc::close(self.control_write_fd) };
            }
        }
    }

    #[cfg(target_os = "linux")]
    fn epoll_timeout_ms(timeout: Option<StdDuration>) -> c_int {
        match timeout {
            None => -1,
            Some(duration) => {
                let mut millis = duration.as_millis();
                if millis == 0 && !duration.is_zero() {
                    millis = 1;
                }
                millis.min(c_int::MAX as u128) as c_int
            }
        }
    }

    /// A pipe whose ends close on exec, so spawned children never inherit
    /// them. Returns 0, or -1 with errno set.
    pub(crate) fn cloexec_pipe(fds: &mut [c_int; 2]) -> c_int {
        #[cfg(target_os = "linux")]
        {
            unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) }
        }
        #[cfg(target_os = "macos")]
        {
            // macOS has no pipe2. Every Taro spawn holds this lock, so none
            // can fork between creating the pipe and marking it.
            let _guard = crate::env::lock_process_state();
            if unsafe { libc::pipe(fds.as_mut_ptr()) } != 0 {
                return -1;
            }
            for fd in *fds {
                if unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } != 0 {
                    let err = std::io::Error::last_os_error();
                    unsafe {
                        libc::close(fds[0]);
                        libc::close(fds[1]);
                    }
                    *fds = [-1, -1];
                    let code = err.raw_os_error().unwrap_or(libc::EINVAL);
                    unsafe { *libc::__error() = code };
                    return -1;
                }
            }
            0
        }
    }

    fn set_nonblocking(fd: RawFd) -> Result<(), i32> {
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
        if flags < 0 {
            return Err(last_errno());
        }

        if unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
            return Err(last_errno());
        }

        Ok(())
    }

    fn push_unique(waiters: &mut Vec<TaskToken>, task_token: TaskToken) {
        if !waiters.contains(&task_token) {
            waiters.push(task_token);
        }
    }

    fn extend_unique(dst: &mut Vec<TaskToken>, src: &[TaskToken]) {
        for &task_token in src {
            push_unique(dst, task_token);
        }
    }

    fn drain_unique(dst: &mut Vec<TaskToken>, src: &mut Vec<TaskToken>) {
        for task_token in src.drain(..) {
            push_unique(dst, task_token);
        }
    }

    fn debug_assert_unique_tasks(_tasks: &[TaskToken]) {
        #[cfg(debug_assertions)]
        for (index, task) in _tasks.iter().enumerate() {
            debug_assert!(
                !_tasks[index + 1..].contains(task),
                "async io wake batch contains duplicate task token"
            );
        }
    }

    fn with_reactor_mut<R>(f: impl FnOnce(&mut Reactor) -> R) -> Option<R> {
        let mut guard = REACTOR.lock().unwrap();
        guard.as_mut().map(f)
    }

    fn ensure_reactor() -> Result<(), i32> {
        let mut guard = REACTOR.lock().unwrap();
        if guard.is_none() {
            *guard = Some(Reactor::new()?);
        }
        Ok(())
    }

    pub(crate) fn initialize() -> Result<(), i32> {
        ensure_reactor()
    }

    pub(crate) fn notify() {
        let guard = REACTOR.lock().unwrap();
        if let Some(reactor) = guard.as_ref() {
            reactor.notify();
        }
    }

    fn last_errno() -> i32 {
        std::io::Error::last_os_error()
            .raw_os_error()
            .unwrap_or(libc::EINVAL)
    }

    pub(crate) fn adopt_fd(fd: RawFd) -> usize {
        if fd < 0 {
            return 0;
        }

        if let Err(_err) = set_nonblocking(fd) {
            return 0;
        }

        // Taro's executable entry does not install Rust main's process-wide
        // SIGPIPE ignore handler. Suppress it per socket, leaving application
        // signal policy untouched. Non-socket descriptors are also adopted.
        #[cfg(target_os = "macos")]
        {
            let enabled: c_int = 1;
            let status = unsafe {
                libc::setsockopt(
                    fd,
                    libc::SOL_SOCKET,
                    libc::SO_NOSIGPIPE,
                    (&enabled as *const c_int).cast(),
                    std::mem::size_of_val(&enabled) as libc::socklen_t,
                )
            };
            if status < 0 {
                match last_errno() {
                    libc::ENOTSOCK => {}
                    // macOS refuses options on a socket its peer has already
                    // reset. That peer is gone, not the listener that accepted it.
                    libc::EINVAL => {
                        unsafe { *libc::__error() = libc::ECONNABORTED };
                        return 0;
                    }
                    _ => return 0,
                }
            }
        }
        if let Err(_err) = ensure_reactor() {
            return 0;
        }

        with_reactor_mut(|reactor| reactor.register_source(fd)).unwrap_or(0)
    }

    pub(crate) fn close_source(source_id: usize) -> (c_int, Vec<TaskWake>) {
        if source_id == 0 {
            return (0, Vec::new());
        }

        if let Some(result) = with_reactor_mut(|reactor| {
            let (status, tokens) = reactor.close_source(source_id);
            let wake = tokens
                .iter()
                .filter_map(|token| reactor.wake_target(token))
                .collect();
            (status, wake)
        }) {
            result
        } else {
            (0, Vec::new())
        }
    }

    pub(crate) fn dup_fd(fd: RawFd) -> c_int {
        loop {
            let result = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 0) };
            if result >= 0 {
                return result;
            }

            let err = last_errno();
            if err != libc::EINTR {
                return -1;
            }
        }
    }

    pub(crate) fn create_pipe(read_fd_out: *mut c_int, write_fd_out: *mut c_int) -> c_int {
        let mut fds = [0 as c_int; 2];
        loop {
            let result = cloexec_pipe(&mut fds);
            if result == 0 {
                unsafe {
                    if !read_fd_out.is_null() {
                        read_fd_out.write(fds[0]);
                    }
                    if !write_fd_out.is_null() {
                        write_fd_out.write(fds[1]);
                    }
                }
                return 0;
            }

            let err = last_errno();
            if err != libc::EINTR {
                return -1;
            }
        }
    }

    pub(crate) fn read_source(source_id: usize, buf: *mut u8, len: usize) -> isize {
        let fd = match crate::fd_lease::acquire(source_id as u64) {
            Ok(value) => value,
            Err(err) => return -(err as isize),
        };

        let result = unsafe { libc::read(fd, buf.cast(), len) };
        let result = if result < 0 {
            -(last_errno() as isize)
        } else {
            result as isize
        };
        crate::fd_lease::release(source_id as u64);
        result
    }

    pub(crate) fn write_source(source_id: usize, buf: *const u8, len: usize) -> isize {
        let fd = match crate::fd_lease::acquire(source_id as u64) {
            Ok(value) => value,
            Err(err) => return -(err as isize),
        };

        #[cfg(target_os = "linux")]
        let result = {
            let sent = unsafe { libc::send(fd, buf.cast(), len, libc::MSG_NOSIGNAL) };
            if sent < 0 && last_errno() == libc::ENOTSOCK {
                unsafe { libc::write(fd, buf.cast(), len) }
            } else {
                sent
            }
        };
        #[cfg(not(target_os = "linux"))]
        let result = unsafe { libc::write(fd, buf.cast(), len) };
        let result = if result < 0 {
            -(last_errno() as isize)
        } else {
            result as isize
        };
        crate::fd_lease::release(source_id as u64);
        result
    }

    pub(crate) fn register_wait(
        source_id: usize,
        target: TaskWake,
        interest: Interest,
    ) -> Result<(), i32> {
        ensure_reactor()?;
        with_reactor_mut(|reactor| reactor.register_wait(source_id, target, interest))
            .expect("async io reactor missing after initialization")
    }

    pub(crate) fn wait(timeout: Option<StdDuration>) -> Vec<TaskWake> {
        let poll_fd = {
            let guard = REACTOR.lock().unwrap();
            guard.as_ref().map(|r| r.poll_fd)
        };
        let Some(poll_fd) = poll_fd else {
            return Vec::new();
        };

        #[cfg(target_os = "linux")]
        {
            let mut events: [libc::epoll_event; 64] = [libc::epoll_event { events: 0, u64: 0 }; 64];
            let timeout_ms = epoll_timeout_ms(timeout);
            let ready = unsafe {
                libc::epoll_wait(
                    poll_fd,
                    events.as_mut_ptr(),
                    events.len() as c_int,
                    timeout_ms,
                )
            };

            if ready < 0 {
                let err = last_errno();
                if err == libc::EINTR {
                    return Vec::new();
                }
                panic!("async io poll wait failed with errno {err}");
            }
            if ready == 0 {
                return Vec::new();
            }
            with_reactor_mut(|reactor| {
                let tokens = reactor.process_epoll_events(&events[..ready as usize]);
                tokens
                    .iter()
                    .filter_map(|token| reactor.wake_target(token))
                    .collect()
            })
            .unwrap_or_default()
        }

        #[cfg(target_os = "macos")]
        {
            let mut events: [libc::kevent64_s; 64] = unsafe { std::mem::zeroed() };
            let mut timeout_storage = timeout.map(|duration| libc::timespec {
                tv_sec: duration.as_secs() as libc::time_t,
                tv_nsec: duration.subsec_nanos() as libc::c_long,
            });
            let timeout_ptr = timeout_storage
                .as_mut()
                .map_or(ptr::null(), |timespec| timespec as *const libc::timespec);
            // A plain `kevent` with a zero timeout takes about 12 us to find nothing on
            // macOS, and this flag about 0.2 us. A kqueue accepts `kevent` or `kevent64`,
            // not both, so everything here uses the second.
            let flags = if timeout.is_some_and(|duration| duration.is_zero()) {
                libc::KEVENT_FLAG_IMMEDIATE
            } else {
                0
            };

            let ready = unsafe {
                libc::kevent64(
                    poll_fd,
                    ptr::null(),
                    0,
                    events.as_mut_ptr(),
                    events.len() as c_int,
                    flags,
                    timeout_ptr,
                )
            };

            if ready < 0 {
                let err = last_errno();
                if err == libc::EINTR {
                    return Vec::new();
                }
                panic!("async io poll wait failed with errno {err}");
            }
            if ready == 0 {
                return Vec::new();
            }
            with_reactor_mut(|reactor| {
                let tokens = reactor.process_kqueue_events(&events[..ready as usize]);
                tokens
                    .iter()
                    .filter_map(|token| reactor.wake_target(token))
                    .collect()
            })
            .unwrap_or_default()
        }
    }

    pub(crate) fn cancel_task(task_token: TaskToken) {
        let _ = with_reactor_mut(|reactor| reactor.cancel_task(task_token));
    }

    #[cfg(test)]
    pub(super) mod tests_support {
        use super::*;
        use crate::executor::test_task_wake;

        pub(crate) fn wake_for(task: u64) -> TaskWake {
            test_task_wake(task)
        }

        /// A private reactor over pipes, away from the process's real one.
        pub(crate) struct TestReactor {
            reactor: Reactor,
            pipes: Vec<RawFd>,
        }
        impl TestReactor {
            pub(crate) fn new() -> Self {
                Self {
                    reactor: Reactor::new().unwrap(),
                    pipes: Vec::new(),
                }
            }
            pub(crate) fn source(&mut self) -> usize {
                let mut fds = [0; 2];
                assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
                self.pipes.push(fds[1]);
                self.reactor.register_source(fds[0])
            }
            pub(crate) fn wait(&mut self, source: usize, task: &TaskWake, read: bool) {
                let interest = if read {
                    Interest::Read
                } else {
                    Interest::Write
                };
                // A pipe's read end can't arm for writing on every platform;
                // only the bookkeeping matters here.
                let _ = self.reactor.register_wait(source, task.clone(), interest);
            }
            pub(crate) fn waiters(&self, source: usize) -> (usize, usize) {
                let entry = &self.reactor.sources[&source];
                (entry.read_waiters.len(), entry.write_waiters.len())
            }
            pub(crate) fn finish(&mut self, task: &TaskWake) {
                self.reactor.cancel_task(task.identity());
            }
            pub(crate) fn close(&mut self, source: usize) {
                self.reactor.close_source(source);
            }
            pub(crate) fn is_tracking(&self, task: &TaskWake) -> bool {
                self.reactor.wake_targets.contains_key(&task.identity())
            }
            pub(crate) fn tracked_sources(&self, task: &TaskWake) -> usize {
                self.reactor.wake_targets[&task.identity()].sources.len()
            }
        }
        impl Drop for TestReactor {
            fn drop(&mut self) {
                let sources: Vec<_> = self.reactor.sources.keys().copied().collect();
                for source in sources {
                    self.reactor.close_source(source);
                }
                for &fd in &self.pipes {
                    unsafe { libc::close(fd) };
                }
            }
        }
    }
}

#[cfg(not(unix))]
mod imp {
    use super::{Interest, StdDuration, TaskToken, TaskWake};

    const UNSUPPORTED_ERRNO: i32 = 95;

    pub(crate) fn adopt_fd(_fd: i32) -> usize {
        0
    }

    pub(crate) fn close_source(_source_id: usize) -> (i32, Vec<TaskWake>) {
        (0, Vec::new())
    }

    pub(crate) fn dup_fd(_fd: i32) -> i32 {
        -1
    }

    pub(crate) fn create_pipe(_read_fd_out: *mut i32, _write_fd_out: *mut i32) -> i32 {
        -1
    }

    pub(crate) fn read_source(_source_id: usize, _buf: *mut u8, _len: usize) -> isize {
        -(UNSUPPORTED_ERRNO as isize)
    }

    pub(crate) fn write_source(_source_id: usize, _buf: *const u8, _len: usize) -> isize {
        -(UNSUPPORTED_ERRNO as isize)
    }

    pub(crate) fn register_wait(
        _source_id: usize,
        _target: TaskWake,
        _interest: Interest,
    ) -> Result<(), i32> {
        Err(UNSUPPORTED_ERRNO)
    }

    pub(crate) fn initialize() -> Result<(), i32> {
        Err(UNSUPPORTED_ERRNO)
    }

    pub(crate) fn notify() {}

    pub(crate) fn wait(_timeout: Option<StdDuration>) -> Vec<TaskWake> {
        Vec::new()
    }

    pub(crate) fn cancel_task(_task_token: TaskToken) {}
}

pub(crate) fn adopt_fd(fd: i32) -> usize {
    imp::adopt_fd(fd)
}

pub(crate) fn close_source(source_id: usize) -> (i32, Vec<TaskWake>) {
    imp::close_source(source_id)
}

pub(crate) fn dup_fd(fd: i32) -> i32 {
    imp::dup_fd(fd)
}

pub(crate) fn create_pipe(read_fd_out: *mut i32, write_fd_out: *mut i32) -> i32 {
    imp::create_pipe(read_fd_out, write_fd_out)
}

pub(crate) fn read_source(source_id: usize, buf: *mut u8, len: usize) -> isize {
    imp::read_source(source_id, buf, len)
}

pub(crate) fn write_source(source_id: usize, buf: *const u8, len: usize) -> isize {
    imp::write_source(source_id, buf, len)
}

pub(crate) fn register_wait(
    source_id: usize,
    target: TaskWake,
    interest: Interest,
) -> Result<(), i32> {
    imp::register_wait(source_id, target, interest)
}

pub(crate) fn initialize() -> Result<(), i32> {
    imp::initialize()
}

pub(crate) fn notify() {
    imp::notify()
}

pub(crate) fn wait(timeout: Option<StdDuration>) -> Vec<TaskWake> {
    imp::wait(timeout)
}

pub(crate) fn cancel_task(task_token: TaskToken) {
    imp::cancel_task(task_token)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_io_adopt_fd(fd: i32) -> usize {
    adopt_fd(fd)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_io_close_source(source_id: usize) -> i32 {
    let (result, waiters) = close_source(source_id);
    for target in waiters {
        target.wake();
    }
    result
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_io_dup(fd: i32) -> i32 {
    dup_fd(fd)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_io_pipe(read_fd_out: *mut i32, write_fd_out: *mut i32) -> i32 {
    create_pipe(read_fd_out, write_fd_out)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_io_read_source(source_id: usize, buf: *mut u8, len: usize) -> isize {
    read_source(source_id, buf, len)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_io_write_source(
    source_id: usize,
    buf: *const u8,
    len: usize,
) -> isize {
    write_source(source_id, buf, len)
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    fn is_open(fd: i32) -> bool {
        (unsafe { libc::fcntl(fd, libc::F_GETFD) }) != -1
    }

    #[test]
    fn disconnected_socket_write_returns_error_without_sigpipe() {
        const CHILD: &str = "TARO_SOCKET_SIGPIPE_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let child = std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "io_poller::tests::disconnected_socket_write_returns_error_without_sigpipe",
                ])
                .env(CHILD, "1")
                .output()
                .unwrap();
            assert!(
                child.status.success(),
                "disconnected write killed the child: {:?}\n{}",
                child.status,
                String::from_utf8_lossy(&child.stderr)
            );
            return;
        }
        // Rust main normally ignores SIGPIPE; Taro executable entry does not.
        // Reset it in a separate process so the test models Taro accurately.
        unsafe { libc::signal(libc::SIGPIPE, libc::SIG_DFL) };
        let mut fds = [0; 2];
        assert_eq!(
            unsafe { libc::socketpair(libc::AF_UNIX, libc::SOCK_STREAM, 0, fds.as_mut_ptr()) },
            0
        );
        let source = adopt_fd(fds[0]);
        assert_ne!(source, 0);
        unsafe { libc::close(fds[1]) };
        assert_eq!(
            write_source(source, b"x".as_ptr(), 1),
            -(libc::EPIPE as isize)
        );
        __rt__async_io_close_source(source);
    }

    mod waiting_tasks {
        use super::super::imp::tests_support::{TestReactor, wake_for};

        #[test]
        fn finishing_a_task_clears_its_waits_and_leaves_other_tasks_waiting() {
            let mut reactor = TestReactor::new();
            let (one, two) = (reactor.source(), reactor.source());
            let (leaving, staying) = (wake_for(1), wake_for(2));
            reactor.wait(one, &leaving, true);
            reactor.wait(one, &leaving, false);
            reactor.wait(two, &leaving, true);
            reactor.wait(one, &staying, true);
            assert_eq!(reactor.waiters(one), (2, 1));
            assert_eq!(reactor.waiters(two), (1, 0));

            reactor.finish(&leaving);
            assert_eq!(reactor.waiters(one), (1, 0));
            assert_eq!(reactor.waiters(two), (0, 0));
            assert!(reactor.is_tracking(&staying));
            assert!(!reactor.is_tracking(&leaving));
        }

        #[test]
        fn finishing_a_task_visits_only_the_sources_it_waited_on() {
            // Other connections' sources stay out of the finishing task's work:
            // on HEAD this cost one visit per open source for each finished task.
            let mut reactor = TestReactor::new();
            let own = reactor.source();
            for _ in 0..64 {
                reactor.source();
            }
            let task = wake_for(3);
            reactor.wait(own, &task, true);
            assert_eq!(reactor.tracked_sources(&task), 1);
            reactor.finish(&task);
            assert_eq!(reactor.waiters(own), (0, 0));
        }

        #[test]
        fn a_task_that_never_waited_has_nothing_to_finish() {
            let mut reactor = TestReactor::new();
            let source = reactor.source();
            let (waiting, idle) = (wake_for(4), wake_for(5));
            reactor.wait(source, &waiting, true);
            reactor.finish(&idle);
            assert_eq!(reactor.waiters(source), (1, 0));
        }

        #[test]
        fn a_long_lived_task_forgets_closed_sources() {
            let mut reactor = TestReactor::new();
            let task = wake_for(6);
            let open = reactor.source();
            reactor.wait(open, &task, true);
            for _ in 0..1_000 {
                let brief = reactor.source();
                reactor.wait(brief, &task, true);
                reactor.close(brief);
            }
            assert!(reactor.tracked_sources(&task) <= 32);
            reactor.finish(&task);
            assert_eq!(reactor.waiters(open), (0, 0));
        }
    }

    #[test]
    fn closing_a_source_defers_until_in_flight_operations_release_it() {
        let (mut read_fd, mut write_fd) = (0, 0);
        assert_eq!(create_pipe(&mut read_fd, &mut write_fd), 0);
        let source = adopt_fd(read_fd);
        assert_ne!(source, 0);

        // An operation between loading the descriptor and its syscall.
        assert_eq!(crate::fd_lease::acquire(source as u64), Ok(read_fd));
        assert_eq!(__rt__async_io_close_source(source), 0);
        assert!(
            is_open(read_fd),
            "close must not release a leased descriptor"
        );
        let mut byte = 0u8;
        assert_eq!(read_source(source, &mut byte, 1), -(libc::EBADF as isize));

        crate::fd_lease::release(source as u64);
        assert!(!is_open(read_fd), "the last release closes the descriptor");
        unsafe { libc::close(write_fd) };
    }

    fn closes_on_exec(fd: i32) -> bool {
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFD) };
        assert!(flags >= 0, "descriptor {fd} is open");
        flags & libc::FD_CLOEXEC != 0
    }

    fn reaches_eof_now(fd: i32) -> bool {
        let mut poll = libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        };
        assert!(unsafe { libc::poll(&mut poll, 1, 0) } >= 0);
        if poll.revents == 0 {
            return false;
        }
        let mut byte = 0u8;
        (unsafe { libc::read(fd, (&mut byte as *mut u8).cast(), 1) }) == 0
    }

    #[test]
    fn child_processes_do_not_inherit_runtime_descriptors() {
        let (mut read, mut write) = (-1, -1);
        assert_eq!(__rt__async_io_pipe(&mut read, &mut write), 0);
        let duplicate = __rt__async_io_dup(write);
        assert!(duplicate >= 0);
        for fd in [read, write, duplicate] {
            assert!(closes_on_exec(fd), "descriptor {fd} leaks into children");
        }

        // A child that inherited the write end would hold the pipe open, so
        // the reader would wait for the child instead of seeing EOF.
        let mut child = std::process::Command::new("/bin/sleep")
            .arg("5")
            .spawn()
            .unwrap();
        unsafe {
            libc::close(write);
            libc::close(duplicate);
        }
        let eof = reaches_eof_now(read);
        child.kill().unwrap();
        child.wait().unwrap();
        unsafe { libc::close(read) };
        assert!(eof, "the child kept the pipe open");
    }
}
