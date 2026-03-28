use std::time::Duration as StdDuration;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Interest {
    Read,
    Write,
}

#[cfg(unix)]
mod imp {
    use super::{Interest, StdDuration};
    use libc::{self, c_int};
    use std::collections::HashMap;
    use std::os::fd::RawFd;
    use std::ptr;
    use std::sync::Mutex;

    static REACTOR: Mutex<Option<Reactor>> = Mutex::new(None);

    struct SourceEntry {
        fd: RawFd,
        read_waiters: Vec<usize>,
        write_waiters: Vec<usize>,
        #[cfg(target_os = "linux")]
        registered: bool,
    }

    struct Reactor {
        poll_fd: RawFd,
        next_source_id: usize,
        sources: HashMap<usize, SourceEntry>,
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

            Ok(Self {
                poll_fd,
                next_source_id: 1,
                sources: HashMap::new(),
            })
        }

        fn register_source(&mut self, fd: RawFd) -> usize {
            let source_id = self.next_source_id;
            self.next_source_id = self
                .next_source_id
                .checked_add(1)
                .expect("async io source id overflow");
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
            task_id: usize,
            interest: Interest,
        ) -> Result<(), i32> {
            let Some(source) = self.sources.get_mut(&source_id) else {
                return Err(libc::EBADF);
            };

            let waiters = match interest {
                Interest::Read => &mut source.read_waiters,
                Interest::Write => &mut source.write_waiters,
            };

            if !waiters.contains(&task_id) {
                waiters.push(task_id);
            }

            self.arm_wait(source_id, interest)
        }

        fn has_waiters(&self) -> bool {
            self.sources
                .values()
                .any(|source| !source.read_waiters.is_empty() || !source.write_waiters.is_empty())
        }

        fn cancel_task(&mut self, task_id: usize) {
            #[cfg(target_os = "linux")]
            let mut needs_rearm = Vec::new();

            for (&source_id, source) in &mut self.sources {
                #[cfg(not(target_os = "linux"))]
                let _ = source_id;

                #[cfg(target_os = "linux")]
                let mut cleared = false;

                let read_before = source.read_waiters.len();
                source.read_waiters.retain(|waiter| *waiter != task_id);
                if source.read_waiters.len() != read_before {
                    #[cfg(target_os = "linux")]
                    {
                        cleared = true;
                    }
                }

                let write_before = source.write_waiters.len();
                source.write_waiters.retain(|waiter| *waiter != task_id);
                if source.write_waiters.len() != write_before {
                    #[cfg(target_os = "linux")]
                    {
                        cleared = true;
                    }
                }

                #[cfg(target_os = "linux")]
                if cleared && (!source.read_waiters.is_empty() || !source.write_waiters.is_empty())
                {
                    needs_rearm.push(source_id);
                }
            }

            #[cfg(target_os = "linux")]
            for source_id in needs_rearm {
                let _ = self.rearm_linux_source(source_id);
            }
        }

        fn close_source(&mut self, source_id: usize) -> (c_int, Vec<usize>) {
            let Some(source) = self.sources.remove(&source_id) else {
                return (0, Vec::new());
            };

            let mut wake = Vec::new();
            extend_unique(&mut wake, &source.read_waiters);
            extend_unique(&mut wake, &source.write_waiters);
            (close_fd(source.fd), wake)
        }

        fn source_fd(&self, source_id: usize) -> Result<RawFd, i32> {
            self.sources
                .get(&source_id)
                .map(|source| source.fd)
                .ok_or(libc::EBADF)
        }

        #[cfg(target_os = "linux")]
        fn process_epoll_events(&mut self, events: &[libc::epoll_event]) -> Vec<usize> {
            let mut wake = Vec::new();
            let mut rearm = Vec::new();
            for event in events {
                let source_id = event.u64 as usize;
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

            wake
        }

        #[cfg(target_os = "macos")]
        fn process_kqueue_events(&mut self, events: &[libc::kevent]) -> Vec<usize> {
            let mut wake = Vec::new();
            for event in events {
                let source_id = event.udata as usize;
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
            let mut change = libc::kevent {
                ident: source.fd as libc::uintptr_t,
                filter,
                flags: (libc::EV_ADD | libc::EV_ENABLE | libc::EV_ONESHOT) as u16,
                fflags: 0,
                data: 0,
                udata: source_id as usize as *mut libc::c_void,
            };

            if unsafe {
                libc::kevent(
                    self.poll_fd,
                    &mut change,
                    1,
                    ptr::null_mut(),
                    0,
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

    fn close_fd(fd: RawFd) -> c_int {
        if fd < 0 {
            return 0;
        }

        let result = unsafe { libc::close(fd) };
        if result == 0 {
            return 0;
        }

        let err = last_errno();
        if err == libc::EINTR { 0 } else { -err }
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

    fn push_unique(waiters: &mut Vec<usize>, task_id: usize) {
        if !waiters.contains(&task_id) {
            waiters.push(task_id);
        }
    }

    fn extend_unique(dst: &mut Vec<usize>, src: &[usize]) {
        for &task_id in src {
            push_unique(dst, task_id);
        }
    }

    fn drain_unique(dst: &mut Vec<usize>, src: &mut Vec<usize>) {
        for task_id in src.drain(..) {
            push_unique(dst, task_id);
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

        if let Err(_err) = ensure_reactor() {
            return 0;
        }

        with_reactor_mut(|reactor| reactor.register_source(fd)).unwrap_or(0)
    }

    pub(crate) fn close_source(source_id: usize) -> (c_int, Vec<usize>) {
        if source_id == 0 {
            return (0, Vec::new());
        }

        if let Some(result) = with_reactor_mut(|reactor| reactor.close_source(source_id)) {
            result
        } else {
            (0, Vec::new())
        }
    }

    pub(crate) fn dup_fd(fd: RawFd) -> c_int {
        loop {
            let result = unsafe { libc::dup(fd) };
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
            let result = unsafe { libc::pipe(fds.as_mut_ptr()) };
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
        let fd =
            with_reactor_mut(|reactor| reactor.source_fd(source_id)).unwrap_or(Err(libc::EBADF));
        let fd = match fd {
            Ok(value) => value,
            Err(err) => return -(err as isize),
        };

        let result = unsafe { libc::read(fd, buf.cast(), len) };
        if result < 0 {
            -(last_errno() as isize)
        } else {
            result as isize
        }
    }

    pub(crate) fn write_source(source_id: usize, buf: *const u8, len: usize) -> isize {
        let fd =
            with_reactor_mut(|reactor| reactor.source_fd(source_id)).unwrap_or(Err(libc::EBADF));
        let fd = match fd {
            Ok(value) => value,
            Err(err) => return -(err as isize),
        };

        let result = unsafe { libc::write(fd, buf.cast(), len) };
        if result < 0 {
            -(last_errno() as isize)
        } else {
            result as isize
        }
    }

    pub(crate) fn register_wait(
        source_id: usize,
        task_id: usize,
        interest: Interest,
    ) -> Result<(), i32> {
        ensure_reactor()?;
        with_reactor_mut(|reactor| reactor.register_wait(source_id, task_id, interest))
            .expect("async io reactor missing after initialization")
    }

    pub(crate) fn has_waiters() -> bool {
        with_reactor_mut(|reactor| reactor.has_waiters()).unwrap_or(false)
    }

    pub(crate) fn wait(timeout: Option<StdDuration>) -> Vec<usize> {
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
            crate::garbage_collector::enter_safepoint();
            let ready = unsafe {
                libc::epoll_wait(
                    poll_fd,
                    events.as_mut_ptr(),
                    events.len() as c_int,
                    timeout_ms,
                )
            };
            crate::garbage_collector::leave_safepoint();

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
            with_reactor_mut(|reactor| reactor.process_epoll_events(&events[..ready as usize]))
                .unwrap_or_default()
        }

        #[cfg(target_os = "macos")]
        {
            let mut events: [libc::kevent; 64] = unsafe { std::mem::zeroed() };
            let mut timeout_storage = timeout.map(|duration| libc::timespec {
                tv_sec: duration.as_secs() as libc::time_t,
                tv_nsec: duration.subsec_nanos() as libc::c_long,
            });
            let timeout_ptr = timeout_storage
                .as_mut()
                .map_or(ptr::null(), |timespec| timespec as *const libc::timespec);

            crate::garbage_collector::enter_safepoint();
            let ready = unsafe {
                libc::kevent(
                    poll_fd,
                    ptr::null(),
                    0,
                    events.as_mut_ptr(),
                    events.len() as c_int,
                    timeout_ptr,
                )
            };
            crate::garbage_collector::leave_safepoint();

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
            with_reactor_mut(|reactor| reactor.process_kqueue_events(&events[..ready as usize]))
                .unwrap_or_default()
        }
    }

    pub(crate) fn cancel_task(task_id: usize) {
        let _ = with_reactor_mut(|reactor| reactor.cancel_task(task_id));
    }
}

#[cfg(not(unix))]
mod imp {
    use super::{Interest, StdDuration};

    const UNSUPPORTED_ERRNO: i32 = 95;

    pub(crate) fn adopt_fd(_fd: i32) -> usize {
        0
    }

    pub(crate) fn close_source(_source_id: usize) -> (i32, Vec<usize>) {
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
        _task_id: usize,
        _interest: Interest,
    ) -> Result<(), i32> {
        Err(UNSUPPORTED_ERRNO)
    }

    pub(crate) fn has_waiters() -> bool {
        false
    }

    pub(crate) fn wait(_timeout: Option<StdDuration>) -> Vec<usize> {
        Vec::new()
    }

    pub(crate) fn cancel_task(_task_id: usize) {}
}

pub(crate) fn adopt_fd(fd: i32) -> usize {
    imp::adopt_fd(fd)
}

pub(crate) fn close_source(source_id: usize) -> (i32, Vec<usize>) {
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
    task_id: usize,
    interest: Interest,
) -> Result<(), i32> {
    imp::register_wait(source_id, task_id, interest)
}

pub(crate) fn has_waiters() -> bool {
    imp::has_waiters()
}

pub(crate) fn wait(timeout: Option<StdDuration>) -> Vec<usize> {
    imp::wait(timeout)
}

pub(crate) fn cancel_task(task_id: usize) {
    imp::cancel_task(task_id)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_io_adopt_fd(fd: i32) -> usize {
    adopt_fd(fd)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__async_io_close_source(source_id: usize) -> i32 {
    let (result, waiters) = close_source(source_id);
    if !waiters.is_empty() {
        crate::executor::wake_tasks(&waiters);
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
