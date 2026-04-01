use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Mutex, OnceLock};

type TaskToken = u64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WaitKind {
    ChannelSend,
    ChannelRecv,
    Mutex,
    RwRead,
    RwWrite,
}

#[derive(Default)]
struct SyncState {
    channels: Vec<Option<ChannelState>>,
    free_channels: Vec<usize>,
    mutexes: Vec<Option<MutexState>>,
    free_mutexes: Vec<usize>,
    rwlocks: Vec<Option<RwLockState>>,
    free_rwlocks: Vec<usize>,
    ownership: HashMap<TaskToken, TaskOwnership>,
}

struct ChannelState {
    elem_size: usize,
    capacity: Option<usize>,
    closed: bool,
    queue: VecDeque<Vec<u8>>,
    send_waiters: VecDeque<TaskToken>,
    recv_waiters: VecDeque<TaskToken>,
}

struct MutexState {
    owner: Option<TaskToken>,
    waiters: VecDeque<TaskToken>,
}

struct RwLockState {
    writer: Option<TaskToken>,
    readers: HashMap<TaskToken, usize>,
    total_readers: usize,
    reader_waiters: VecDeque<TaskToken>,
    writer_waiters: VecDeque<TaskToken>,
}

#[derive(Default)]
struct TaskOwnership {
    mutexes: HashSet<usize>,
    rw_read: HashMap<usize, usize>,
    rw_write: HashMap<usize, usize>,
}

impl TaskOwnership {
    fn is_empty(&self) -> bool {
        self.mutexes.is_empty() && self.rw_read.is_empty() && self.rw_write.is_empty()
    }
}

fn state_cell() -> &'static Mutex<SyncState> {
    static CELL: OnceLock<Mutex<SyncState>> = OnceLock::new();
    CELL.get_or_init(|| Mutex::new(SyncState::default()))
}

fn err_invalid() -> i32 {
    libc::EBADF
}

fn err_busy() -> i32 {
    libc::EAGAIN
}

fn err_would_block() -> i32 {
    libc::EAGAIN
}

fn err_closed() -> i32 {
    libc::EPIPE
}

fn err_perm() -> i32 {
    libc::EPERM
}

fn push_unique(waiters: &mut Vec<TaskToken>, task_token: TaskToken) {
    if !waiters.contains(&task_token) {
        waiters.push(task_token);
    }
}

fn extend_unique(waiters: &mut Vec<TaskToken>, tasks: impl IntoIterator<Item = TaskToken>) {
    for task in tasks {
        push_unique(waiters, task);
    }
}

fn queue_waiter(queue: &mut VecDeque<TaskToken>, task_token: TaskToken) {
    if !queue.contains(&task_token) {
        queue.push_back(task_token);
    }
}

fn remove_waiter(queue: &mut VecDeque<TaskToken>, task_token: TaskToken) {
    queue.retain(|entry| *entry != task_token);
}

fn pop_waiter(queue: &mut VecDeque<TaskToken>) -> Option<TaskToken> {
    queue.pop_front()
}

fn current_task_token() -> Result<TaskToken, i32> {
    crate::executor::current_task_token().ok_or_else(err_perm)
}

impl SyncState {
    fn alloc_slot<T>(slots: &mut Vec<Option<T>>, free: &mut Vec<usize>, value: T) -> usize {
        if let Some(id) = free.pop() {
            slots[id] = Some(value);
            return id;
        }

        if slots.is_empty() {
            slots.push(None);
        }

        let id = slots.len();
        slots.push(Some(value));
        id
    }

    fn channel_create(&mut self, elem_size: usize, capacity: usize, bounded: bool) -> usize {
        if bounded && capacity == 0 {
            return 0;
        }

        Self::alloc_slot(
            &mut self.channels,
            &mut self.free_channels,
            ChannelState {
                elem_size,
                capacity: bounded.then_some(capacity),
                closed: false,
                queue: VecDeque::new(),
                send_waiters: VecDeque::new(),
                recv_waiters: VecDeque::new(),
            },
        )
    }

    fn channel_destroy(&mut self, channel_id: usize) -> (i32, Vec<TaskToken>) {
        let Some(slot) = self.channels.get_mut(channel_id) else {
            return (err_invalid(), Vec::new());
        };
        let Some(channel) = slot.take() else {
            return (err_invalid(), Vec::new());
        };

        self.free_channels.push(channel_id);

        let mut wake = Vec::new();
        extend_unique(&mut wake, channel.send_waiters);
        extend_unique(&mut wake, channel.recv_waiters);
        (0, wake)
    }

    fn channel_close(&mut self, channel_id: usize) -> (i32, Vec<TaskToken>) {
        let Some(channel) = self
            .channels
            .get_mut(channel_id)
            .and_then(Option::as_mut)
        else {
            return (err_invalid(), Vec::new());
        };

        if channel.closed {
            return (0, Vec::new());
        }

        channel.closed = true;
        let mut wake = Vec::new();
        extend_unique(&mut wake, channel.send_waiters.iter().copied());
        extend_unique(&mut wake, channel.recv_waiters.iter().copied());
        (0, wake)
    }

    fn channel_try_send(&mut self, channel_id: usize, value_ptr: *const u8) -> (i32, Vec<TaskToken>) {
        let Some(channel) = self
            .channels
            .get_mut(channel_id)
            .and_then(Option::as_mut)
        else {
            return (err_invalid(), Vec::new());
        };

        if channel.closed {
            return (err_closed(), Vec::new());
        }

        if let Some(cap) = channel.capacity {
            if channel.queue.len() >= cap {
                return (err_would_block(), Vec::new());
            }
        }

        if channel.elem_size > 0 && value_ptr.is_null() {
            return (libc::EINVAL, Vec::new());
        }

        let mut bytes = vec![0u8; channel.elem_size];
        if channel.elem_size > 0 {
            unsafe {
                std::ptr::copy_nonoverlapping(value_ptr, bytes.as_mut_ptr(), channel.elem_size);
            }
        }

        channel.queue.push_back(bytes);

        let mut wake = Vec::new();
        if let Some(waiter) = pop_waiter(&mut channel.recv_waiters) {
            push_unique(&mut wake, waiter);
        }

        (0, wake)
    }

    fn channel_try_recv(&mut self, channel_id: usize, out_ptr: *mut u8) -> (i32, Vec<TaskToken>) {
        let Some(channel) = self
            .channels
            .get_mut(channel_id)
            .and_then(Option::as_mut)
        else {
            return (err_invalid(), Vec::new());
        };

        if channel.elem_size > 0 && out_ptr.is_null() {
            return (libc::EINVAL, Vec::new());
        }

        let Some(bytes) = channel.queue.pop_front() else {
            if channel.closed {
                return (err_closed(), Vec::new());
            }
            return (err_would_block(), Vec::new());
        };

        if channel.elem_size > 0 {
            unsafe {
                std::ptr::copy_nonoverlapping(bytes.as_ptr(), out_ptr, channel.elem_size);
            }
        }

        let mut wake = Vec::new();
        if channel.capacity.is_some() {
            if let Some(waiter) = pop_waiter(&mut channel.send_waiters) {
                push_unique(&mut wake, waiter);
            }
        }

        (0, wake)
    }

    fn mutex_create(&mut self) -> usize {
        Self::alloc_slot(
            &mut self.mutexes,
            &mut self.free_mutexes,
            MutexState {
                owner: None,
                waiters: VecDeque::new(),
            },
        )
    }

    fn mutex_destroy(&mut self, mutex_id: usize) -> i32 {
        let Some(slot) = self.mutexes.get_mut(mutex_id) else {
            return err_invalid();
        };
        let Some(mutex) = slot.as_ref() else {
            return err_invalid();
        };

        if mutex.owner.is_some() || !mutex.waiters.is_empty() {
            return err_busy();
        }

        *slot = None;
        self.free_mutexes.push(mutex_id);
        0
    }

    fn mutex_try_lock(&mut self, mutex_id: usize, task_token: TaskToken) -> i32 {
        let Some(mutex) = self
            .mutexes
            .get_mut(mutex_id)
            .and_then(Option::as_mut)
        else {
            return err_invalid();
        };

        if mutex.owner.is_some() {
            return err_busy();
        }

        mutex.owner = Some(task_token);
        self.ownership
            .entry(task_token)
            .or_default()
            .mutexes
            .insert(mutex_id);
        0
    }

    fn mutex_unlock(&mut self, mutex_id: usize, task_token: TaskToken) -> (i32, Vec<TaskToken>) {
        let Some(mutex) = self
            .mutexes
            .get_mut(mutex_id)
            .and_then(Option::as_mut)
        else {
            return (err_invalid(), Vec::new());
        };

        if mutex.owner != Some(task_token) {
            return (err_perm(), Vec::new());
        }

        mutex.owner = None;

        if let Some(owned) = self.ownership.get_mut(&task_token) {
            owned.mutexes.remove(&mutex_id);
            if owned.is_empty() {
                self.ownership.remove(&task_token);
            }
        }

        let mut wake = Vec::new();
        if let Some(waiter) = pop_waiter(&mut mutex.waiters) {
            push_unique(&mut wake, waiter);
        }

        (0, wake)
    }

    fn rwlock_create(&mut self) -> usize {
        Self::alloc_slot(
            &mut self.rwlocks,
            &mut self.free_rwlocks,
            RwLockState {
                writer: None,
                readers: HashMap::new(),
                total_readers: 0,
                reader_waiters: VecDeque::new(),
                writer_waiters: VecDeque::new(),
            },
        )
    }

    fn rwlock_destroy(&mut self, lock_id: usize) -> i32 {
        let Some(slot) = self.rwlocks.get_mut(lock_id) else {
            return err_invalid();
        };
        let Some(lock) = slot.as_ref() else {
            return err_invalid();
        };

        if lock.writer.is_some()
            || lock.total_readers > 0
            || !lock.reader_waiters.is_empty()
            || !lock.writer_waiters.is_empty()
        {
            return err_busy();
        }

        *slot = None;
        self.free_rwlocks.push(lock_id);
        0
    }

    fn rwlock_try_read(&mut self, lock_id: usize, task_token: TaskToken) -> i32 {
        let Some(lock) = self
            .rwlocks
            .get_mut(lock_id)
            .and_then(Option::as_mut)
        else {
            return err_invalid();
        };

        // Writer-preferring: readers block if any writer is queued.
        if lock.writer.is_some() || !lock.writer_waiters.is_empty() {
            return err_busy();
        }

        *lock.readers.entry(task_token).or_insert(0) += 1;
        lock.total_readers += 1;

        *self
            .ownership
            .entry(task_token)
            .or_default()
            .rw_read
            .entry(lock_id)
            .or_insert(0) += 1;

        0
    }

    fn rwlock_try_write(&mut self, lock_id: usize, task_token: TaskToken) -> i32 {
        let Some(lock) = self
            .rwlocks
            .get_mut(lock_id)
            .and_then(Option::as_mut)
        else {
            return err_invalid();
        };

        if lock.writer.is_some() || lock.total_readers > 0 {
            return err_busy();
        }

        lock.writer = Some(task_token);

        *self
            .ownership
            .entry(task_token)
            .or_default()
            .rw_write
            .entry(lock_id)
            .or_insert(0) += 1;

        0
    }

    fn rwlock_unlock_read(&mut self, lock_id: usize, task_token: TaskToken) -> (i32, Vec<TaskToken>) {
        let Some(lock) = self
            .rwlocks
            .get_mut(lock_id)
            .and_then(Option::as_mut)
        else {
            return (err_invalid(), Vec::new());
        };

        let Some(count) = lock.readers.get_mut(&task_token) else {
            return (err_perm(), Vec::new());
        };

        *count -= 1;
        lock.total_readers = lock.total_readers.saturating_sub(1);
        if *count == 0 {
            lock.readers.remove(&task_token);
        }

        if let Some(owned) = self.ownership.get_mut(&task_token) {
            if let Some(read_count) = owned.rw_read.get_mut(&lock_id) {
                *read_count -= 1;
                if *read_count == 0 {
                    owned.rw_read.remove(&lock_id);
                }
            }
            if owned.is_empty() {
                self.ownership.remove(&task_token);
            }
        }

        let mut wake = Vec::new();
        if lock.total_readers == 0 {
            if let Some(waiter) = pop_waiter(&mut lock.writer_waiters) {
                push_unique(&mut wake, waiter);
            }
        }

        (0, wake)
    }

    fn rwlock_unlock_write(&mut self, lock_id: usize, task_token: TaskToken) -> (i32, Vec<TaskToken>) {
        let Some(lock) = self
            .rwlocks
            .get_mut(lock_id)
            .and_then(Option::as_mut)
        else {
            return (err_invalid(), Vec::new());
        };

        if lock.writer != Some(task_token) {
            return (err_perm(), Vec::new());
        }

        lock.writer = None;

        if let Some(owned) = self.ownership.get_mut(&task_token) {
            if let Some(write_count) = owned.rw_write.get_mut(&lock_id) {
                *write_count -= 1;
                if *write_count == 0 {
                    owned.rw_write.remove(&lock_id);
                }
            }
            if owned.is_empty() {
                self.ownership.remove(&task_token);
            }
        }

        let mut wake = Vec::new();
        if let Some(waiter) = pop_waiter(&mut lock.writer_waiters) {
            push_unique(&mut wake, waiter);
        } else {
            extend_unique(&mut wake, lock.reader_waiters.drain(..));
        }

        (0, wake)
    }

    fn register_wait(
        &mut self,
        task_token: TaskToken,
        id: usize,
        kind: WaitKind,
    ) -> Result<Vec<TaskToken>, i32> {
        let mut wake = Vec::new();

        match kind {
            WaitKind::ChannelSend => {
                let Some(channel) = self.channels.get_mut(id).and_then(Option::as_mut) else {
                    return Err(err_invalid());
                };
                queue_waiter(&mut channel.send_waiters, task_token);
                if channel.closed {
                    remove_waiter(&mut channel.send_waiters, task_token);
                    push_unique(&mut wake, task_token);
                } else {
                    let can_send = channel
                        .capacity
                        .map(|capacity| channel.queue.len() < capacity)
                        .unwrap_or(true);
                    if can_send {
                        remove_waiter(&mut channel.send_waiters, task_token);
                        push_unique(&mut wake, task_token);
                    }
                }
            }
            WaitKind::ChannelRecv => {
                let Some(channel) = self.channels.get_mut(id).and_then(Option::as_mut) else {
                    return Err(err_invalid());
                };
                queue_waiter(&mut channel.recv_waiters, task_token);
                if channel.closed || !channel.queue.is_empty() {
                    remove_waiter(&mut channel.recv_waiters, task_token);
                    push_unique(&mut wake, task_token);
                }
            }
            WaitKind::Mutex => {
                let Some(mutex) = self.mutexes.get_mut(id).and_then(Option::as_mut) else {
                    return Err(err_invalid());
                };
                queue_waiter(&mut mutex.waiters, task_token);
                if mutex.owner.is_none() {
                    remove_waiter(&mut mutex.waiters, task_token);
                    push_unique(&mut wake, task_token);
                }
            }
            WaitKind::RwRead => {
                let Some(lock) = self.rwlocks.get_mut(id).and_then(Option::as_mut) else {
                    return Err(err_invalid());
                };
                queue_waiter(&mut lock.reader_waiters, task_token);
                if lock.writer.is_none() && lock.writer_waiters.is_empty() {
                    remove_waiter(&mut lock.reader_waiters, task_token);
                    push_unique(&mut wake, task_token);
                }
            }
            WaitKind::RwWrite => {
                let Some(lock) = self.rwlocks.get_mut(id).and_then(Option::as_mut) else {
                    return Err(err_invalid());
                };
                queue_waiter(&mut lock.writer_waiters, task_token);
                let can_write = lock.writer.is_none()
                    && lock.total_readers == 0
                    && lock.writer_waiters.front().is_some_and(|front| *front == task_token);
                if can_write {
                    remove_waiter(&mut lock.writer_waiters, task_token);
                    push_unique(&mut wake, task_token);
                }
            }
        }

        Ok(wake)
    }

    fn collect_ready_waiters(&mut self, wake: &mut Vec<TaskToken>) {
        for channel in self.channels.iter_mut().flatten() {
            if channel.closed {
                extend_unique(wake, channel.send_waiters.drain(..));
                extend_unique(wake, channel.recv_waiters.drain(..));
                continue;
            }

            if !channel.queue.is_empty() {
                if let Some(waiter) = pop_waiter(&mut channel.recv_waiters) {
                    push_unique(wake, waiter);
                }
            }

            let can_send = channel
                .capacity
                .map(|capacity| channel.queue.len() < capacity)
                .unwrap_or(true);
            if can_send {
                if let Some(waiter) = pop_waiter(&mut channel.send_waiters) {
                    push_unique(wake, waiter);
                }
            }
        }

        for mutex in self.mutexes.iter_mut().flatten() {
            if mutex.owner.is_none() {
                if let Some(waiter) = pop_waiter(&mut mutex.waiters) {
                    push_unique(wake, waiter);
                }
            }
        }

        for lock in self.rwlocks.iter_mut().flatten() {
            if lock.writer.is_none() && lock.total_readers == 0 {
                if let Some(waiter) = pop_waiter(&mut lock.writer_waiters) {
                    push_unique(wake, waiter);
                    continue;
                }
            }

            if lock.writer.is_none() && lock.writer_waiters.is_empty() {
                extend_unique(wake, lock.reader_waiters.drain(..));
            }
        }
    }

    fn task_finalized(&mut self, task_token: TaskToken) -> Vec<TaskToken> {
        let mut wake = Vec::new();

        for channel in self.channels.iter_mut().flatten() {
            remove_waiter(&mut channel.send_waiters, task_token);
            remove_waiter(&mut channel.recv_waiters, task_token);
        }

        for mutex in self.mutexes.iter_mut().flatten() {
            remove_waiter(&mut mutex.waiters, task_token);
        }

        for lock in self.rwlocks.iter_mut().flatten() {
            remove_waiter(&mut lock.reader_waiters, task_token);
            remove_waiter(&mut lock.writer_waiters, task_token);
        }

        if let Some(owned) = self.ownership.remove(&task_token) {
            for mutex_id in owned.mutexes {
                let Some(mutex) = self.mutexes.get_mut(mutex_id).and_then(Option::as_mut) else {
                    continue;
                };
                if mutex.owner == Some(task_token) {
                    mutex.owner = None;
                    if let Some(waiter) = pop_waiter(&mut mutex.waiters) {
                        push_unique(&mut wake, waiter);
                    }
                }
            }

            for (lock_id, _) in owned.rw_read {
                let Some(lock) = self.rwlocks.get_mut(lock_id).and_then(Option::as_mut) else {
                    continue;
                };
                if let Some(count) = lock.readers.remove(&task_token) {
                    lock.total_readers = lock.total_readers.saturating_sub(count);
                    if lock.total_readers == 0 {
                        if let Some(waiter) = pop_waiter(&mut lock.writer_waiters) {
                            push_unique(&mut wake, waiter);
                        }
                    }
                }
            }

            for (lock_id, _) in owned.rw_write {
                let Some(lock) = self.rwlocks.get_mut(lock_id).and_then(Option::as_mut) else {
                    continue;
                };
                if lock.writer == Some(task_token) {
                    lock.writer = None;
                    if let Some(waiter) = pop_waiter(&mut lock.writer_waiters) {
                        push_unique(&mut wake, waiter);
                    } else {
                        extend_unique(&mut wake, lock.reader_waiters.drain(..));
                    }
                }
            }
        }

        self.collect_ready_waiters(&mut wake);

        wake
    }
}

pub(crate) fn register_wait(task_token: TaskToken, id: usize, kind: WaitKind) -> Result<(), i32> {
    let mut state = state_cell().lock().unwrap();
    let wake = state.register_wait(task_token, id, kind)?;
    drop(state);

    if !wake.is_empty() {
        crate::executor::wake_tasks(&wake);
    }

    Ok(())
}

pub(crate) fn task_finalized(task_token: TaskToken) {
    let mut state = state_cell().lock().unwrap();
    let wake = state.task_finalized(task_token);
    drop(state);

    if !wake.is_empty() {
        crate::executor::wake_tasks(&wake);
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_channel_create(elem_size: usize, capacity: usize, bounded: u8) -> usize {
    state_cell()
        .lock()
        .unwrap()
        .channel_create(elem_size, capacity, bounded != 0)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_channel_destroy(channel_id: usize) -> i32 {
    let mut state = state_cell().lock().unwrap();
    let (status, wake) = state.channel_destroy(channel_id);
    drop(state);

    if !wake.is_empty() {
        crate::executor::wake_tasks(&wake);
    }

    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_channel_close(channel_id: usize) -> i32 {
    let mut state = state_cell().lock().unwrap();
    let (status, wake) = state.channel_close(channel_id);
    drop(state);

    if !wake.is_empty() {
        crate::executor::wake_tasks(&wake);
    }

    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_channel_try_send(channel_id: usize, value_ptr: *const u8) -> i32 {
    let mut state = state_cell().lock().unwrap();
    let (status, wake) = state.channel_try_send(channel_id, value_ptr);
    drop(state);

    if !wake.is_empty() {
        crate::executor::wake_tasks(&wake);
    }

    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_channel_try_recv(channel_id: usize, out_ptr: *mut u8) -> i32 {
    let mut state = state_cell().lock().unwrap();
    let (status, wake) = state.channel_try_recv(channel_id, out_ptr);
    drop(state);

    if !wake.is_empty() {
        crate::executor::wake_tasks(&wake);
    }

    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_mutex_create() -> usize {
    state_cell().lock().unwrap().mutex_create()
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_mutex_destroy(mutex_id: usize) -> i32 {
    state_cell().lock().unwrap().mutex_destroy(mutex_id)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_mutex_try_lock(mutex_id: usize) -> i32 {
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    state_cell().lock().unwrap().mutex_try_lock(mutex_id, task_token)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_mutex_unlock(mutex_id: usize) -> i32 {
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    let mut state = state_cell().lock().unwrap();
    let (status, wake) = state.mutex_unlock(mutex_id, task_token);
    drop(state);

    if !wake.is_empty() {
        crate::executor::wake_tasks(&wake);
    }

    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_create() -> usize {
    state_cell().lock().unwrap().rwlock_create()
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_destroy(lock_id: usize) -> i32 {
    state_cell().lock().unwrap().rwlock_destroy(lock_id)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_try_read(lock_id: usize) -> i32 {
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    state_cell().lock().unwrap().rwlock_try_read(lock_id, task_token)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_try_write(lock_id: usize) -> i32 {
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    state_cell().lock().unwrap().rwlock_try_write(lock_id, task_token)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_unlock_read(lock_id: usize) -> i32 {
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    let mut state = state_cell().lock().unwrap();
    let (status, wake) = state.rwlock_unlock_read(lock_id, task_token);
    drop(state);

    if !wake.is_empty() {
        crate::executor::wake_tasks(&wake);
    }

    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_unlock_write(lock_id: usize) -> i32 {
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    let mut state = state_cell().lock().unwrap();
    let (status, wake) = state.rwlock_unlock_write(lock_id, task_token);
    drop(state);

    if !wake.is_empty() {
        crate::executor::wake_tasks(&wake);
    }

    status
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounded_channel_close_and_drain() {
        let mut state = SyncState::default();
        let id = state.channel_create(4, 1, true);
        assert_ne!(id, 0);

        let value = 7u32.to_ne_bytes();
        let (send_status, _) = state.channel_try_send(id, value.as_ptr());
        assert_eq!(send_status, 0);

        let second = 9u32.to_ne_bytes();
        let (blocked_status, _) = state.channel_try_send(id, second.as_ptr());
        assert_eq!(blocked_status, err_would_block());

        let mut out = [0u8; 4];
        let (recv_status, _) = state.channel_try_recv(id, out.as_mut_ptr());
        assert_eq!(recv_status, 0);
        assert_eq!(u32::from_ne_bytes(out), 7);

        let (close_status, _) = state.channel_close(id);
        assert_eq!(close_status, 0);

        let (closed_recv, _) = state.channel_try_recv(id, out.as_mut_ptr());
        assert_eq!(closed_recv, err_closed());
    }

    #[test]
    fn channel_try_recv_invalid_pointer_keeps_queued_value() {
        let mut state = SyncState::default();
        let id = state.channel_create(4, 1, true);
        assert_ne!(id, 0);

        let value = 27u32.to_ne_bytes();
        let (send_status, _) = state.channel_try_send(id, value.as_ptr());
        assert_eq!(send_status, 0);

        let (invalid_status, _) = state.channel_try_recv(id, std::ptr::null_mut());
        assert_eq!(invalid_status, libc::EINVAL);

        let mut out = [0u8; 4];
        let (recv_status, _) = state.channel_try_recv(id, out.as_mut_ptr());
        assert_eq!(recv_status, 0);
        assert_eq!(u32::from_ne_bytes(out), 27);
    }

    #[test]
    fn mutex_owner_enforced() {
        let mut state = SyncState::default();
        let id = state.mutex_create();
        assert_eq!(state.mutex_try_lock(id, 11), 0);
        assert_eq!(state.mutex_try_lock(id, 22), err_busy());
        assert_eq!(state.mutex_unlock(id, 22).0, err_perm());
        assert_eq!(state.mutex_unlock(id, 11).0, 0);
        assert_eq!(state.mutex_try_lock(id, 22), 0);
    }

    #[test]
    fn rwlock_writer_preference_blocks_new_readers() {
        let mut state = SyncState::default();
        let id = state.rwlock_create();

        assert_eq!(state.rwlock_try_read(id, 1), 0);
        let wake = state.register_wait(2, id, WaitKind::RwWrite).unwrap();
        assert!(wake.is_empty());

        assert_eq!(state.rwlock_try_read(id, 3), err_busy());

        let (unlock_status, wake_after_read) = state.rwlock_unlock_read(id, 1);
        assert_eq!(unlock_status, 0);
        assert_eq!(wake_after_read, vec![2]);
    }

    #[test]
    fn task_finalization_releases_owned_mutexes() {
        let mut state = SyncState::default();
        let id = state.mutex_create();
        assert_eq!(state.mutex_try_lock(id, 1), 0);
        let _ = state.register_wait(2, id, WaitKind::Mutex).unwrap();

        let wake = state.task_finalized(1);
        assert_eq!(wake, vec![2]);

        assert_eq!(state.mutex_try_lock(id, 2), 0);
    }

    #[test]
    fn task_finalization_requeues_mutex_when_woken_waiter_exits() {
        let mut state = SyncState::default();
        let id = state.mutex_create();
        assert_eq!(state.mutex_try_lock(id, 1), 0);
        let _ = state.register_wait(2, id, WaitKind::Mutex).unwrap();
        let _ = state.register_wait(3, id, WaitKind::Mutex).unwrap();

        let (unlock_status, wake) = state.mutex_unlock(id, 1);
        assert_eq!(unlock_status, 0);
        assert_eq!(wake, vec![2]);

        let wake_after_finalize = state.task_finalized(2);
        assert_eq!(wake_after_finalize, vec![3]);
    }

    #[test]
    fn mutex_destroy_returns_busy_with_pending_waiters() {
        let mut state = SyncState::default();
        let id = state.mutex_create();
        assert_eq!(state.mutex_try_lock(id, 1), 0);
        let _ = state.register_wait(2, id, WaitKind::Mutex).unwrap();
        let _ = state.register_wait(3, id, WaitKind::Mutex).unwrap();

        let (unlock_status, wake) = state.mutex_unlock(id, 1);
        assert_eq!(unlock_status, 0);
        assert_eq!(wake, vec![2]);
        assert_eq!(state.mutex_destroy(id), err_busy());
    }

    #[test]
    fn task_finalization_requeues_rwlock_readers_when_writer_exits() {
        let mut state = SyncState::default();
        let id = state.rwlock_create();
        assert_eq!(state.rwlock_try_read(id, 1), 0);

        let _ = state.register_wait(2, id, WaitKind::RwWrite).unwrap();
        let _ = state.register_wait(3, id, WaitKind::RwRead).unwrap();

        let (read_unlock_status, wake_writer) = state.rwlock_unlock_read(id, 1);
        assert_eq!(read_unlock_status, 0);
        assert_eq!(wake_writer, vec![2]);

        let wake_after_finalize = state.task_finalized(2);
        assert_eq!(wake_after_finalize, vec![3]);
    }

    #[test]
    fn rwlock_destroy_returns_busy_with_pending_waiters() {
        let mut state = SyncState::default();
        let id = state.rwlock_create();
        assert_eq!(state.rwlock_try_read(id, 1), 0);
        let _ = state.register_wait(2, id, WaitKind::RwWrite).unwrap();
        let _ = state.register_wait(3, id, WaitKind::RwWrite).unwrap();

        let (unlock_status, wake) = state.rwlock_unlock_read(id, 1);
        assert_eq!(unlock_status, 0);
        assert_eq!(wake, vec![2]);
        assert_eq!(state.rwlock_destroy(id), err_busy());
    }
}
