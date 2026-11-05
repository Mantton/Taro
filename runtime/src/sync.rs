use crate::executor::{TaskIdentity, TaskWake};
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex, OnceLock};

mod channel_value;
#[cfg(test)]
mod identity_tests;
use channel_value::{ChannelLayout, QueuedValue};

// Process-wide registry IDs, distinct from scheduler-local executor tokens.
// They are interned from TaskIdentity and are never reused.
type SyncTaskId = u64;

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
    // Every handle/wait/ownership entry carries a never-reused family identity,
    // independently of reusable vector storage. Delayed native operations
    // cannot act on a replacement that happens to reuse a slot.
    channel_slots: HashMap<usize, usize>,
    next_channel_id: usize,
    mutexes: Vec<Option<MutexState>>,
    free_mutexes: Vec<usize>,
    mutex_slots: HashMap<usize, usize>,
    next_mutex_id: usize,
    rwlocks: Vec<Option<RwLockState>>,
    free_rwlocks: Vec<usize>,
    rwlock_slots: HashMap<usize, usize>,
    next_rwlock_id: usize,
    ownership: HashMap<SyncTaskId, TaskOwnership>,
    // A low-level lock may outlive its last source handle while a task still
    // holds logical ownership. That native task lease, not tracing, keeps the
    // registry entry until task finalization releases it.
    retired_mutexes: HashSet<usize>,
    retired_rwlocks: HashSet<usize>,
    next_task_id: SyncTaskId,
    task_bindings: HashMap<TaskIdentity, SyncTaskId>,
    wake_targets: HashMap<SyncTaskId, TaskWake>,
}

struct ChannelState {
    elem_size: usize,
    layout: Arc<ChannelLayout>,
    capacity: Option<usize>,
    closed: bool,
    queue: VecDeque<QueuedValue>,
    send_waiters: VecDeque<SyncTaskId>,
    recv_waiters: VecDeque<SyncTaskId>,
}

struct MutexState {
    owner: Option<SyncTaskId>,
    waiters: VecDeque<SyncTaskId>,
}

struct RwLockState {
    writer: Option<SyncTaskId>,
    readers: HashMap<SyncTaskId, usize>,
    total_readers: usize,
    reader_waiters: VecDeque<SyncTaskId>,
    writer_waiters: VecDeque<SyncTaskId>,
}

#[derive(Default)]
struct TaskOwnership {
    mutexes: HashSet<usize>,
    rw_read: HashMap<usize, usize>,
    rw_write: HashMap<usize, usize>,
}

#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SyncHandleKind {
    Channel = 1,
    Mutex = 2,
    RwLock = 3,
}

#[repr(C)]
struct SyncHandle {
    id: usize,
    kind: SyncHandleKind,
}

fn handle_id(handle: *const u8, expected: SyncHandleKind) -> Result<usize, i32> {
    let Some(handle) = (unsafe { (handle as *const SyncHandle).as_ref() }) else {
        return Err(err_invalid());
    };
    if handle.kind != expected {
        return Err(err_invalid());
    }
    Ok(handle.id)
}

// `SyncState::task_bindings.len()`, readable without the registry's lock.
static TASK_BINDINGS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
static LIVE_SYNC_HANDLES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn allocate_handle(id: usize, kind: SyncHandleKind) -> *mut u8 {
    LIVE_SYNC_HANDLES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    // A GC native-owner object releases this opaque box when unreachable.
    // Copied endpoints share that owner, never duplicate the box.
    Box::into_raw(Box::new(SyncHandle { id, kind })).cast()
}

/// Release the unique opaque handle when its GC owner is reclaimed. Explicit
/// destroy only retires registry state, so copied handles remain valid closed
/// identities until the owner is reclaimed. The Box is freed on unwind too.
///
/// # Safety
/// handle is null or one live allocation returned by allocate_handle; this
/// function consumes its sole native ownership obligation exactly once.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __rt__sync_handle_release(handle: *mut u8) {
    if handle.is_null() {
        return;
    }
    let handle = unsafe { Box::from_raw(handle.cast::<SyncHandle>()) };
    LIVE_SYNC_HANDLES.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
    match handle.kind {
        SyncHandleKind::Channel => {
            let _ = finish_channel_destroy(handle.id);
        }
        SyncHandleKind::Mutex => {
            state_cell().lock().unwrap().retire_mutex(handle.id);
        }
        SyncHandleKind::RwLock => {
            state_cell().lock().unwrap().retire_rwlock(handle.id);
        }
    }
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

fn push_unique(waiters: &mut Vec<SyncTaskId>, task_token: SyncTaskId) {
    if !waiters.contains(&task_token) {
        waiters.push(task_token);
    }
}

fn extend_unique(waiters: &mut Vec<SyncTaskId>, tasks: impl IntoIterator<Item = SyncTaskId>) {
    for task in tasks {
        push_unique(waiters, task);
    }
}

fn queue_waiter(queue: &mut VecDeque<SyncTaskId>, task_token: SyncTaskId) {
    if !queue.contains(&task_token) {
        queue.push_back(task_token);
    }
}

fn remove_waiter(queue: &mut VecDeque<SyncTaskId>, task_token: SyncTaskId) {
    queue.retain(|entry| *entry != task_token);
}

fn pop_waiter(queue: &mut VecDeque<SyncTaskId>) -> Option<SyncTaskId> {
    queue.pop_front()
}

fn front_waiter(queue: &VecDeque<SyncTaskId>) -> Option<SyncTaskId> {
    queue.front().copied()
}

fn current_task_token() -> Result<SyncTaskId, i32> {
    let target = crate::executor::current_task_wake().ok_or_else(err_perm)?;
    Ok(state_cell().lock().unwrap().bind_task(target))
}

pub(crate) fn wait_handle_id(handle: *const u8, kind: WaitKind) -> Result<usize, i32> {
    let expected = match kind {
        WaitKind::ChannelSend | WaitKind::ChannelRecv => SyncHandleKind::Channel,
        WaitKind::Mutex => SyncHandleKind::Mutex,
        WaitKind::RwRead | WaitKind::RwWrite => SyncHandleKind::RwLock,
    };
    handle_id(handle, expected)
}

impl SyncState {
    fn bind_task(&mut self, target: TaskWake) -> SyncTaskId {
        let identity = target.identity();
        let id = if let Some(&id) = self.task_bindings.get(&identity) {
            id
        } else {
            self.next_task_id = self
                .next_task_id
                .checked_add(1)
                .expect("synchronization task identity space exhausted");
            self.task_bindings.insert(identity, self.next_task_id);
            TASK_BINDINGS.fetch_add(1, Ordering::Release);
            self.next_task_id
        };
        self.wake_targets.insert(id, target);
        id
    }

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

    fn channel(&self, id: usize) -> Option<&ChannelState> {
        let slot = *self.channel_slots.get(&id)?;
        self.channels.get(slot)?.as_ref()
    }

    fn channel_mut(&mut self, id: usize) -> Option<&mut ChannelState> {
        let slot = *self.channel_slots.get(&id)?;
        self.channels.get_mut(slot)?.as_mut()
    }

    fn channel_create_with_layout(
        &mut self,
        layout: Arc<ChannelLayout>,
        capacity: usize,
        bounded: bool,
    ) -> usize {
        if bounded && capacity == 0 {
            return 0;
        }
        let elem_size = layout.size;
        let Some(id) = self.next_channel_id.checked_add(1) else {
            return 0;
        };
        let slot = Self::alloc_slot(
            &mut self.channels,
            &mut self.free_channels,
            ChannelState {
                elem_size,
                layout,
                capacity: bounded.then_some(capacity),
                closed: false,
                queue: VecDeque::new(),
                send_waiters: VecDeque::new(),
                recv_waiters: VecDeque::new(),
            },
        );
        self.next_channel_id = id;
        self.channel_slots.insert(id, slot);
        id
    }

    fn channel_destroy(
        &mut self,
        channel_id: usize,
    ) -> (i32, Vec<SyncTaskId>, VecDeque<QueuedValue>) {
        let Some(slot) = self.channel_slots.remove(&channel_id) else {
            return (err_invalid(), Vec::new(), VecDeque::new());
        };
        let channel = self.channels[slot].take().expect("live channel identity");
        self.free_channels.push(slot);

        let mut wake = Vec::new();
        extend_unique(&mut wake, channel.send_waiters);
        extend_unique(&mut wake, channel.recv_waiters);
        // Move the complete queue out. Payload code runs only after the caller
        // releases the registry lock and wakes waiters.
        (0, wake, channel.queue)
    }

    fn channel_close(&mut self, channel_id: usize) -> (i32, Vec<SyncTaskId>) {
        let Some(channel) = self.channel_mut(channel_id) else {
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

    fn channel_send_status(&self, channel_id: usize) -> i32 {
        let Some(channel) = self.channel(channel_id) else {
            return err_invalid();
        };
        if channel.closed {
            return err_closed();
        }
        if channel
            .capacity
            .is_some_and(|capacity| channel.queue.len() >= capacity)
        {
            return err_would_block();
        }
        0
    }

    fn channel_try_send_value(
        &mut self,
        channel_id: usize,
        mut value: QueuedValue,
    ) -> (i32, Vec<SyncTaskId>, Option<QueuedValue>) {
        let Some(channel) = self.channel_mut(channel_id) else {
            return (err_invalid(), Vec::new(), Some(value));
        };

        if channel.closed {
            return (err_closed(), Vec::new(), Some(value));
        }

        if let Some(cap) = channel.capacity {
            if channel.queue.len() >= cap {
                return (err_would_block(), Vec::new(), Some(value));
            }
        }

        value.commit();
        channel.queue.push_back(value);

        let mut wake = Vec::new();
        if let Some(waiter) = pop_waiter(&mut channel.recv_waiters) {
            push_unique(&mut wake, waiter);
        }

        (0, wake, None)
    }

    #[cfg(test)]
    fn channel_try_send(
        &mut self,
        channel_id: usize,
        value_ptr: *const u8,
    ) -> (i32, Vec<SyncTaskId>) {
        let Some(channel) = self.channel(channel_id) else {
            return (err_invalid(), Vec::new());
        };
        let value = match unsafe { QueuedValue::prepare(&channel.layout, value_ptr) } {
            Ok(value) => value,
            Err(error) => return (error, Vec::new()),
        };
        let (status, wake, _) = self.channel_try_send_value(channel_id, value);
        (status, wake)
    }

    fn channel_try_recv(
        &mut self,
        channel_id: usize,
        out_ptr: *mut u8,
    ) -> (i32, Vec<SyncTaskId>, Option<QueuedValue>) {
        let Some(channel) = self.channel_mut(channel_id) else {
            return (err_invalid(), Vec::new(), None);
        };

        if channel.elem_size > 0 && out_ptr.is_null() {
            return (libc::EINVAL, Vec::new(), None);
        }

        let Some(mut value) = channel.queue.pop_front() else {
            if channel.closed {
                return (err_closed(), Vec::new(), None);
            }
            return (err_would_block(), Vec::new(), None);
        };

        unsafe { value.move_into(out_ptr) };

        let mut wake = Vec::new();
        if channel.capacity.is_some() {
            if let Some(waiter) = pop_waiter(&mut channel.send_waiters) {
                push_unique(&mut wake, waiter);
            }
        }

        (0, wake, Some(value))
    }

    fn mutex_create(&mut self) -> usize {
        let Some(id) = self.next_mutex_id.checked_add(1) else {
            return 0;
        };
        let slot = Self::alloc_slot(
            &mut self.mutexes,
            &mut self.free_mutexes,
            MutexState {
                owner: None,
                waiters: VecDeque::new(),
            },
        );
        self.next_mutex_id = id;
        self.mutex_slots.insert(id, slot);
        id
    }

    fn retire_mutex(&mut self, id: usize) {
        if self.mutex_destroy(id) == err_busy() {
            self.retired_mutexes.insert(id);
        }
    }
    fn retire_rwlock(&mut self, id: usize) {
        if self.rwlock_destroy(id) == err_busy() {
            self.retired_rwlocks.insert(id);
        }
    }
    fn collect_retired_locks(&mut self) {
        for id in std::mem::take(&mut self.retired_mutexes) {
            self.retire_mutex(id);
        }
        for id in std::mem::take(&mut self.retired_rwlocks) {
            self.retire_rwlock(id);
        }
    }

    fn mutex_destroy(&mut self, mutex_id: usize) -> i32 {
        let Some(&slot_id) = self.mutex_slots.get(&mutex_id) else {
            return err_invalid();
        };
        let Some(slot) = self.mutexes.get_mut(slot_id) else {
            return err_invalid();
        };
        let Some(mutex) = slot.as_ref() else {
            return err_invalid();
        };

        if mutex.owner.is_some() || !mutex.waiters.is_empty() {
            return err_busy();
        }

        *slot = None;
        self.mutex_slots.remove(&mutex_id);
        self.retired_mutexes.remove(&mutex_id);
        self.free_mutexes.push(slot_id);
        0
    }

    fn mutex_try_lock(&mut self, mutex_id: usize, task_token: SyncTaskId) -> i32 {
        let Some(&slot_id) = self.mutex_slots.get(&mutex_id) else {
            return err_invalid();
        };
        let Some(mutex) = self.mutexes.get_mut(slot_id).and_then(Option::as_mut) else {
            return err_invalid();
        };

        if mutex.owner.is_some() {
            return err_busy();
        }

        if let Some(front) = front_waiter(&mutex.waiters) {
            if front != task_token {
                return err_busy();
            }
            mutex.waiters.pop_front();
        }

        mutex.owner = Some(task_token);
        self.ownership
            .entry(task_token)
            .or_default()
            .mutexes
            .insert(mutex_id);
        0
    }

    fn mutex_unlock(&mut self, mutex_id: usize, task_token: SyncTaskId) -> (i32, Vec<SyncTaskId>) {
        let Some(&slot_id) = self.mutex_slots.get(&mutex_id) else {
            return (err_invalid(), Vec::new());
        };
        let Some(mutex) = self.mutexes.get_mut(slot_id).and_then(Option::as_mut) else {
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
        if let Some(waiter) = front_waiter(&mutex.waiters) {
            push_unique(&mut wake, waiter);
        }

        (0, wake)
    }

    fn rwlock_create(&mut self) -> usize {
        let Some(id) = self.next_rwlock_id.checked_add(1) else {
            return 0;
        };
        let slot = Self::alloc_slot(
            &mut self.rwlocks,
            &mut self.free_rwlocks,
            RwLockState {
                writer: None,
                readers: HashMap::new(),
                total_readers: 0,
                reader_waiters: VecDeque::new(),
                writer_waiters: VecDeque::new(),
            },
        );
        self.next_rwlock_id = id;
        self.rwlock_slots.insert(id, slot);
        id
    }

    fn rwlock_destroy(&mut self, lock_id: usize) -> i32 {
        let Some(&slot_id) = self.rwlock_slots.get(&lock_id) else {
            return err_invalid();
        };
        let Some(slot) = self.rwlocks.get_mut(slot_id) else {
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
        self.rwlock_slots.remove(&lock_id);
        self.retired_rwlocks.remove(&lock_id);
        self.free_rwlocks.push(slot_id);
        0
    }

    fn rwlock_try_read(&mut self, lock_id: usize, task_token: SyncTaskId) -> i32 {
        let Some(&slot_id) = self.rwlock_slots.get(&lock_id) else {
            return err_invalid();
        };
        let Some(lock) = self.rwlocks.get_mut(slot_id).and_then(Option::as_mut) else {
            return err_invalid();
        };

        // Writer-preferring: readers block if any writer is queued.
        if lock.writer.is_some() || !lock.writer_waiters.is_empty() {
            return err_busy();
        }

        remove_waiter(&mut lock.reader_waiters, task_token);
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

    fn rwlock_try_write(&mut self, lock_id: usize, task_token: SyncTaskId) -> i32 {
        let Some(&slot_id) = self.rwlock_slots.get(&lock_id) else {
            return err_invalid();
        };
        let Some(lock) = self.rwlocks.get_mut(slot_id).and_then(Option::as_mut) else {
            return err_invalid();
        };

        if lock.writer.is_some() || lock.total_readers > 0 {
            return err_busy();
        }

        if let Some(front) = front_waiter(&lock.writer_waiters) {
            if front != task_token {
                return err_busy();
            }
            lock.writer_waiters.pop_front();
        } else if !lock.reader_waiters.is_empty() {
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

    fn rwlock_unlock_read(
        &mut self,
        lock_id: usize,
        task_token: SyncTaskId,
    ) -> (i32, Vec<SyncTaskId>) {
        let Some(&slot_id) = self.rwlock_slots.get(&lock_id) else {
            return (err_invalid(), Vec::new());
        };
        let Some(lock) = self.rwlocks.get_mut(slot_id).and_then(Option::as_mut) else {
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
            if let Some(waiter) = front_waiter(&lock.writer_waiters) {
                push_unique(&mut wake, waiter);
            } else {
                extend_unique(&mut wake, lock.reader_waiters.iter().copied());
            }
        }

        (0, wake)
    }

    fn rwlock_unlock_write(
        &mut self,
        lock_id: usize,
        task_token: SyncTaskId,
    ) -> (i32, Vec<SyncTaskId>) {
        let Some(&slot_id) = self.rwlock_slots.get(&lock_id) else {
            return (err_invalid(), Vec::new());
        };
        let Some(lock) = self.rwlocks.get_mut(slot_id).and_then(Option::as_mut) else {
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
        if let Some(waiter) = front_waiter(&lock.writer_waiters) {
            push_unique(&mut wake, waiter);
        } else {
            extend_unique(&mut wake, lock.reader_waiters.iter().copied());
        }

        (0, wake)
    }

    fn register_wait(
        &mut self,
        task_token: SyncTaskId,
        id: usize,
        kind: WaitKind,
    ) -> Result<Vec<SyncTaskId>, i32> {
        let mut wake = Vec::new();

        match kind {
            WaitKind::ChannelSend => {
                let Some(channel) = self.channel_mut(id) else {
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
                let Some(channel) = self.channel_mut(id) else {
                    return Err(err_invalid());
                };
                queue_waiter(&mut channel.recv_waiters, task_token);
                if channel.closed || !channel.queue.is_empty() {
                    remove_waiter(&mut channel.recv_waiters, task_token);
                    push_unique(&mut wake, task_token);
                }
            }
            WaitKind::Mutex => {
                let Some(&slot_id) = self.mutex_slots.get(&id) else {
                    return Err(err_invalid());
                };
                let Some(mutex) = self.mutexes.get_mut(slot_id).and_then(Option::as_mut) else {
                    return Err(err_invalid());
                };
                queue_waiter(&mut mutex.waiters, task_token);
                if mutex.owner.is_none() && front_waiter(&mutex.waiters) == Some(task_token) {
                    push_unique(&mut wake, task_token);
                }
            }
            WaitKind::RwRead => {
                let Some(&slot_id) = self.rwlock_slots.get(&id) else {
                    return Err(err_invalid());
                };
                let Some(lock) = self.rwlocks.get_mut(slot_id).and_then(Option::as_mut) else {
                    return Err(err_invalid());
                };
                queue_waiter(&mut lock.reader_waiters, task_token);
                if lock.writer.is_none() && lock.writer_waiters.is_empty() {
                    push_unique(&mut wake, task_token);
                }
            }
            WaitKind::RwWrite => {
                let Some(&slot_id) = self.rwlock_slots.get(&id) else {
                    return Err(err_invalid());
                };
                let Some(lock) = self.rwlocks.get_mut(slot_id).and_then(Option::as_mut) else {
                    return Err(err_invalid());
                };
                queue_waiter(&mut lock.writer_waiters, task_token);
                let can_write = lock.writer.is_none()
                    && lock.total_readers == 0
                    && lock.reader_waiters.is_empty()
                    && lock
                        .writer_waiters
                        .front()
                        .is_some_and(|front| *front == task_token);
                if can_write {
                    push_unique(&mut wake, task_token);
                }
            }
        }

        debug_assert_unique_tasks(&wake);
        Ok(wake)
    }

    fn collect_ready_waiters(&mut self, wake: &mut Vec<SyncTaskId>) {
        // This pass runs after state changes such as unlock, close, or task
        // finalization. It wakes waiters made ready by the new state while
        // preserving one wake per task token.
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
                if let Some(waiter) = front_waiter(&mutex.waiters) {
                    push_unique(wake, waiter);
                }
            }
        }

        for lock in self.rwlocks.iter_mut().flatten() {
            if lock.writer.is_none() && lock.total_readers == 0 {
                if let Some(waiter) = front_waiter(&lock.writer_waiters) {
                    push_unique(wake, waiter);
                    continue;
                }
            }

            if lock.writer.is_none() && lock.writer_waiters.is_empty() {
                extend_unique(wake, lock.reader_waiters.iter().copied());
            }
        }
    }

    fn task_finalized(&mut self, task_token: SyncTaskId) -> Vec<SyncTaskId> {
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
                let Some(&slot_id) = self.mutex_slots.get(&mutex_id) else {
                    continue;
                };
                let Some(mutex) = self.mutexes.get_mut(slot_id).and_then(Option::as_mut) else {
                    continue;
                };
                if mutex.owner == Some(task_token) {
                    // Cancelled/panicked tasks release logical ownership so the
                    // next waiter can acquire the mutex on its next poll.
                    mutex.owner = None;
                    if let Some(waiter) = front_waiter(&mutex.waiters) {
                        push_unique(&mut wake, waiter);
                    }
                }
            }

            for (lock_id, _) in owned.rw_read {
                let Some(&slot_id) = self.rwlock_slots.get(&lock_id) else {
                    continue;
                };
                let Some(lock) = self.rwlocks.get_mut(slot_id).and_then(Option::as_mut) else {
                    continue;
                };
                if let Some(count) = lock.readers.remove(&task_token) {
                    lock.total_readers = lock.total_readers.saturating_sub(count);
                    if lock.total_readers == 0 {
                        if let Some(waiter) = front_waiter(&lock.writer_waiters) {
                            push_unique(&mut wake, waiter);
                        } else {
                            extend_unique(&mut wake, lock.reader_waiters.iter().copied());
                        }
                    }
                }
            }

            for (lock_id, _) in owned.rw_write {
                let Some(&slot_id) = self.rwlock_slots.get(&lock_id) else {
                    continue;
                };
                let Some(lock) = self.rwlocks.get_mut(slot_id).and_then(Option::as_mut) else {
                    continue;
                };
                if lock.writer == Some(task_token) {
                    // Writer finalization hands off to the next writer first,
                    // then to all queued readers if no writer is waiting.
                    lock.writer = None;
                    if let Some(waiter) = front_waiter(&lock.writer_waiters) {
                        push_unique(&mut wake, waiter);
                    } else {
                        extend_unique(&mut wake, lock.reader_waiters.iter().copied());
                    }
                }
            }
        }

        self.collect_ready_waiters(&mut wake);
        self.collect_retired_locks();
        debug_assert_unique_tasks(&wake);

        wake
    }
}

fn debug_assert_unique_tasks(_tasks: &[SyncTaskId]) {
    #[cfg(debug_assertions)]
    for (index, task) in _tasks.iter().enumerate() {
        debug_assert!(
            !_tasks[index + 1..].contains(task),
            "sync wake batch contains duplicate task token"
        );
    }
}

fn capture_wakes(state: &SyncState, tokens: &[SyncTaskId]) -> Vec<TaskWake> {
    tokens
        .iter()
        .filter_map(|token| state.wake_targets.get(token).cloned())
        .collect()
}

pub(crate) fn register_wait(target: TaskWake, id: usize, kind: WaitKind) -> Result<(), i32> {
    let mut state = state_cell().lock().unwrap();
    let task_token = state.bind_task(target);
    let wake = state.register_wait(task_token, id, kind)?;
    let wake = capture_wakes(&state, &wake);
    drop(state);

    for target in wake {
        target.wake();
    }

    Ok(())
}

/// Return task-to-task dependencies for a blocked synchronization operation.
/// External state (for example a future channel sender that does not exist yet)
/// intentionally has no edge and therefore cannot be classified as a cycle.
pub(crate) fn wait_dependencies(scheduler: u64, id: usize, kind: WaitKind) -> Vec<u64> {
    let state = state_cell().lock().unwrap();
    let mut dependencies: Vec<SyncTaskId> = match kind {
        WaitKind::ChannelSend => state
            .channel(id)
            .map(|channel| channel.recv_waiters.iter().copied().collect())
            .unwrap_or_default(),
        WaitKind::ChannelRecv => state
            .channel(id)
            .map(|channel| channel.send_waiters.iter().copied().collect())
            .unwrap_or_default(),
        WaitKind::Mutex => state
            .mutex_slots
            .get(&id)
            .and_then(|slot| state.mutexes.get(*slot))
            .and_then(Option::as_ref)
            .and_then(|mutex| mutex.owner)
            .into_iter()
            .collect(),
        WaitKind::RwRead => state
            .rwlock_slots
            .get(&id)
            .and_then(|slot| state.rwlocks.get(*slot))
            .and_then(Option::as_ref)
            .and_then(|lock| lock.writer)
            .into_iter()
            .collect(),
        WaitKind::RwWrite => state
            .rwlock_slots
            .get(&id)
            .and_then(|slot| state.rwlocks.get(*slot))
            .and_then(Option::as_ref)
            .map(|lock| {
                let mut owners: Vec<_> = lock.readers.keys().copied().collect();
                owners.extend(lock.writer);
                owners
            })
            .unwrap_or_default(),
    };
    let mut dependencies: Vec<u64> = dependencies
        .drain(..)
        .filter_map(|id| state.wake_targets.get(&id))
        .filter(|target| target.identity().belongs_to(scheduler))
        .map(TaskWake::token)
        .collect();
    dependencies.sort_unstable();
    dependencies.dedup();
    dependencies
}

pub(crate) fn task_finalized(identity: TaskIdentity) {
    // Binding happens in one of the task's own polls, and its finalization is
    // ordered after them. So a task that bound can't see zero, and programs and
    // periods using no sync primitive skip the registry's global lock per task.
    if TASK_BINDINGS.load(Ordering::Acquire) == 0 {
        return;
    }
    let mut state = state_cell().lock().unwrap();
    let Some(task_token) = state.task_bindings.remove(&identity) else {
        return;
    };
    TASK_BINDINGS.fetch_sub(1, Ordering::Release);
    let wake = state.task_finalized(task_token);
    let wake = capture_wakes(&state, &wake);
    state.wake_targets.remove(&task_token);
    drop(state);

    for target in wake {
        target.wake();
    }
}

fn finish_channel_destroy(channel_id: usize) -> i32 {
    let mut state = state_cell().lock().unwrap();
    let (status, wake, queued) = state.channel_destroy(channel_id);
    let wake = capture_wakes(&state, &wake);
    drop(state);
    for target in wake {
        target.wake();
    }
    // Synchronous source destruction runs in its caller's context. Every
    // queued owner is destroyed outside the registry lock, including on panic.
    drop(queued);
    status
}

fn release_collected_handle(handle: usize) {
    unsafe { __rt__sync_handle_release(handle as *mut u8) };
}

/// Wrap a sync handle box in a collected owner; copies of the source handle
/// share it, and the box is released once no copy can reach it.
#[unsafe(no_mangle)]
pub extern "C-unwind" fn __gc__sync_owner_new(handle: *mut u8) -> *mut u8 {
    crate::garbage_collector::gc_native_new(handle, release_collected_handle)
}

/// Private oracle for tests: sync handle boxes not yet released.
#[unsafe(no_mangle)]
pub extern "C" fn __gc__test_live_sync_handles() -> usize {
    LIVE_SYNC_HANDLES.load(std::sync::atomic::Ordering::Relaxed)
}

/// Create a channel whose queued messages are rooted collected copies.
///
/// # Safety
/// element is a process-long compiler GC value descriptor of the exact
/// element type.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __gc__sync_channel_create(
    capacity: usize,
    bounded: u8,
    element: *const crate::gc_existentials::GcValueDescriptor,
) -> *mut u8 {
    let Some(layout) = (unsafe { ChannelLayout::new(element) }) else {
        return std::ptr::null_mut();
    };
    let id =
        state_cell()
            .lock()
            .unwrap()
            .channel_create_with_layout(layout, capacity, bounded != 0);
    if id == 0 {
        return std::ptr::null_mut();
    }
    let handle = allocate_handle(id, SyncHandleKind::Channel);
    if handle.is_null() {
        let _ = finish_channel_destroy(id);
    }
    handle
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__sync_channel_destroy(handle: *mut u8) -> i32 {
    let channel_id = match handle_id(handle, SyncHandleKind::Channel) {
        Ok(id) => id,
        Err(error) => return error,
    };
    // The opaque box remains live in copied source handles; only the registry
    // entry is retired. GC reclamation frees the box independently.
    finish_channel_destroy(channel_id)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_channel_close(handle: *mut u8) -> i32 {
    let channel_id = match handle_id(handle, SyncHandleKind::Channel) {
        Ok(id) => id,
        Err(error) => return error,
    };
    let mut state = state_cell().lock().unwrap();
    let (status, wake) = state.channel_close(channel_id);
    let wake = capture_wakes(&state, &wake);
    drop(state);

    for target in wake {
        target.wake();
    }

    status
}

#[unsafe(no_mangle)]
pub extern "C-unwind" fn __rt__sync_channel_try_send(handle: *mut u8, value_ptr: *const u8) -> i32 {
    let channel_id = match handle_id(handle, SyncHandleKind::Channel) {
        Ok(id) => id,
        Err(error) => return error,
    };
    let layout = {
        let state = state_cell().lock().unwrap();
        let status = state.channel_send_status(channel_id);
        if status != 0 {
            return status;
        }
        let channel = state
            .channel(channel_id)
            .expect("validated channel disappeared");
        channel.layout.clone()
    };
    let value = match unsafe { QueuedValue::prepare(&layout, value_ptr) } {
        Ok(value) => value,
        Err(error) => return error,
    };
    let mut state = state_cell().lock().unwrap();
    let (status, wake, rejected) = state.channel_try_send_value(channel_id, value);
    let wake = capture_wakes(&state, &wake);
    drop(state);

    // A raced close/full result rolls staging ownership back, without cleanup.
    drop(rejected);
    for target in wake {
        target.wake();
    }

    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_channel_try_recv(handle: *mut u8, out_ptr: *mut u8) -> i32 {
    let channel_id = match handle_id(handle, SyncHandleKind::Channel) {
        Ok(id) => id,
        Err(error) => return error,
    };
    let mut state = state_cell().lock().unwrap();
    let (status, wake, received) = state.channel_try_recv(channel_id, out_ptr);
    let wake = capture_wakes(&state, &wake);
    drop(state);

    drop(received);
    for target in wake {
        target.wake();
    }

    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_mutex_create() -> *mut u8 {
    let id = state_cell().lock().unwrap().mutex_create();
    if id == 0 {
        return std::ptr::null_mut();
    }
    let handle = allocate_handle(id, SyncHandleKind::Mutex);
    if handle.is_null() {
        let _ = state_cell().lock().unwrap().mutex_destroy(id);
    }
    handle
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_mutex_destroy(handle: *mut u8) -> i32 {
    let mutex_id = match handle_id(handle, SyncHandleKind::Mutex) {
        Ok(id) => id,
        Err(error) => return error,
    };
    let status = state_cell().lock().unwrap().mutex_destroy(mutex_id);
    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_mutex_try_lock(handle: *mut u8) -> i32 {
    let mutex_id = match handle_id(handle, SyncHandleKind::Mutex) {
        Ok(id) => id,
        Err(error) => return error,
    };
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    state_cell()
        .lock()
        .unwrap()
        .mutex_try_lock(mutex_id, task_token)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_mutex_unlock(handle: *mut u8) -> i32 {
    let mutex_id = match handle_id(handle, SyncHandleKind::Mutex) {
        Ok(id) => id,
        Err(error) => return error,
    };
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    let mut state = state_cell().lock().unwrap();
    let (status, wake) = state.mutex_unlock(mutex_id, task_token);
    let wake = capture_wakes(&state, &wake);
    drop(state);

    for target in wake {
        target.wake();
    }

    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_create() -> *mut u8 {
    let id = state_cell().lock().unwrap().rwlock_create();
    if id == 0 {
        return std::ptr::null_mut();
    }
    let handle = allocate_handle(id, SyncHandleKind::RwLock);
    if handle.is_null() {
        let _ = state_cell().lock().unwrap().rwlock_destroy(id);
    }
    handle
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_destroy(handle: *mut u8) -> i32 {
    let lock_id = match handle_id(handle, SyncHandleKind::RwLock) {
        Ok(id) => id,
        Err(error) => return error,
    };
    let status = state_cell().lock().unwrap().rwlock_destroy(lock_id);
    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_try_read(handle: *mut u8) -> i32 {
    let lock_id = match handle_id(handle, SyncHandleKind::RwLock) {
        Ok(id) => id,
        Err(error) => return error,
    };
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    state_cell()
        .lock()
        .unwrap()
        .rwlock_try_read(lock_id, task_token)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_try_write(handle: *mut u8) -> i32 {
    let lock_id = match handle_id(handle, SyncHandleKind::RwLock) {
        Ok(id) => id,
        Err(error) => return error,
    };
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    state_cell()
        .lock()
        .unwrap()
        .rwlock_try_write(lock_id, task_token)
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_unlock_read(handle: *mut u8) -> i32 {
    let lock_id = match handle_id(handle, SyncHandleKind::RwLock) {
        Ok(id) => id,
        Err(error) => return error,
    };
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    let mut state = state_cell().lock().unwrap();
    let (status, wake) = state.rwlock_unlock_read(lock_id, task_token);
    let wake = capture_wakes(&state, &wake);
    drop(state);

    for target in wake {
        target.wake();
    }

    status
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__sync_rwlock_unlock_write(handle: *mut u8) -> i32 {
    let lock_id = match handle_id(handle, SyncHandleKind::RwLock) {
        Ok(id) => id,
        Err(error) => return error,
    };
    let task_token = match current_task_token() {
        Ok(task) => task,
        Err(err) => return err,
    };

    let mut state = state_cell().lock().unwrap();
    let (status, wake) = state.rwlock_unlock_write(lock_id, task_token);
    let wake = capture_wakes(&state, &wake);
    drop(state);

    for target in wake {
        target.wake();
    }

    status
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_u32_channel(state: &mut SyncState, capacity: usize) -> usize {
        let layout = unsafe { ChannelLayout::new(crate::test_layout::value::<u32>()) }.unwrap();
        state.channel_create_with_layout(layout, capacity, true)
    }

    #[test]
    fn retired_native_locks_follow_the_remaining_task_ownership_lease() {
        let mut state = SyncState::default();
        let mutex = state.mutex_create();
        assert_eq!(state.mutex_try_lock(mutex, 71), 0);
        state.retire_mutex(mutex);
        assert!(state.retired_mutexes.contains(&mutex));
        assert!(state.mutex_slots.contains_key(&mutex));
        state.task_finalized(71);
        assert!(!state.mutex_slots.contains_key(&mutex));
        assert!(state.retired_mutexes.is_empty());

        let reader = state.rwlock_create();
        assert_eq!(state.rwlock_try_read(reader, 72), 0);
        state.retire_rwlock(reader);
        assert!(state.retired_rwlocks.contains(&reader));
        state.task_finalized(72);
        assert!(!state.rwlock_slots.contains_key(&reader));
        assert!(state.retired_rwlocks.is_empty());

        let writer = state.rwlock_create();
        assert_eq!(state.rwlock_try_write(writer, 73), 0);
        state.retire_rwlock(writer);
        state.task_finalized(73);
        assert!(!state.rwlock_slots.contains_key(&writer));
        assert!(state.retired_rwlocks.is_empty());
    }

    #[test]
    fn explicit_native_destroy_keeps_the_opaque_box_live_until_final_release() {
        let id = state_cell().lock().unwrap().mutex_create();
        let handle = allocate_handle(id, SyncHandleKind::Mutex);
        assert_eq!(__rt__sync_mutex_destroy(handle), 0);
        assert_eq!(handle_id(handle, SyncHandleKind::Mutex), Ok(id));
        assert_eq!(__rt__sync_mutex_destroy(handle), err_invalid());
        // No reclaimer can subsequently retire a reused registry slot.
        unsafe { __rt__sync_handle_release(handle) };
        assert!(!state_cell().lock().unwrap().mutex_slots.contains_key(&id));
    }

    #[test]
    fn stale_channel_identity_cannot_target_reused_storage() {
        let mut state = SyncState::default();
        let old = create_u32_channel(&mut state, 1);
        drop(state.channel_destroy(old));
        let replacement = create_u32_channel(&mut state, 1);
        let value = 37_u32;
        let (status, _) = state.channel_try_send(old, (&value as *const u32).cast());
        assert_eq!(
            status,
            err_invalid(),
            "an old operation cannot enqueue into a replacement channel"
        );
        let mut output = 0_u32;
        assert_eq!(
            state
                .channel_try_recv(replacement, (&mut output as *mut u32).cast())
                .0,
            err_would_block()
        );
    }

    #[test]
    fn staged_messages_cannot_commit_after_destroy_and_identity_exhaustion_never_wraps() {
        let mut state = SyncState::default();
        let old = create_u32_channel(&mut state, 1);
        let layout = state.channel(old).unwrap().layout.clone();
        let value = 41_u32;
        let staged =
            unsafe { QueuedValue::prepare(&layout, (&value as *const u32).cast()) }.unwrap();
        drop(state.channel_destroy(old));
        let replacement = create_u32_channel(&mut state, 1);
        let (status, _, rejected) = state.channel_try_send_value(old, staged);
        assert_eq!(status, err_invalid());
        drop(rejected);
        assert!(state.channel(replacement).unwrap().queue.is_empty());
        state.next_channel_id = usize::MAX;
        assert_eq!(create_u32_channel(&mut state, 1), 0);
        assert_eq!(state.next_channel_id, usize::MAX);
    }

    #[test]
    fn bounded_channel_close_and_drain() {
        let mut state = SyncState::default();
        let id = create_u32_channel(&mut state, 1);
        assert_ne!(id, 0);

        let value = 7u32.to_ne_bytes();
        let (send_status, _) = state.channel_try_send(id, value.as_ptr());
        assert_eq!(send_status, 0);

        let second = 9u32.to_ne_bytes();
        let (blocked_status, _) = state.channel_try_send(id, second.as_ptr());
        assert_eq!(blocked_status, err_would_block());

        let mut out = [0u8; 4];
        let (recv_status, _, _) = state.channel_try_recv(id, out.as_mut_ptr());
        assert_eq!(recv_status, 0);
        assert_eq!(u32::from_ne_bytes(out), 7);

        let (close_status, _) = state.channel_close(id);
        assert_eq!(close_status, 0);

        let (closed_recv, _, _) = state.channel_try_recv(id, out.as_mut_ptr());
        assert_eq!(closed_recv, err_closed());
    }

    #[test]
    fn channel_try_recv_invalid_pointer_keeps_queued_value() {
        let mut state = SyncState::default();
        let id = create_u32_channel(&mut state, 1);
        assert_ne!(id, 0);

        let value = 27u32.to_ne_bytes();
        let (send_status, _) = state.channel_try_send(id, value.as_ptr());
        assert_eq!(send_status, 0);

        let (invalid_status, _, _) = state.channel_try_recv(id, std::ptr::null_mut());
        assert_eq!(invalid_status, libc::EINVAL);

        let mut out = [0u8; 4];
        let (recv_status, _, _) = state.channel_try_recv(id, out.as_mut_ptr());
        assert_eq!(recv_status, 0);
        assert_eq!(u32::from_ne_bytes(out), 27);
    }

    #[test]
    fn destroyed_sync_slots_are_reused() {
        let mut state = SyncState::default();

        let channel_id = create_u32_channel(&mut state, 1);
        let old_slot = state.channel_slots[&channel_id];
        assert_eq!(state.channel_destroy(channel_id).0, 0);
        let replacement = create_u32_channel(&mut state, 1);
        assert_ne!(replacement, channel_id);
        assert_eq!(state.channel_slots[&replacement], old_slot);

        let mutex_id = state.mutex_create();
        let old_slot = state.mutex_slots[&mutex_id];
        assert_eq!(state.mutex_destroy(mutex_id), 0);
        let replacement = state.mutex_create();
        assert_ne!(replacement, mutex_id);
        assert_eq!(state.mutex_slots[&replacement], old_slot);

        let rwlock_id = state.rwlock_create();
        let old_slot = state.rwlock_slots[&rwlock_id];
        assert_eq!(state.rwlock_destroy(rwlock_id), 0);
        let replacement = state.rwlock_create();
        assert_ne!(replacement, rwlock_id);
        assert_eq!(state.rwlock_slots[&replacement], old_slot);
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
    fn mutex_woken_waiter_reserves_turn_against_new_lockers() {
        let mut state = SyncState::default();
        let id = state.mutex_create();
        assert_eq!(state.mutex_try_lock(id, 1), 0);
        let _ = state.register_wait(2, id, WaitKind::Mutex).unwrap();

        let (unlock_status, wake) = state.mutex_unlock(id, 1);
        assert_eq!(unlock_status, 0);
        assert_eq!(wake, vec![2]);
        assert_eq!(state.mutex_try_lock(id, 3), err_busy());
        assert_eq!(state.mutex_try_lock(id, 2), 0);
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
        assert_eq!(state.rwlock_try_read(id, 3), err_busy());
        assert_eq!(state.rwlock_try_write(id, 2), 0);
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
    fn task_finalization_removes_channel_waiters() {
        let mut state = SyncState::default();

        let send_id = create_u32_channel(&mut state, 1);
        let value = 7u32.to_ne_bytes();
        let (send_status, _) = state.channel_try_send(send_id, value.as_ptr());
        assert_eq!(send_status, 0);
        assert!(
            state
                .register_wait(44, send_id, WaitKind::ChannelSend)
                .unwrap()
                .is_empty()
        );

        let recv_id = create_u32_channel(&mut state, 1);
        assert!(
            state
                .register_wait(44, recv_id, WaitKind::ChannelRecv)
                .unwrap()
                .is_empty()
        );

        let wake = state.task_finalized(44);
        assert!(wake.is_empty());

        let send_channel = state.channel(send_id).unwrap();
        assert!(!send_channel.send_waiters.contains(&44));
        let recv_channel = state.channel(recv_id).unwrap();
        assert!(!recv_channel.recv_waiters.contains(&44));
    }

    #[test]
    fn channel_close_wakes_unique_waiters() {
        let mut state = SyncState::default();
        let id = create_u32_channel(&mut state, 1);
        {
            let channel = state.channel_mut(id).unwrap();
            queue_waiter(&mut channel.send_waiters, 7);
            queue_waiter(&mut channel.send_waiters, 11);
            queue_waiter(&mut channel.recv_waiters, 7);
        }

        let (status, wake) = state.channel_close(id);
        assert_eq!(status, 0);
        assert_eq!(wake, vec![7, 11]);
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
    fn task_finalization_releases_rwlock_writer_and_wakes_readers() {
        let mut state = SyncState::default();
        let id = state.rwlock_create();
        assert_eq!(state.rwlock_try_write(id, 1), 0);
        assert!(
            state
                .register_wait(2, id, WaitKind::RwRead)
                .unwrap()
                .is_empty()
        );
        assert!(
            state
                .register_wait(3, id, WaitKind::RwRead)
                .unwrap()
                .is_empty()
        );

        let wake = state.task_finalized(1);
        assert_eq!(wake, vec![2, 3]);

        let lock = state.rwlocks[state.rwlock_slots[&id]].as_ref().unwrap();
        assert_eq!(lock.writer, None);
        assert!(lock.reader_waiters.contains(&2));
        assert!(lock.reader_waiters.contains(&3));

        assert_eq!(state.rwlock_try_read(id, 2), 0);
        assert_eq!(state.rwlock_try_read(id, 3), 0);
        let lock = state.rwlocks[state.rwlock_slots[&id]].as_ref().unwrap();
        assert!(lock.reader_waiters.is_empty());
    }

    #[test]
    fn task_finalization_releases_rwlock_readers_and_wakes_writer() {
        let mut state = SyncState::default();
        let id = state.rwlock_create();
        assert_eq!(state.rwlock_try_read(id, 1), 0);
        assert_eq!(state.rwlock_try_read(id, 2), 0);
        assert!(
            state
                .register_wait(3, id, WaitKind::RwWrite)
                .unwrap()
                .is_empty()
        );

        let first_wake = state.task_finalized(1);
        assert!(first_wake.is_empty());

        let second_wake = state.task_finalized(2);
        assert_eq!(second_wake, vec![3]);

        let lock = state.rwlocks[state.rwlock_slots[&id]].as_ref().unwrap();
        assert_eq!(lock.total_readers, 0);
        assert!(lock.writer_waiters.contains(&3));

        assert_eq!(state.rwlock_try_write(id, 3), 0);
        let lock = state.rwlocks[state.rwlock_slots[&id]].as_ref().unwrap();
        assert!(lock.writer_waiters.is_empty());
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
