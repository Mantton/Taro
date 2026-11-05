//! Opaque synchronization identities must never alias replacement registry slots.
use super::*;

#[test]
fn stale_mutex_operations_cannot_access_or_destroy_a_replacement() {
    let mut state = SyncState::default();
    let old = state.mutex_create();
    assert_eq!(state.mutex_destroy(old), 0);
    let replacement = state.mutex_create();
    assert_eq!(state.mutex_try_lock(old, 41), err_invalid());
    assert_eq!(state.mutex_unlock(old, 41).0, err_invalid());
    assert_eq!(
        state.register_wait(41, old, WaitKind::Mutex),
        Err(err_invalid())
    );
    assert_eq!(state.mutex_destroy(old), err_invalid());
    assert_eq!(state.mutex_try_lock(replacement, 42), 0);
    assert_eq!(state.mutex_unlock(replacement, 42).0, 0);
    assert_eq!(state.mutex_destroy(replacement), 0);
}

#[test]
fn stale_rwlock_operations_cannot_access_or_destroy_a_replacement() {
    let mut state = SyncState::default();
    let old = state.rwlock_create();
    assert_eq!(state.rwlock_destroy(old), 0);
    let replacement = state.rwlock_create();
    assert_eq!(state.rwlock_try_read(old, 41), err_invalid());
    assert_eq!(state.rwlock_try_write(old, 41), err_invalid());
    assert_eq!(state.rwlock_unlock_read(old, 41).0, err_invalid());
    assert_eq!(state.rwlock_unlock_write(old, 41).0, err_invalid());
    assert_eq!(
        state.register_wait(41, old, WaitKind::RwRead),
        Err(err_invalid())
    );
    assert_eq!(
        state.register_wait(41, old, WaitKind::RwWrite),
        Err(err_invalid())
    );
    assert_eq!(state.rwlock_destroy(old), err_invalid());
    assert_eq!(state.rwlock_try_write(replacement, 42), 0);
    assert_eq!(state.rwlock_unlock_write(replacement, 42).0, 0);
    assert_eq!(state.rwlock_destroy(replacement), 0);
}

#[test]
fn lock_identity_exhaustion_preserves_existing_owners_and_registry_storage() {
    let mut state = SyncState::default();
    let mutex = state.mutex_create();
    let rwlock = state.rwlock_create();
    let mutex_slots = state.mutexes.len();
    let rwlock_slots = state.rwlocks.len();
    state.next_mutex_id = usize::MAX;
    state.next_rwlock_id = usize::MAX;
    for _ in 0..2 {
        assert_eq!(state.mutex_create(), 0);
        assert_eq!(state.rwlock_create(), 0);
    }
    assert_eq!(state.mutexes.len(), mutex_slots);
    assert_eq!(state.rwlocks.len(), rwlock_slots);
    assert_eq!(state.next_mutex_id, usize::MAX);
    assert_eq!(state.next_rwlock_id, usize::MAX);
    assert_eq!(state.mutex_try_lock(mutex, 19), 0);
    assert_eq!(state.rwlock_try_write(rwlock, 19), 0);
    assert_eq!(state.mutex_destroy(mutex), err_busy());
    assert_eq!(state.rwlock_destroy(rwlock), err_busy());
    assert_eq!(state.mutex_unlock(mutex, 19).0, 0);
    assert_eq!(state.rwlock_unlock_write(rwlock, 19).0, 0);
    assert_eq!(state.mutex_destroy(mutex), 0);
    assert_eq!(state.rwlock_destroy(rwlock), 0);
}

#[test]
fn busy_destroy_keeps_the_identity_and_task_finalization_wakes_the_right_waiter() {
    let mut state = SyncState::default();
    // Force slot and identity to differ before exercising every ownership path.
    let old_mutex = state.mutex_create();
    let old_rwlock = state.rwlock_create();
    assert_eq!(state.mutex_destroy(old_mutex), 0);
    assert_eq!(state.rwlock_destroy(old_rwlock), 0);
    let mutex = state.mutex_create();
    let rwlock = state.rwlock_create();
    assert_eq!(state.mutex_try_lock(mutex, 17), 0);
    assert_eq!(state.rwlock_try_read(rwlock, 17), 0);
    assert!(
        state
            .register_wait(18, mutex, WaitKind::Mutex)
            .unwrap()
            .is_empty()
    );
    assert!(
        state
            .register_wait(18, rwlock, WaitKind::RwWrite)
            .unwrap()
            .is_empty()
    );
    assert_eq!(state.mutex_destroy(mutex), err_busy());
    assert_eq!(state.rwlock_destroy(rwlock), err_busy());
    assert_eq!(state.task_finalized(17), vec![18]);
    assert_eq!(state.mutex_try_lock(mutex, 18), 0);
    assert_eq!(state.rwlock_try_write(rwlock, 18), 0);
    assert_eq!(state.mutex_unlock(mutex, 18).0, 0);
    assert_eq!(state.rwlock_unlock_write(rwlock, 18).0, 0);
    assert_eq!(state.mutex_destroy(mutex), 0);
    assert_eq!(state.rwlock_destroy(rwlock), 0);
}
