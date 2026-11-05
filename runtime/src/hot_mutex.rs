//! A mutex for short critical sections that every task poll or socket call takes.
//!
//! On Apple platforms `std::sync::Mutex` wraps a separately allocated pthread
//! mutex, so each new one costs an allocation and each lock a slow path of
//! checks. Even `os_unfair_lock` costs two calls through dyld stubs, for sections
//! taken dozens of times per request. This is one byte, with both directions
//! inlined. A waiter spins briefly and then yields, which suits only sections
//! that never block; every user here holds it for a few fields or one map entry.
//! The rest of the contract matches std, including poisoning; elsewhere std's
//! own futex mutex already behaves like this and is used directly.

#[cfg(not(target_vendor = "apple"))]
pub(crate) use std::sync::{Mutex as HotMutex, MutexGuard as HotMutexGuard};

#[cfg(target_vendor = "apple")]
pub(crate) use apple::{HotMutex, HotMutexGuard};

#[cfg(target_vendor = "apple")]
mod apple {
    use std::cell::UnsafeCell;
    use std::ops::{Deref, DerefMut};
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{LockResult, PoisonError};

    pub(crate) struct HotMutex<T: ?Sized> {
        locked: AtomicBool,
        poisoned: AtomicBool,
        value: UnsafeCell<T>,
    }
    // As for std's Mutex: the lock serializes every access to the value.
    unsafe impl<T: ?Sized + Send> Send for HotMutex<T> {}
    unsafe impl<T: ?Sized + Send> Sync for HotMutex<T> {}

    pub(crate) struct HotMutexGuard<'a, T: ?Sized> {
        mutex: &'a HotMutex<T>,
        panicking_at_lock: bool,
        // The lock must be released by the thread that took it.
        _not_send: std::marker::PhantomData<*mut ()>,
    }

    impl<T> HotMutex<T> {
        pub(crate) const fn new(value: T) -> Self {
            Self {
                locked: AtomicBool::new(false),
                poisoned: AtomicBool::new(false),
                value: UnsafeCell::new(value),
            }
        }
    }

    impl<T: ?Sized> HotMutex<T> {
        #[inline]
        pub(crate) fn lock(&self) -> LockResult<HotMutexGuard<'_, T>> {
            if self
                .locked
                .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_err()
            {
                self.lock_contended();
            }
            let guard = HotMutexGuard {
                mutex: self,
                panicking_at_lock: std::thread::panicking(),
                _not_send: std::marker::PhantomData,
            };
            if self.poisoned.load(Ordering::Relaxed) {
                Err(PoisonError::new(guard))
            } else {
                Ok(guard)
            }
        }

        #[cold]
        #[inline(never)]
        fn lock_contended(&self) {
            const SPINS: u32 = 64;
            let mut attempts = 0;
            loop {
                if !self.locked.load(Ordering::Relaxed)
                    && self
                        .locked
                        .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
                        .is_ok()
                {
                    return;
                }
                attempts += 1;
                if attempts < SPINS {
                    std::hint::spin_loop();
                } else {
                    // The holder may not have a CPU.
                    std::thread::yield_now();
                }
            }
        }

        pub(crate) fn clear_poison(&self) {
            self.poisoned.store(false, Ordering::Relaxed);
        }
    }

    impl<T: ?Sized> Deref for HotMutexGuard<'_, T> {
        type Target = T;
        #[inline]
        fn deref(&self) -> &T {
            unsafe { &*self.mutex.value.get() }
        }
    }
    impl<T: ?Sized> DerefMut for HotMutexGuard<'_, T> {
        #[inline]
        fn deref_mut(&mut self) -> &mut T {
            unsafe { &mut *self.mutex.value.get() }
        }
    }
    impl<T: ?Sized> Drop for HotMutexGuard<'_, T> {
        #[inline]
        fn drop(&mut self) {
            if !self.panicking_at_lock && std::thread::panicking() {
                self.mutex.poisoned.store(true, Ordering::Relaxed);
            }
            self.mutex.locked.store(false, Ordering::Release);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::HotMutex;
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn serializes_writers() {
        let mutex = Arc::new(HotMutex::new(0usize));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let mutex = Arc::clone(&mutex);
                std::thread::spawn(move || {
                    for _ in 0..20_000 {
                        *mutex.lock().unwrap() += 1;
                    }
                })
            })
            .collect();
        for thread in threads {
            thread.join().unwrap();
        }
        assert_eq!(*mutex.lock().unwrap(), 160_000);
    }

    #[test]
    fn a_panic_under_the_lock_poisons_it_until_cleared() {
        let mutex = Arc::new(HotMutex::new(7usize));
        let holder = Arc::clone(&mutex);
        assert!(
            std::thread::spawn(move || {
                let _guard = holder.lock().unwrap();
                panic!("expected panic under the lock");
            })
            .join()
            .is_err()
        );
        let poisoned = mutex.lock();
        assert!(poisoned.is_err());
        assert_eq!(
            *poisoned.unwrap_or_else(std::sync::PoisonError::into_inner),
            7
        );
        mutex.clear_poison();
        assert!(mutex.lock().is_ok());
    }

    #[test]
    fn locking_while_already_unwinding_does_not_poison() {
        static LOCKS: AtomicUsize = AtomicUsize::new(0);
        static MUTEX: HotMutex<()> = HotMutex::new(());
        struct LockOnDrop;
        impl Drop for LockOnDrop {
            fn drop(&mut self) {
                let _guard = MUTEX.lock().unwrap();
                LOCKS.fetch_add(1, Ordering::Relaxed);
            }
        }
        assert!(
            std::thread::spawn(|| {
                let _lock = LockOnDrop;
                panic!("expected panic before the lock");
            })
            .join()
            .is_err()
        );
        assert_eq!(LOCKS.load(Ordering::Relaxed), 1);
        assert!(MUTEX.lock().is_ok());
    }
}
