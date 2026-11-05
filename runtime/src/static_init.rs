//! Synchronous lazy-initialization admission, independent of value storage.
//!
//! One caller claims the gate and runs the initializer; the others wait for its
//! outcome parked at a GC safepoint, so a collection started by the initializer
//! never waits on them. Failed callbacks are never retried; a short-held graph
//! lock detects recursive and cross-thread initialization cycles before a
//! caller could block. No initializer or owned callback is dropped while a
//! mutator is parked or while the graph lock is held. Source static
//! storage/access guards and panic diagnostics are separate integration work.
use std::{
    collections::{HashMap, HashSet},
    sync::{
        Condvar, Mutex, OnceLock,
        atomic::{AtomicU8, AtomicU64, Ordering},
    },
    thread::ThreadId,
};

mod abi;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct InitId(u64);
static NEXT_ID: AtomicU64 = AtomicU64::new(1);
const UNINITIALIZED: u8 = 0;
const INITIALIZING: u8 = 1;
const READY: u8 = 2;
const FAILED: u8 = 3;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum InitError {
    Cycle,
    PreviouslyFailed,
}

#[derive(Default)]
struct Graph {
    owners: HashMap<InitId, ThreadId>,
    waiting: HashMap<ThreadId, InitId>,
}
fn graph() -> &'static Mutex<Graph> {
    static GRAPH: OnceLock<Mutex<Graph>> = OnceLock::new();
    GRAPH.get_or_init(Mutex::default)
}
struct Wait {
    thread: ThreadId,
    target: InitId,
}
impl Wait {
    fn begin(target: InitId) -> Result<Self, InitError> {
        let thread = std::thread::current().id();
        let mut graph = graph()
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        graph.waiting.insert(thread, target);
        let mut cursor = target;
        let mut seen = HashSet::new();
        while let Some(&owner) = graph.owners.get(&cursor) {
            if owner == thread || !seen.insert(cursor) {
                graph.waiting.remove(&thread);
                return Err(InitError::Cycle);
            }
            let Some(&next) = graph.waiting.get(&owner) else {
                break;
            };
            cursor = next;
        }
        Ok(Self { thread, target })
    }
}
impl Drop for Wait {
    fn drop(&mut self) {
        let mut graph = graph()
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if graph.waiting.get(&self.thread) == Some(&self.target) {
            graph.waiting.remove(&self.thread);
        }
    }
}
struct Owner<'a> {
    gate: &'a InitGate,
    complete: bool,
}
impl<'a> Owner<'a> {
    /// Claim an uninitialized gate. Claiming and owner registration share the
    /// graph lock, so a waiter's cycle walk never sees a claimed gate without
    /// its owner.
    fn claim(gate: &'a InitGate) -> Option<Self> {
        let thread = std::thread::current().id();
        let mut graph = graph()
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if gate
            .state
            .compare_exchange(
                UNINITIALIZED,
                INITIALIZING,
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .is_err()
        {
            return None;
        }
        // This thread is no longer a waiter. One thread may own multiple
        // gates while synchronously initializing dependencies.
        graph.waiting.remove(&thread);
        graph.owners.insert(gate.id, thread);
        Some(Self {
            gate,
            complete: false,
        })
    }
}
impl Drop for Owner<'_> {
    fn drop(&mut self) {
        if !self.complete {
            self.gate.state.store(FAILED, Ordering::Release);
        }
        graph()
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .owners
            .remove(&self.gate.id);
        // Waiters re-check the state under this lock, so none misses the wake.
        let _published = self
            .gate
            .published
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        self.gate.settled.notify_all();
    }
}

/// Controls publication only; the caller supplies stable storage and owns
/// initialized-value cleanup on failed construction. Successful statics retain
/// their initialized value until explicit replacement or process termination.
pub(crate) struct InitGate {
    id: InitId,
    state: AtomicU8,
    published: Mutex<()>,
    settled: Condvar,
}
impl InitGate {
    pub(crate) fn new() -> Self {
        let id = NEXT_ID
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .expect("static initialization identity exhausted");
        Self {
            id: InitId(id),
            state: AtomicU8::new(UNINITIALIZED),
            published: Mutex::new(()),
            settled: Condvar::new(),
        }
    }

    pub(crate) fn ensure(
        &self,
        initialize: impl FnOnce() -> Result<(), InitError>,
    ) -> Result<(), InitError> {
        match self.state.load(Ordering::Acquire) {
            READY => return Ok(()),
            FAILED => return Err(InitError::PreviouslyFailed),
            _ => {}
        }
        let _wait = Wait::begin(self.id)?;
        if let Some(mut owner) = Owner::claim(self) {
            let outcome = initialize();
            self.state.store(
                if outcome.is_ok() { READY } else { FAILED },
                Ordering::Release,
            );
            owner.complete = true;
            return outcome;
        }
        // The owner may collect while initializing: wait parked so that
        // collection never waits on this thread. The unused callback is
        // dropped only after the mutator has resumed.
        crate::garbage_collector::idle_wait(|| {
            let mut published = self
                .published
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            while self.state.load(Ordering::Acquire) == INITIALIZING {
                published = self
                    .settled
                    .wait(published)
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
            }
        });
        drop(initialize);
        match self.state.load(Ordering::Acquire) {
            READY => Ok(()),
            _ => Err(InitError::PreviouslyFailed),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        sync::{Arc, Barrier, atomic::AtomicUsize, mpsc},
        time::Duration,
    };

    #[test]
    fn one_publisher_wins_and_ready_access_never_runs_another_initializer() {
        let gate = Arc::new(InitGate::new());
        let count = Arc::new(AtomicUsize::new(0));
        let value = Arc::new(AtomicUsize::new(0));
        let start = Arc::new(Barrier::new(8));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let (gate, count, value, start) =
                    (gate.clone(), count.clone(), value.clone(), start.clone());
                std::thread::spawn(move || {
                    start.wait();
                    gate.ensure(|| {
                        count.fetch_add(1, Ordering::Relaxed);
                        value.store(41, Ordering::Relaxed);
                        Ok(())
                    })
                    .unwrap();
                    assert_eq!(value.load(Ordering::Relaxed), 41);
                })
            })
            .collect();
        for thread in threads {
            thread.join().unwrap();
        }
        assert_eq!(count.load(Ordering::Relaxed), 1);
        gate.ensure(|| panic!("a ready initializer cannot run again"))
            .unwrap();
    }

    #[test]
    fn a_panicking_initializer_stays_failed_and_clears_ownership() {
        let gate = InitGate::new();
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                || gate.ensure(|| panic!("initializer failed"))
            ))
            .is_err()
        );
        assert_eq!(
            gate.ensure(|| panic!("must not retry")),
            Err(InitError::PreviouslyFailed)
        );
        InitGate::new().ensure(|| Ok(())).unwrap();
    }

    #[test]
    fn returned_failure_is_permanent_without_poison_retry() {
        let gate = InitGate::new();
        assert_eq!(
            gate.ensure(|| Err(InitError::PreviouslyFailed)),
            Err(InitError::PreviouslyFailed)
        );
        assert_eq!(
            gate.ensure(|| panic!("must not retry")),
            Err(InitError::PreviouslyFailed)
        );
    }

    #[test]
    fn recursive_and_nested_cycles_fail_without_entering_once_wait() {
        let first = InitGate::new();
        assert_eq!(
            first.ensure(|| first.ensure(|| Ok(()))),
            Err(InitError::Cycle)
        );
        let (first, second) = (InitGate::new(), InitGate::new());
        assert_eq!(
            first.ensure(|| second.ensure(|| first.ensure(|| Ok(())))),
            Err(InitError::Cycle)
        );
        assert_eq!(first.ensure(|| Ok(())), Err(InitError::PreviouslyFailed));
        assert_eq!(second.ensure(|| Ok(())), Err(InitError::PreviouslyFailed));
    }

    #[test]
    fn ordinary_dependencies_can_initialize_on_the_same_thread() {
        let (first, second) = (InitGate::new(), InitGate::new());
        first.ensure(|| second.ensure(|| Ok(()))).unwrap();
        second.ensure(|| panic!("already initialized")).unwrap();
    }

    #[test]
    fn cross_thread_cycle_wakes_both_failed_initializers() {
        let (first, second) = (Arc::new(InitGate::new()), Arc::new(InitGate::new()));
        let entered = Arc::new(Barrier::new(2));
        let (send, receive) = mpsc::channel();
        let threads: Vec<_> = [(first.clone(), second.clone()), (second, first)]
            .into_iter()
            .map(|(owner, dependency)| {
                let (entered, send) = (entered.clone(), send.clone());
                std::thread::spawn(move || {
                    let result = owner.ensure(|| {
                        entered.wait();
                        dependency.ensure(|| Ok(()))
                    });
                    send.send(result).unwrap();
                })
            })
            .collect();
        let results = [
            receive
                .recv_timeout(Duration::from_secs(5))
                .expect("first initializer deadlocked"),
            receive
                .recv_timeout(Duration::from_secs(5))
                .expect("second initializer deadlocked"),
        ];
        assert!(results.contains(&Err(InitError::Cycle)));
        assert!(results.iter().all(Result::is_err));
        for thread in threads {
            thread.join().unwrap();
        }
    }

    #[test]
    fn a_waiter_observes_failure_without_retrying_a_poisoned_initializer() {
        let gate = Arc::new(InitGate::new());
        let (entered_send, entered) = mpsc::channel();
        let (release, released) = mpsc::channel();
        let owner_gate = gate.clone();
        let owner = std::thread::spawn(move || {
            std::panic::catch_unwind(|| {
                owner_gate.ensure(|| {
                    entered_send.send(()).unwrap();
                    released.recv().unwrap();
                    panic!("initialization failed while another thread waited");
                })
            })
            .is_err()
        });
        entered.recv_timeout(Duration::from_secs(5)).unwrap();
        let waiter_gate = gate.clone();
        let waiter = std::thread::spawn(move || {
            waiter_gate.ensure(|| panic!("a waiting thread must not retry"))
        });
        let deadline = std::time::Instant::now() + Duration::from_secs(5);
        // Observe the actual wait edge, rather than depending on scheduling or
        // sleeping before releasing the initializer's deterministic barrier.
        while !graph()
            .lock()
            .unwrap()
            .waiting
            .values()
            .any(|id| *id == gate.id)
        {
            assert!(std::time::Instant::now() < deadline, "waiter never entered");
            std::thread::yield_now();
        }
        release.send(()).unwrap();
        assert!(owner.join().unwrap());
        assert_eq!(waiter.join().unwrap(), Err(InitError::PreviouslyFailed));
    }
}
