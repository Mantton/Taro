//! Marking on several threads during a collection's pause.
//!
//! Every mutator is parked, so the heap's structure can't change: workers only read
//! it and set mark bits. Helpers are native threads that never touch mutator state.
//! The thread running the collection is always one of the workers and never waits
//! for a helper to wake. It does wait for one that took work, so on an oversubscribed
//! machine a helper preempted mid-batch can lengthen a pause.

use super::{Gc, MarkStack};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Condvar, LazyLock, Mutex};

/// Below this many objects, waking helpers costs about what they would save.
const MIN_OBJECTS: usize = 16 << 10;
const MAX_THREADS: usize = 8;
/// How often a worker checks whether another is short of work.
const SHARE_CHECK_INTERVAL: usize = 64;
/// A smaller stack isn't worth the lock it takes to share.
const MIN_SHARED_STACK: usize = 128;
// Marking walks its own stack, and layouts recurse only to a bounded depth.
const HELPER_STACK_BYTES: usize = 256 << 10;

/// How many threads should mark, given how many objects the last collection
/// marked and how many threads the program itself runs on.
pub(super) fn thread_count(last_marked_objects: usize, mutators: usize) -> usize {
    static AVAILABLE: LazyLock<usize> = LazyLock::new(|| {
        std::thread::available_parallelism().map_or(1, std::num::NonZero::get)
    });
    if last_marked_objects < MIN_OBJECTS {
        return 1;
    }
    mutators.min(*AVAILABLE).clamp(1, MAX_THREADS)
}

/// Work that any worker may take, and when all of it is finished.
struct Pool {
    batches: Mutex<Vec<MarkStack>>,
    available: AtomicUsize,
    /// Workers holding no work, counting helpers that haven't arrived yet.
    idle: AtomicUsize,
    workers: usize,
    marked: AtomicUsize,
}

impl Pool {
    fn new(helpers: usize) -> Self {
        Self {
            batches: Mutex::new(Vec::new()),
            available: AtomicUsize::new(0),
            idle: AtomicUsize::new(helpers),
            workers: helpers + 1,
            marked: AtomicUsize::new(0),
        }
    }

    fn share(&self, stack: &mut MarkStack) {
        let batch = stack.split_off(stack.len() / 2);
        let mut batches = self.batches.lock().unwrap();
        batches.push(batch);
        self.available.store(batches.len(), Ordering::Release);
    }

    /// For a worker counted as idle: its next work, or `None` once there is no more.
    ///
    /// Shared work is published before its giver can become idle, and a worker stops
    /// being idle before the work it takes stops being available. So seeing every
    /// worker idle and then nothing available means nothing is left, except what a
    /// worker took in between, which that worker finishes itself.
    fn next_batch(&self) -> Option<MarkStack> {
        let mut waits = 0_u32;
        loop {
            if self.available.load(Ordering::Acquire) > 0 {
                let mut batches = self.batches.lock().unwrap();
                if let Some(batch) = batches.pop() {
                    self.idle.fetch_sub(1, Ordering::AcqRel);
                    self.available.store(batches.len(), Ordering::Release);
                    return Some(batch);
                }
            }
            if self.idle.load(Ordering::Acquire) == self.workers
                && self.available.load(Ordering::Acquire) == 0
            {
                return None;
            }
            waits += 1;
            if waits < 256 {
                std::hint::spin_loop();
            } else {
                std::thread::yield_now();
            }
        }
    }

    fn work(&self, gc: &Gc, mut stack: MarkStack) {
        let mut marked = 0;
        let mut marked_leaf = 0..0;
        let mut until_check = SHARE_CHECK_INTERVAL;
        loop {
            while let Some(ptr) = stack.pop() {
                if !marked_leaf.contains(&(ptr as usize)) {
                    marked += usize::from(gc.mark_ptr::<true>(ptr, &mut stack, &mut marked_leaf));
                }
                until_check -= 1;
                if until_check == 0 {
                    until_check = SHARE_CHECK_INTERVAL;
                    if stack.len() >= MIN_SHARED_STACK
                        && self.idle.load(Ordering::Relaxed)
                            > self.available.load(Ordering::Relaxed)
                    {
                        self.share(&mut stack);
                    }
                }
            }
            self.idle.fetch_add(1, Ordering::AcqRel);
            match self.next_batch() {
                Some(batch) => stack = batch,
                None => break,
            }
        }
        self.marked.fetch_add(marked, Ordering::Relaxed);
    }
}

struct Job {
    gc: *const Gc,
    pool: *const Pool,
    /// Helpers still wanted for the current collection.
    places: usize,
    spawned: usize,
}

// Both pointers are only followed between a helper taking a place, under the lock,
// and leaving `inside`, and the collection outlives that by waiting for `inside`.
unsafe impl Send for Job {}

struct Helpers {
    job: Mutex<Job>,
    wake: Condvar,
    inside: AtomicUsize,
    in_use: AtomicBool,
}

static HELPERS: Helpers = Helpers {
    job: Mutex::new(Job {
        gc: std::ptr::null(),
        pool: std::ptr::null(),
        places: 0,
        spawned: 0,
    }),
    wake: Condvar::new(),
    inside: AtomicUsize::new(0),
    in_use: AtomicBool::new(false),
};

fn run_helper() {
    let mut job = HELPERS.job.lock().unwrap();
    loop {
        if job.places == 0 {
            job = HELPERS.wake.wait(job).unwrap();
            continue;
        }
        job.places -= 1;
        HELPERS.inside.fetch_add(1, Ordering::Relaxed);
        let (gc, pool) = (job.gc, job.pool);
        drop(job);
        // SAFETY: see `Job`.
        let (gc, pool) = unsafe { (&*gc, &*pool) };
        if let Some(batch) = pool.next_batch() {
            pool.work(gc, batch);
        }
        HELPERS.inside.fetch_sub(1, Ordering::Release);
        job = HELPERS.job.lock().unwrap();
    }
}

/// Start helpers up to `wanted`, returning how many exist. Having fewer than wanted
/// only makes marking slower, so failing to start one isn't an error.
fn ensure_helpers(job: &mut Job, wanted: usize) -> usize {
    while job.spawned < wanted {
        let started = std::thread::Builder::new()
            .name("taro-gc-mark".to_string())
            .stack_size(HELPER_STACK_BYTES)
            .spawn(run_helper);
        if started.is_err() {
            break;
        }
        job.spawned += 1;
    }
    job.spawned.min(wanted)
}

/// Mark everything reachable from `stack` on `threads` threads, returning how many
/// objects were marked, or giving `stack` back if another collection, which only
/// tests run at the same time, is using the helpers.
pub(super) fn mark(gc: &Gc, stack: MarkStack, threads: usize) -> Result<usize, MarkStack> {
    if HELPERS
        .in_use
        .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
        .is_err()
    {
        return Err(stack);
    }
    let mut job = HELPERS.job.lock().unwrap();
    let helpers = ensure_helpers(&mut job, threads - 1);
    let pool = Pool::new(helpers);
    job.gc = gc;
    job.pool = &pool;
    job.places = helpers;
    drop(job);
    HELPERS.wake.notify_all();

    pool.work(gc, stack);

    HELPERS.job.lock().unwrap().places = 0;
    while HELPERS.inside.load(Ordering::Acquire) != 0 {
        std::thread::yield_now();
    }
    HELPERS.in_use.store(false, Ordering::Release);
    Ok(pool.marked.load(Ordering::Relaxed))
}
