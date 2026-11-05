//! Trusted admission ABI for compiler-owned, process-long static storage.
//! Successful admission publishes the initialized value to every caller.
use super::{InitError, InitGate};
use crate::{
    abi::{RawSource, invalid_metadata, read_source},
    panic_unwind::{__rt__panic_unwind_at, RtString},
};
use std::sync::atomic::{AtomicPtr, Ordering};

struct StaticInit {
    gate: InitGate,
    data: usize,
    initialize: usize,
}

impl StaticInit {
    /// The compiler owns the slot and payload for the entire process. Nothing
    /// registers a global destructor or destroys the initialized payload here.
    unsafe fn from_slot(slot: *mut *mut u8, data: *mut u8, initialize: *const u8) -> &'static Self {
        if slot.is_null() || data.is_null() || initialize.is_null() || !slot.is_aligned() {
            invalid_metadata("invalid lazy static admission pointers");
        }
        let slot = unsafe { AtomicPtr::<StaticInit>::from_ptr(slot.cast()) };
        let mut state = slot.load(Ordering::Acquire);
        if state.is_null() {
            let candidate = Box::into_raw(Box::new(Self {
                gate: InitGate::new(),
                data: data as usize,
                initialize: initialize as usize,
            }));
            state = match slot.compare_exchange(
                std::ptr::null_mut(),
                candidate,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => candidate,
                Err(published) => {
                    // No value, callback environment or access owner belongs
                    // to a losing metadata candidate; dropping it runs no Taro.
                    drop(unsafe { Box::from_raw(candidate) });
                    published
                }
            };
        }
        let state = unsafe { &*state };
        if state.data != data as usize || state.initialize != initialize as usize {
            invalid_metadata("lazy static storage or initializer changed");
        }
        state
    }
}

/// Initialize a static once. Recursive/cross-worker cycles panic; a failed
/// initializer is never retried. Waiters park, and the winner runs as a managed
/// mutator. Partial storage is never published.
///
/// # Safety
/// slot is a distinct, zero-initialized, pointer-aligned process-long global.
/// Every call uses the same data and C-unwind initializer addresses. The
/// initializer writes the complete value before returning. Source metadata is
/// readable for this call and its file bytes have process lifetime.
#[unsafe(no_mangle)]
pub unsafe extern "C-unwind" fn __rt__static_initialize(
    slot: *mut *mut u8,
    data: *mut u8,
    initialize: *const u8,
    source: *const RawSource,
) {
    let source = unsafe { read_source(source) };
    let state = unsafe { StaticInit::from_slot(slot, data, initialize) };
    let result = state.gate.ensure(|| {
        let initialize: unsafe extern "C-unwind" fn(*mut u8) =
            unsafe { std::mem::transmute(state.initialize) };
        crate::stack_guard::guard_current_thread();
        unsafe { initialize(data) };
        Ok(())
    });
    if let Err(error) = result {
        let message: &[u8] = match error {
            InitError::Cycle => b"static initialization dependency cycle",
            InitError::PreviouslyFailed => b"static initialization previously failed",
        };
        __rt__panic_unwind_at(
            RtString {
                ptr: message.as_ptr(),
                len: message.len(),
            },
            RtString {
                ptr: source.file.as_ptr(),
                len: source.file.len(),
            },
            source.line as usize,
            source.column as usize,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::panic_unwind::catch_executor_panic;
    use std::sync::{Arc, Barrier, atomic::AtomicUsize};

    struct Payload {
        calls: AtomicUsize,
        value: AtomicUsize,
    }
    struct Fixture {
        slot: AtomicPtr<u8>,
        payload: Payload,
    }
    impl Fixture {
        fn new() -> &'static Self {
            // Actual ABI storage is process-long and never receives automatic
            // teardown. Use the same lifetime here, including failed fixtures.
            Box::leak(Box::new(Self {
                slot: AtomicPtr::new(std::ptr::null_mut()),
                payload: Payload {
                    calls: AtomicUsize::new(0),
                    value: AtomicUsize::new(0),
                },
            }))
        }
        fn ensure(&self, initialize: unsafe extern "C-unwind" fn(*mut u8)) {
            unsafe {
                __rt__static_initialize(
                    self.slot.as_ptr(),
                    (&raw const self.payload).cast_mut().cast(),
                    initialize as *const u8,
                    &RawSource {
                        file: b"static_init.tr".as_ptr(),
                        file_len: 14,
                        line: 7,
                        column: 3,
                    },
                )
            }
        }
    }
    unsafe extern "C-unwind" fn initialize(data: *mut u8) {
        let payload = unsafe { &*data.cast::<Payload>() };
        payload.calls.fetch_add(1, Ordering::Relaxed);
        payload.value.store(41, Ordering::Relaxed);
    }

    #[test]
    fn admission_publishes_once_for_concurrent_and_repeated_callers() {
        let fixture = Fixture::new();
        let start = Arc::new(Barrier::new(8));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let start = start.clone();
                std::thread::spawn(move || {
                    start.wait();
                    fixture.ensure(initialize);
                    assert_eq!(fixture.payload.value.load(Ordering::Relaxed), 41);
                })
            })
            .collect();
        for thread in threads {
            thread.join().unwrap();
        }
        assert_eq!(fixture.payload.calls.load(Ordering::Relaxed), 1);
        fixture.ensure(initialize);
        assert_eq!(fixture.payload.calls.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn initializer_panic_permanently_fails_the_slot_with_a_source_diagnostic() {
        unsafe extern "C-unwind" fn fails(data: *mut u8) {
            unsafe { &*data.cast::<Payload>() }
                .calls
                .fetch_add(1, Ordering::Relaxed);
            panic!("initializer panic");
        }
        let fixture = Fixture::new();
        assert!(catch_executor_panic(|| fixture.ensure(fails)).is_err());
        let report = catch_executor_panic(|| fixture.ensure(fails)).unwrap_err();
        assert_eq!(report.message, "static initialization previously failed");
        assert!(
            report
                .location
                .as_deref()
                .unwrap()
                .contains("static_init.tr:7:3")
        );
        assert_eq!(fixture.payload.calls.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn recursive_admission_panics_without_publishing_or_retrying() {
        unsafe extern "C-unwind" fn recursive(data: *mut u8) {
            let fixture = unsafe { &*data.cast::<Fixture>() };
            unsafe {
                __rt__static_initialize(
                    fixture.slot.as_ptr(),
                    data,
                    recursive as *const u8,
                    &RawSource {
                        file: b"cycle.tr".as_ptr(),
                        file_len: 8,
                        line: 2,
                        column: 1,
                    },
                )
            };
        }
        let fixture = Fixture::new();
        let invoke = || unsafe {
            __rt__static_initialize(
                fixture.slot.as_ptr(),
                (fixture as *const Fixture).cast_mut().cast(),
                recursive as *const u8,
                &RawSource {
                    file: b"cycle.tr".as_ptr(),
                    file_len: 8,
                    line: 1,
                    column: 1,
                },
            )
        };
        let report = catch_executor_panic(invoke).unwrap_err();
        assert_eq!(report.message, "static initialization dependency cycle");
        assert!(report.location.as_deref().unwrap().contains("cycle.tr:2:1"));
        assert_eq!(
            catch_executor_panic(invoke).unwrap_err().message,
            "static initialization previously failed"
        );
    }
}
