//! Process-local support for generated benchmark harnesses.
//!
//! The compiler emits only case metadata and a small wrapper. Calibration,
//! measurement, and panic containment live here. The standard library
//! summarizes completed measurements and writes the benchmark protocol.

use std::{
    cell::RefCell,
    time::{Duration, Instant},
};

const ACTION_ENV: &str = "TARO_BENCH_ACTION";
const CASE_ENV: &str = "TARO_BENCH_CASE";
const WARMUP_NS_ENV: &str = "TARO_BENCH_WARMUP_NS";
const MEASUREMENT_NS_ENV: &str = "TARO_BENCH_MEASUREMENT_NS";
const SAMPLES_ENV: &str = "TARO_BENCH_SAMPLES";

const DEFAULT_WARMUP_NS: u64 = 250_000_000;
const DEFAULT_MEASUREMENT_NS: u64 = 1_000_000_000;
const DEFAULT_SAMPLES: usize = 20;
const MAX_SAMPLES: usize = 10_000;
const MAX_BATCH_ITERATIONS: u64 = 1 << 48;

thread_local! {
    static STATE: RefCell<Option<BenchmarkState>> = const { RefCell::new(None) };
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Action {
    List,
    Run,
}

impl Action {
    fn from_env() -> Result<Self, String> {
        match std::env::var(ACTION_ENV).as_deref() {
            Ok("list") => Ok(Self::List),
            Ok("run") => Ok(Self::Run),
            Ok(other) => Err(format!("unsupported benchmark action {other:?}")),
            Err(_) => Err(format!(
                "missing {ACTION_ENV}; run this executable through `taro bench`"
            )),
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct BenchmarkConfig {
    warmup: Duration,
    measurement: Duration,
    samples: usize,
}

impl BenchmarkConfig {
    fn from_env() -> Result<Self, String> {
        let warmup_ns = parse_env_u64(WARMUP_NS_ENV, DEFAULT_WARMUP_NS)?;
        let measurement_ns = parse_env_u64(MEASUREMENT_NS_ENV, DEFAULT_MEASUREMENT_NS)?;
        let samples = parse_env_usize(SAMPLES_ENV, DEFAULT_SAMPLES)?;
        if measurement_ns == 0 {
            return Err("benchmark measurement time must be greater than zero".into());
        }
        if samples == 0 {
            return Err("benchmark sample count must be greater than zero".into());
        }
        if samples > MAX_SAMPLES {
            return Err(format!(
                "benchmark sample count must not exceed {MAX_SAMPLES}"
            ));
        }
        Ok(Self {
            warmup: Duration::from_nanos(warmup_ns),
            measurement: Duration::from_nanos(measurement_ns),
            samples,
        })
    }

    fn target_sample_time(self) -> Duration {
        let nanos = (self.measurement.as_nanos() / self.samples as u128).max(1);
        Duration::from_nanos(nanos.min(u64::MAX as u128) as u64)
    }
}

fn parse_env_u64(name: &str, default: u64) -> Result<u64, String> {
    match std::env::var(name) {
        Ok(value) => value
            .parse()
            .map_err(|_| format!("{name} must be an unsigned integer, got {value:?}")),
        Err(std::env::VarError::NotPresent) => Ok(default),
        Err(error) => Err(format!("could not read {name}: {error}")),
    }
}

fn parse_env_usize(name: &str, default: usize) -> Result<usize, String> {
    match std::env::var(name) {
        Ok(value) => value
            .parse()
            .map_err(|_| format!("{name} must be an unsigned integer, got {value:?}")),
        Err(std::env::VarError::NotPresent) => Ok(default),
        Err(error) => Err(format!("could not read {name}: {error}")),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Phase {
    Warmup,
    Measure,
    Done,
}

#[derive(Debug)]
struct BenchmarkState {
    config: BenchmarkConfig,
    phase: Phase,
    batch_started: Option<Instant>,
    batch_iterations: u64,
    warmup_elapsed: Duration,
    samples_ns_per_op: Vec<f64>,
    bytes_per_iteration: Option<usize>,
    called_next: bool,
}

impl BenchmarkState {
    fn new(config: BenchmarkConfig) -> Self {
        Self {
            config,
            phase: Phase::Warmup,
            batch_started: None,
            batch_iterations: 1,
            warmup_elapsed: Duration::ZERO,
            samples_ns_per_op: Vec::with_capacity(config.samples),
            bytes_per_iteration: None,
            called_next: false,
        }
    }

    fn next_batch_at(&mut self, now: Instant) -> usize {
        self.called_next = true;
        if self.phase == Phase::Done {
            return 0;
        }

        if let Some(started) = self.batch_started.take() {
            self.finish_batch(now.saturating_duration_since(started));
            if self.phase == Phase::Done {
                return 0;
            }
        }

        self.batch_started = Some(now);
        self.batch_iterations.min(usize::MAX as u64) as usize
    }

    fn finish_batch(&mut self, elapsed: Duration) {
        let iterations = self.batch_iterations.max(1);
        match self.phase {
            Phase::Warmup => {
                self.warmup_elapsed = self.warmup_elapsed.saturating_add(elapsed);
                self.batch_iterations =
                    calibrated_iterations(iterations, elapsed, self.config.target_sample_time());

                // A target-sized batch is required even when warmup is zero.
                // This avoids recording the one-iteration calibration probe as
                // a real sample for very fast benchmarks.
                let target_nanos = self.config.target_sample_time().as_nanos();
                let batch_is_representative = elapsed.as_nanos().saturating_mul(2) >= target_nanos;
                if self.warmup_elapsed >= self.config.warmup && batch_is_representative {
                    self.phase = Phase::Measure;
                }
            }
            Phase::Measure => {
                self.samples_ns_per_op
                    .push(elapsed.as_secs_f64() * 1_000_000_000.0 / iterations as f64);
                if self.samples_ns_per_op.len() >= self.config.samples {
                    self.phase = Phase::Done;
                }
            }
            Phase::Done => {}
        }
    }
}

fn calibrated_iterations(current: u64, elapsed: Duration, target: Duration) -> u64 {
    let elapsed_nanos = elapsed.as_nanos().max(1);
    let target_nanos = target.as_nanos().max(1);
    let estimated = (current as u128)
        .saturating_mul(target_nanos)
        .saturating_add(elapsed_nanos - 1)
        / elapsed_nanos;

    // Limit each calibration jump so a timer anomaly cannot create a giant,
    // effectively uninterruptible batch. Repeated warmup batches still ramp
    // quickly for sub-nanosecond optimized operations.
    let upper_step = current.saturating_mul(10).max(1);
    estimated.clamp(1, upper_step.min(MAX_BATCH_ITERATIONS) as u128) as u64
}

/// Drive warmup and measured batches for the active benchmark.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__bench_next_batch() -> usize {
    STATE.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(state) = slot.as_mut() else {
            eprintln!("benchmark.next() called outside a benchmark harness");
            return 0;
        };
        state.next_batch_at(Instant::now())
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn __rt__bench_set_bytes(bytes: usize) {
    STATE.with(|slot| {
        let mut slot = slot.borrow_mut();
        if let Some(state) = slot.as_mut() {
            state.bytes_per_iteration = Some(bytes);
        } else {
            eprintln!("benchmark.setBytes() called outside a benchmark harness");
        }
    });
}

/// Opaque a materialized value to LLVM while preserving its bytes unchanged.
///
/// Taro codegen passes a temporary allocation. Because this separately
/// compiled function may mutate that pointer from LLVM's perspective, the
/// reload after the call cannot be replaced with the pre-call SSA value.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__black_box(value: *mut u8, size: usize) {
    std::hint::black_box((value, size));
}

// Keep these values in sync with std.bench's report driver.
#[repr(u8)]
enum CaseOutcome {
    Ignore = 0,
    Listed = 1,
    Skipped = 2,
    Measured = 3,
    Panicked = 4,
    MissingNext = 5,
    Incomplete = 6,
    HarnessError = 7,
}

/// The matching `@repr("C")` standard-library type is used by codegen to
/// allocate one output slot in the generated harness. Only successful
/// measurements transfer a sample allocation to the reporter.
#[repr(C)]
pub struct BenchmarkMeasurement {
    iterations: u64,
    bytes_per_iteration: usize,
    samples: *mut f64,
    sample_count: usize,
    has_bytes: bool,
}

// std/src/bench/report.tr declares the same fields in this order with
// `@repr("C")`. Pin that layout so a change on this side cannot silently
// disagree with the reader, which has no way to check it.
const _: () = {
    use std::mem::{offset_of, size_of};
    let word = size_of::<usize>();
    assert!(offset_of!(BenchmarkMeasurement, iterations) == 0);
    assert!(offset_of!(BenchmarkMeasurement, bytes_per_iteration) == 8);
    assert!(offset_of!(BenchmarkMeasurement, samples) == 8 + word);
    assert!(offset_of!(BenchmarkMeasurement, sample_count) == 8 + 2 * word);
    assert!(offset_of!(BenchmarkMeasurement, has_bytes) == 8 + 3 * word);
    assert!(size_of::<BenchmarkMeasurement>() == (8 + 3 * word + 1).next_multiple_of(8));
};

/// Select or measure one statically generated case.
///
/// # Safety
/// The callback must be a valid generated benchmark wrapper. `name_ptr`
/// must address `name_len` immutable bytes of compiler-generated UTF-8.
/// `output` must be aligned, writable storage for one measurement. The caller
/// must release any returned sample allocation exactly once.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__bench_measure_case(
    function: extern "C-unwind" fn(),
    name_ptr: *const u8,
    name_len: usize,
    skipped: bool,
    output: *mut BenchmarkMeasurement,
) -> u8 {
    let action = match Action::from_env() {
        Ok(action) => action,
        Err(error) => {
            eprintln!("benchmark harness error: {error}");
            return CaseOutcome::HarnessError as u8;
        }
    };
    if action == Action::List {
        return CaseOutcome::Listed as u8;
    }

    let name =
        unsafe { std::str::from_utf8_unchecked(std::slice::from_raw_parts(name_ptr, name_len)) };
    if std::env::var(CASE_ENV).ok().as_deref() != Some(name) {
        return CaseOutcome::Ignore as u8;
    }
    if skipped {
        return CaseOutcome::Skipped as u8;
    }

    let config = match BenchmarkConfig::from_env() {
        Ok(config) => config,
        Err(error) => {
            eprintln!("benchmark harness error: {error}");
            return CaseOutcome::HarnessError as u8;
        }
    };
    if STATE.with(|slot| slot.borrow().is_some()) {
        eprintln!("benchmark harness error: nested benchmark invocation");
        return CaseOutcome::HarnessError as u8;
    }
    STATE.with(|slot| *slot.borrow_mut() = Some(BenchmarkState::new(config)));

    let panicked = crate::panic_unwind::__rt__test_call_fn(function);
    let state = STATE
        .with(|slot| slot.borrow_mut().take())
        .expect("benchmark state installed");

    let outcome = if panicked {
        crate::panic_unwind::finish_unexpected_harness_panic();
        CaseOutcome::Panicked
    } else if !state.called_next {
        CaseOutcome::MissingNext
    } else if state.phase != Phase::Done || state.samples_ns_per_op.len() != config.samples {
        CaseOutcome::Incomplete
    } else {
        CaseOutcome::Measured
    };

    let mut measurement = BenchmarkMeasurement {
        iterations: state.batch_iterations,
        bytes_per_iteration: state.bytes_per_iteration.unwrap_or(0),
        samples: std::ptr::null_mut(),
        sample_count: 0,
        has_bytes: state.bytes_per_iteration.is_some(),
    };
    if matches!(outcome, CaseOutcome::Measured) {
        let samples = state.samples_ns_per_op.into_boxed_slice();
        measurement.sample_count = samples.len();
        measurement.samples = Box::into_raw(samples).cast::<f64>();
    }
    unsafe { output.write(measurement) };
    outcome as u8
}

/// # Safety
/// A non-null pointer and count must come from a successful measurement
/// that has not been released yet.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __rt__bench_release_samples(samples: *mut f64, count: usize) {
    if !samples.is_null() {
        let slice = std::ptr::slice_from_raw_parts_mut(samples, count);
        drop(unsafe { Box::from_raw(slice) });
    }
}

#[cfg(test)]
mod tests {
    use super::{BenchmarkConfig, BenchmarkState, Phase, calibrated_iterations};
    use std::time::{Duration, Instant};

    #[test]
    fn calibration_is_bounded_and_never_zero() {
        assert_eq!(
            calibrated_iterations(1, Duration::ZERO, Duration::from_millis(10)),
            10
        );
        assert_eq!(
            calibrated_iterations(100, Duration::from_secs(10), Duration::from_millis(1)),
            1
        );
    }

    #[test]
    fn state_collects_the_requested_number_of_samples() {
        let config = BenchmarkConfig {
            warmup: Duration::ZERO,
            measurement: Duration::from_nanos(40),
            samples: 2,
        };
        let mut state = BenchmarkState::new(config);
        let mut now = Instant::now();

        assert_eq!(state.next_batch_at(now), 1);
        now += Duration::from_nanos(20);
        assert_eq!(state.next_batch_at(now), 1);
        assert_eq!(state.phase, Phase::Measure);
        now += Duration::from_nanos(20);
        assert_eq!(state.next_batch_at(now), 1);
        now += Duration::from_nanos(20);
        assert_eq!(state.next_batch_at(now), 0);
        assert_eq!(state.samples_ns_per_op.len(), 2);
    }
}
