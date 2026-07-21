//! Process-local support for generated benchmark harnesses.
//!
//! The compiler emits only case metadata and a small wrapper. Calibration,
//! measurement, panic containment, and protocol serialization live here so
//! every compiler backend observes the same benchmark semantics.

use serde::Serialize;
use std::{
    cell::RefCell,
    fs::OpenOptions,
    io::Write,
    time::{Duration, Instant},
};

const ACTION_ENV: &str = "TARO_BENCH_ACTION";
const CASE_ENV: &str = "TARO_BENCH_CASE";
const PROTOCOL_PATH_ENV: &str = "TARO_BENCH_PROTOCOL_PATH";
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

#[derive(Serialize)]
struct ProtocolRecord<'a> {
    protocol_version: u32,
    kind: &'static str,
    name: &'a str,
    tags: &'a [String],
    skipped: bool,
    skip_reason: Option<&'a str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    status: Option<&'static str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    error: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    iterations_per_sample: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    samples_ns_per_op: Option<Vec<f64>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    median_ns_per_op: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    p95_ns_per_op: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    mad_ns_per_op: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    bytes_per_iteration: Option<usize>,
}

impl<'a> ProtocolRecord<'a> {
    fn listed(name: &'a str, tags: &'a [String], skipped: bool, reason: Option<&'a str>) -> Self {
        Self {
            protocol_version: 1,
            kind: "case",
            name,
            tags,
            skipped,
            skip_reason: reason,
            status: None,
            error: None,
            iterations_per_sample: None,
            samples_ns_per_op: None,
            median_ns_per_op: None,
            p95_ns_per_op: None,
            mad_ns_per_op: None,
            bytes_per_iteration: None,
        }
    }
}

fn parse_bytes(ptr: *const u8, len: usize) -> String {
    if ptr.is_null() || len == 0 {
        return String::new();
    }
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    String::from_utf8_lossy(bytes).into_owned()
}

fn parse_tags(ptr: *const u8, len: usize) -> Vec<String> {
    if ptr.is_null() || len == 0 {
        return Vec::new();
    }
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    bytes
        .split(|byte| *byte == 0)
        .filter(|tag| !tag.is_empty())
        .map(|tag| String::from_utf8_lossy(tag).into_owned())
        .collect()
}

fn write_record(record: &ProtocolRecord<'_>) -> Result<(), String> {
    let path = std::env::var_os(PROTOCOL_PATH_ENV).ok_or_else(|| {
        format!("missing {PROTOCOL_PATH_ENV}; run this executable through `taro bench`")
    })?;
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .map_err(|error| format!("could not open benchmark protocol file {path:?}: {error}"))?;
    serde_json::to_writer(&mut file, record)
        .map_err(|error| format!("could not serialize benchmark result: {error}"))?;
    file.write_all(b"\n")
        .map_err(|error| format!("could not write benchmark result: {error}"))
}

fn percentile_nearest_rank(sorted: &[f64], percentile: f64) -> f64 {
    let rank = (percentile * sorted.len() as f64).ceil() as usize;
    sorted[rank.saturating_sub(1).min(sorted.len() - 1)]
}

fn summary(samples: &[f64]) -> (f64, f64, f64) {
    let mut sorted = samples.to_vec();
    sorted.sort_by(f64::total_cmp);
    let median = if sorted.len() % 2 == 0 {
        (sorted[sorted.len() / 2 - 1] + sorted[sorted.len() / 2]) / 2.0
    } else {
        sorted[sorted.len() / 2]
    };
    let mut deviations = sorted
        .iter()
        .map(|sample| (sample - median).abs())
        .collect::<Vec<_>>();
    deviations.sort_by(f64::total_cmp);
    let mad = if deviations.len() % 2 == 0 {
        (deviations[deviations.len() / 2 - 1] + deviations[deviations.len() / 2]) / 2.0
    } else {
        deviations[deviations.len() / 2]
    };
    (median, percentile_nearest_rank(&sorted, 0.95), mad)
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

/// List or run one statically generated benchmark case.
#[unsafe(no_mangle)]
pub extern "C" fn __rt__bench_run_case(
    function: extern "C-unwind" fn(),
    name_ptr: *const u8,
    name_len: usize,
    tags_ptr: *const u8,
    tags_len: usize,
    skipped: bool,
    reason_ptr: *const u8,
    reason_len: usize,
) -> u8 {
    let name = parse_bytes(name_ptr, name_len);
    let tags = parse_tags(tags_ptr, tags_len);
    let reason = parse_bytes(reason_ptr, reason_len);
    let reason = (!reason.is_empty()).then_some(reason);

    let action = match Action::from_env() {
        Ok(action) => action,
        Err(error) => {
            eprintln!("benchmark harness error: {error}");
            return 1;
        }
    };

    if action == Action::List {
        return match write_record(&ProtocolRecord::listed(
            &name,
            &tags,
            skipped,
            reason.as_deref(),
        )) {
            Ok(()) => 0,
            Err(error) => {
                eprintln!("benchmark harness error: {error}");
                1
            }
        };
    }

    if std::env::var(CASE_ENV).ok().as_deref() != Some(name.as_str()) {
        return 0;
    }

    if skipped {
        let mut record = ProtocolRecord::listed(&name, &tags, true, reason.as_deref());
        record.kind = "result";
        record.status = Some("skipped");
        return match write_record(&record) {
            Ok(()) => 0,
            Err(error) => {
                eprintln!("benchmark harness error: {error}");
                1
            }
        };
    }

    let config = match BenchmarkConfig::from_env() {
        Ok(config) => config,
        Err(error) => {
            eprintln!("benchmark harness error: {error}");
            return 1;
        }
    };
    if STATE.with(|slot| slot.borrow().is_some()) {
        eprintln!("benchmark harness error: nested benchmark invocation");
        return 1;
    }
    STATE.with(|slot| *slot.borrow_mut() = Some(BenchmarkState::new(config)));

    let panicked = crate::panic_unwind::__rt__test_call_fn(function);
    let state = STATE
        .with(|slot| slot.borrow_mut().take())
        .expect("benchmark state installed");

    let mut record = ProtocolRecord::listed(&name, &tags, false, None);
    record.kind = "result";
    record.iterations_per_sample = Some(state.batch_iterations);
    record.bytes_per_iteration = state.bytes_per_iteration;

    if panicked {
        record.status = Some("failed");
        record.error = Some("benchmark panicked".into());
        crate::panic_unwind::finish_unexpected_harness_panic();
    } else if !state.called_next {
        record.status = Some("failed");
        record.error = Some("benchmark returned without calling benchmark.next()".into());
    } else if state.phase != Phase::Done || state.samples_ns_per_op.len() != config.samples {
        record.status = Some("failed");
        record.error = Some("benchmark stopped before measurement completed".into());
    } else {
        let (median, p95, mad) = summary(&state.samples_ns_per_op);
        record.status = Some("ok");
        record.samples_ns_per_op = Some(state.samples_ns_per_op);
        record.median_ns_per_op = Some(median);
        record.p95_ns_per_op = Some(p95);
        record.mad_ns_per_op = Some(mad);
    }

    let failed = record.status != Some("ok");
    if let Err(error) = write_record(&record) {
        eprintln!("benchmark harness error: {error}");
        return 1;
    }
    u8::from(failed)
}

#[cfg(test)]
mod tests {
    use super::{BenchmarkConfig, BenchmarkState, Phase, calibrated_iterations, summary};
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

    #[test]
    fn summary_uses_median_nearest_rank_p95_and_mad() {
        let (median, p95, mad) = summary(&[1.0, 2.0, 3.0, 100.0]);
        assert_eq!(median, 2.5);
        assert_eq!(p95, 100.0);
        assert_eq!(mad, 1.0);
    }
}
