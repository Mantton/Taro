use crate::{
    BenchArgs, BenchOutputFormat,
    command::{CommandOutcome, CommandResult, build},
};
use compiler::error::ReportedError;
use serde::{Deserialize, Serialize};
use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Stdio},
    sync::atomic::{AtomicU64, Ordering},
    time::{Duration, SystemTime, UNIX_EPOCH},
};

const PROTOCOL_VERSION: u32 = 1;
const FAILURE_EXIT_CODE: i32 = 101;
const MAX_SAMPLES: usize = 10_000;
static NEXT_PROTOCOL_FILE: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Debug, Deserialize)]
struct ProtocolRecord {
    protocol_version: u32,
    kind: String,
    name: String,
    tags: Vec<String>,
    skipped: bool,
    skip_reason: Option<String>,
    status: Option<String>,
    error: Option<String>,
    iterations_per_sample: Option<u64>,
    samples_ns_per_op: Option<Vec<f64>>,
    median_ns_per_op: Option<f64>,
    p95_ns_per_op: Option<f64>,
    mad_ns_per_op: Option<f64>,
    bytes_per_iteration: Option<usize>,
}

#[derive(Clone, Debug, Serialize)]
struct BenchmarkResult {
    name: String,
    tags: Vec<String>,
    skipped: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    skip_reason: Option<String>,
    status: String,
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
    #[serde(skip_serializing_if = "Option::is_none")]
    throughput_bytes_per_second: Option<f64>,
}

impl BenchmarkResult {
    fn listed(case: &ProtocolRecord) -> Self {
        Self {
            name: case.name.clone(),
            tags: case.tags.clone(),
            skipped: case.skipped,
            skip_reason: case.skip_reason.clone(),
            status: "listed".into(),
            error: None,
            iterations_per_sample: None,
            samples_ns_per_op: None,
            median_ns_per_op: None,
            p95_ns_per_op: None,
            mad_ns_per_op: None,
            bytes_per_iteration: None,
            throughput_bytes_per_second: None,
        }
    }

    fn skipped(case: &ProtocolRecord) -> Self {
        let mut result = Self::listed(case);
        result.status = "skipped".into();
        result
    }

    fn failed(case: &ProtocolRecord, error: impl Into<String>) -> Self {
        let mut result = Self::listed(case);
        result.status = "failed".into();
        result.error = Some(error.into());
        result
    }

    fn from_protocol(record: ProtocolRecord, expected_samples: usize) -> Result<Self, String> {
        validate_protocol_record(&record, "result")?;
        let status = record
            .status
            .as_deref()
            .ok_or_else(|| format!("result for {:?} is missing status", record.name))?;
        if !matches!(status, "ok" | "failed" | "skipped") {
            return Err(format!(
                "result for {:?} has unknown status {status:?}",
                record.name
            ));
        }

        if status == "ok" {
            let samples = record.samples_ns_per_op.as_ref().ok_or_else(|| {
                format!("successful result for {:?} is missing samples", record.name)
            })?;
            if samples.len() != expected_samples {
                return Err(format!(
                    "result for {:?} contains {} samples; expected {}",
                    record.name,
                    samples.len(),
                    expected_samples
                ));
            }
            if samples
                .iter()
                .any(|value| !value.is_finite() || *value < 0.0)
            {
                return Err(format!(
                    "result for {:?} contains invalid samples",
                    record.name
                ));
            }
            for (label, value) in [
                ("median", record.median_ns_per_op),
                ("p95", record.p95_ns_per_op),
                ("MAD", record.mad_ns_per_op),
            ] {
                if !value.is_some_and(|value| value.is_finite() && value >= 0.0) {
                    return Err(format!(
                        "successful result for {:?} has invalid {label}",
                        record.name
                    ));
                }
            }
            if !record.iterations_per_sample.is_some_and(|value| value > 0) {
                return Err(format!(
                    "successful result for {:?} has no iteration count",
                    record.name
                ));
            }
        }

        let throughput = match (record.bytes_per_iteration, record.median_ns_per_op) {
            (Some(bytes), Some(nanos)) if nanos > 0.0 => {
                Some(bytes as f64 * 1_000_000_000.0 / nanos)
            }
            _ => None,
        };
        Ok(Self {
            name: record.name,
            tags: record.tags,
            skipped: record.skipped,
            skip_reason: record.skip_reason,
            status: status.to_owned(),
            error: record.error,
            iterations_per_sample: record.iterations_per_sample,
            samples_ns_per_op: record.samples_ns_per_op,
            median_ns_per_op: record.median_ns_per_op,
            p95_ns_per_op: record.p95_ns_per_op,
            mad_ns_per_op: record.mad_ns_per_op,
            bytes_per_iteration: record.bytes_per_iteration,
            throughput_bytes_per_second: throughput,
        })
    }
}

#[derive(Serialize)]
struct BenchmarkReport<'a> {
    schema_version: u32,
    command: &'static str,
    profile: &'static str,
    warmup_ns: u64,
    measurement_time_ns: u64,
    samples: usize,
    timeout_ns: u64,
    benchmarks: &'a [BenchmarkResult],
}

pub fn run(mut arguments: BenchArgs) -> CommandResult {
    validate_arguments(&arguments)?;

    // Benchmarks represent optimized application behavior by default. `--debug`
    // is intentionally explicit so accidental debug measurements are visible
    // both in the command line and the JSON report.
    arguments.common.release = !arguments.debug;
    let executable = build::run_bench_mode(arguments.common.clone())?;
    let executable =
        executable.ok_or_else(|| command_error("no benchmark executable was produced"))?;

    let listed = list_cases(&executable, arguments.timeout.as_duration())?;
    let selected = select_cases(
        listed,
        arguments.normalized_filter().as_deref(),
        &arguments.normalized_tags(),
    );
    if selected.is_empty() {
        return Err(command_error(
            "no benchmarks matched the requested selection",
        ));
    }

    if arguments.list {
        let results = selected
            .iter()
            .map(BenchmarkResult::listed)
            .collect::<Vec<_>>();
        emit_report(&arguments, "list", &results)?;
        return Ok(CommandOutcome::Success);
    }

    let mut results = Vec::with_capacity(selected.len());
    for case in &selected {
        if case.skipped {
            results.push(BenchmarkResult::skipped(case));
            continue;
        }
        results.push(run_case(&executable, case, &arguments)?);
    }

    emit_report(&arguments, "run", &results)?;
    if results.iter().any(|result| result.status == "failed") {
        Ok(CommandOutcome::ChildExit(FAILURE_EXIT_CODE))
    } else {
        Ok(CommandOutcome::Success)
    }
}

fn validate_arguments(arguments: &BenchArgs) -> Result<(), ReportedError> {
    if arguments.measurement_time.as_nanos() == 0 {
        return Err(command_error("--time must be greater than zero"));
    }
    if arguments.samples == 0 {
        return Err(command_error("--samples must be greater than zero"));
    }
    if arguments.samples > MAX_SAMPLES {
        return Err(command_error(format!(
            "--samples must not exceed {MAX_SAMPLES}"
        )));
    }
    if arguments.timeout.as_nanos() == 0 {
        return Err(command_error("--timeout must be greater than zero"));
    }
    Ok(())
}

fn list_cases(executable: &Path, timeout: Duration) -> Result<Vec<ProtocolRecord>, ReportedError> {
    let protocol = ProtocolFile::new()?;
    let outcome = spawn_harness(
        executable,
        "list",
        None,
        &protocol.path,
        None,
        timeout,
        false,
    )?;
    let ProcessOutcome::Finished(status) = outcome else {
        return Err(command_error("benchmark discovery timed out"));
    };
    if !status.success() {
        return Err(command_error(format!(
            "benchmark discovery process exited with {status}"
        )));
    }
    let records = protocol.read()?;
    for record in &records {
        validate_protocol_record(record, "case").map_err(command_error)?;
    }
    if records.is_empty() {
        return Err(command_error("no @bench functions were discovered"));
    }
    Ok(records)
}

fn run_case(
    executable: &Path,
    case: &ProtocolRecord,
    arguments: &BenchArgs,
) -> Result<BenchmarkResult, ReportedError> {
    let protocol = ProtocolFile::new()?;
    let settings = ProcessSettings {
        warmup_ns: arguments.warmup.as_nanos(),
        measurement_ns: arguments.measurement_time.as_nanos(),
        samples: arguments.samples,
    };
    let show_user_stdout = arguments.format == BenchOutputFormat::Human;
    let outcome = spawn_harness(
        executable,
        "run",
        Some(&case.name),
        &protocol.path,
        Some(settings),
        arguments.timeout.as_duration(),
        show_user_stdout,
    )?;
    if matches!(outcome, ProcessOutcome::TimedOut) {
        return Ok(BenchmarkResult::failed(
            case,
            format!(
                "timed out after {}",
                format_duration(arguments.timeout.as_duration())
            ),
        ));
    }

    let records = protocol.read()?;
    if records.is_empty() {
        if let ProcessOutcome::Finished(status) = outcome {
            if !status.success() {
                return Ok(BenchmarkResult::failed(
                    case,
                    format!("process exited with {status} before reporting a result"),
                ));
            }
        }
    }
    if records.len() != 1 {
        return Err(command_error(format!(
            "benchmark {:?} produced {} protocol records; expected exactly one",
            case.name,
            records.len()
        )));
    }
    let record = records.into_iter().next().expect("one record");
    if record.name != case.name {
        return Err(command_error(format!(
            "benchmark protocol returned {:?} while running {:?}",
            record.name, case.name
        )));
    }
    let result =
        BenchmarkResult::from_protocol(record, arguments.samples).map_err(command_error)?;
    if let ProcessOutcome::Finished(status) = outcome {
        if status.success() != (result.status == "ok") {
            return Err(command_error(format!(
                "benchmark {:?} result status {:?} disagrees with child exit status {status}",
                case.name, result.status
            )));
        }
    }
    Ok(result)
}

#[derive(Clone, Copy)]
struct ProcessSettings {
    warmup_ns: u64,
    measurement_ns: u64,
    samples: usize,
}

enum ProcessOutcome {
    Finished(ExitStatus),
    TimedOut,
}

fn spawn_harness(
    executable: &Path,
    action: &str,
    case: Option<&str>,
    protocol_path: &Path,
    settings: Option<ProcessSettings>,
    timeout: Duration,
    show_user_stdout: bool,
) -> Result<ProcessOutcome, ReportedError> {
    let mut command = Command::new(executable);
    command
        .env("TARO_BENCH_ACTION", action)
        .env("TARO_BENCH_PROTOCOL_PATH", protocol_path)
        .stderr(Stdio::inherit())
        .stdout(if show_user_stdout {
            Stdio::inherit()
        } else {
            Stdio::null()
        });
    if let Some(case) = case {
        command.env("TARO_BENCH_CASE", case);
    } else {
        command.env_remove("TARO_BENCH_CASE");
    }
    if let Some(settings) = settings {
        command
            .env("TARO_BENCH_WARMUP_NS", settings.warmup_ns.to_string())
            .env(
                "TARO_BENCH_MEASUREMENT_NS",
                settings.measurement_ns.to_string(),
            )
            .env("TARO_BENCH_SAMPLES", settings.samples.to_string());
    }

    let mut child = command.spawn().map_err(|error| {
        command_error(format!(
            "failed to execute benchmark harness '{}': {error}",
            executable.display()
        ))
    })?;
    wait_with_timeout(&mut child, timeout)
}

fn wait_with_timeout(
    child: &mut std::process::Child,
    timeout: Duration,
) -> Result<ProcessOutcome, ReportedError> {
    let started = std::time::Instant::now();
    loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|error| command_error(format!("failed to poll benchmark process: {error}")))?
        {
            return Ok(ProcessOutcome::Finished(status));
        }
        if started.elapsed() >= timeout {
            if let Err(error) = child.kill() {
                eprintln!("warning: failed to kill timed-out benchmark process: {error}");
            }
            let _ = child.wait();
            return Ok(ProcessOutcome::TimedOut);
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}

fn validate_protocol_record(record: &ProtocolRecord, expected_kind: &str) -> Result<(), String> {
    if record.protocol_version != PROTOCOL_VERSION {
        return Err(format!(
            "unsupported benchmark protocol version {}; expected {}",
            record.protocol_version, PROTOCOL_VERSION
        ));
    }
    if record.kind != expected_kind {
        return Err(format!(
            "benchmark protocol record {:?} has kind {:?}; expected {expected_kind:?}",
            record.name, record.kind
        ));
    }
    if record.name.is_empty() {
        return Err("benchmark protocol contains an empty case name".into());
    }
    Ok(())
}

fn select_cases(
    cases: Vec<ProtocolRecord>,
    filter: Option<&str>,
    requested_tags: &[String],
) -> Vec<ProtocolRecord> {
    let filter = filter.map(normalized_name);
    let requested_tags = requested_tags
        .iter()
        .map(|tag| tag.to_ascii_lowercase())
        .collect::<Vec<_>>();
    cases
        .into_iter()
        .filter(|case| {
            filter
                .as_ref()
                .is_none_or(|filter| normalized_name(&case.name).contains(filter))
                && (requested_tags.is_empty()
                    || case.tags.iter().any(|tag| {
                        requested_tags
                            .iter()
                            .any(|wanted| wanted.eq_ignore_ascii_case(tag))
                    }))
        })
        .collect()
}

fn normalized_name(name: &str) -> String {
    name.replace("::", ".").to_ascii_lowercase()
}

fn emit_report(
    arguments: &BenchArgs,
    command: &'static str,
    results: &[BenchmarkResult],
) -> Result<(), ReportedError> {
    if arguments.format == BenchOutputFormat::Json {
        let report = BenchmarkReport {
            schema_version: 1,
            command,
            profile: if arguments.debug { "debug" } else { "release" },
            warmup_ns: arguments.warmup.as_nanos(),
            measurement_time_ns: arguments.measurement_time.as_nanos(),
            samples: arguments.samples,
            timeout_ns: arguments.timeout.as_nanos(),
            benchmarks: results,
        };
        println!(
            "{}",
            serde_json::to_string_pretty(&report).map_err(|error| {
                command_error(format!("failed to serialize benchmark report: {error}"))
            })?
        );
        return Ok(());
    }

    if command == "list" {
        for result in results {
            let tags = if result.tags.is_empty() {
                String::new()
            } else {
                format!(" [{}]", result.tags.join(", "))
            };
            let skipped = if result.skipped { " (skipped)" } else { "" };
            println!("{}{}{}", result.name, tags, skipped);
        }
        return Ok(());
    }

    println!("running {} benchmarks", results.len());
    for result in results {
        match result.status.as_str() {
            "ok" => {
                let median = result.median_ns_per_op.expect("validated median");
                let p95 = result.p95_ns_per_op.expect("validated p95");
                let mad = result.mad_ns_per_op.expect("validated MAD");
                let iterations = result.iterations_per_sample.expect("validated iterations");
                let throughput = result
                    .throughput_bytes_per_second
                    .map(|value| format!("; {}", format_throughput(value)))
                    .unwrap_or_default();
                println!(
                    "{}  {} (p95 {}; MAD {}; {} iter/sample{})",
                    result.name,
                    format_ns_per_op(median),
                    format_ns_per_op(p95),
                    format_ns_per_op(mad),
                    iterations,
                    throughput
                );
            }
            "skipped" => println!(
                "{}  SKIPPED{}",
                result.name,
                result
                    .skip_reason
                    .as_deref()
                    .map(|reason| format!(" ({reason})"))
                    .unwrap_or_default()
            ),
            "failed" => println!(
                "{}  FAILED ({})",
                result.name,
                result
                    .error
                    .as_deref()
                    .unwrap_or("unknown benchmark failure")
            ),
            _ => unreachable!("validated status"),
        }
    }
    Ok(())
}

fn format_ns_per_op(nanos: f64) -> String {
    if nanos < 1_000.0 {
        format!("{nanos:.2} ns/op")
    } else if nanos < 1_000_000.0 {
        format!("{:.2} µs/op", nanos / 1_000.0)
    } else if nanos < 1_000_000_000.0 {
        format!("{:.2} ms/op", nanos / 1_000_000.0)
    } else {
        format!("{:.2} s/op", nanos / 1_000_000_000.0)
    }
}

fn format_throughput(bytes_per_second: f64) -> String {
    if bytes_per_second < 1_000_000.0 {
        format!("{:.2} kB/s", bytes_per_second / 1_000.0)
    } else if bytes_per_second < 1_000_000_000.0 {
        format!("{:.2} MB/s", bytes_per_second / 1_000_000.0)
    } else {
        format!("{:.2} GB/s", bytes_per_second / 1_000_000_000.0)
    }
}

fn format_duration(duration: Duration) -> String {
    if duration.as_secs() > 0 && duration.subsec_nanos() == 0 {
        format!("{}s", duration.as_secs())
    } else {
        format!("{:.3}s", duration.as_secs_f64())
    }
}

struct ProtocolFile {
    path: PathBuf,
}

impl ProtocolFile {
    fn new() -> Result<Self, ReportedError> {
        let unique = NEXT_PROTOCOL_FILE.fetch_add(1, Ordering::Relaxed);
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "taro-bench-{}-{timestamp}-{unique}.jsonl",
            std::process::id()
        ));
        File::create(&path).map_err(|error| {
            command_error(format!(
                "failed to create benchmark protocol file '{}': {error}",
                path.display()
            ))
        })?;
        Ok(Self { path })
    }

    fn read(&self) -> Result<Vec<ProtocolRecord>, ReportedError> {
        let file = File::open(&self.path).map_err(|error| {
            command_error(format!(
                "failed to open benchmark protocol file '{}': {error}",
                self.path.display()
            ))
        })?;
        BufReader::new(file)
            .lines()
            .enumerate()
            .filter_map(|(index, line)| match line {
                Ok(line) if line.trim().is_empty() => None,
                line => Some((index, line)),
            })
            .map(|(index, line)| {
                let line = line.map_err(|error| {
                    command_error(format!(
                        "failed to read benchmark protocol line {}: {error}",
                        index + 1
                    ))
                })?;
                serde_json::from_str(&line).map_err(|error| {
                    command_error(format!(
                        "invalid benchmark protocol JSON on line {}: {error}",
                        index + 1
                    ))
                })
            })
            .collect()
    }
}

impl Drop for ProtocolFile {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

fn command_error(message: impl std::fmt::Display) -> ReportedError {
    eprintln!("error: {message}");
    ReportedError
}

#[cfg(test)]
mod tests {
    use super::{
        BenchmarkResult, ProcessOutcome, ProtocolRecord, select_cases, validate_protocol_record,
        wait_with_timeout,
    };
    use std::{process::Command, time::Duration};

    fn case(name: &str, tags: &[&str]) -> ProtocolRecord {
        ProtocolRecord {
            protocol_version: 1,
            kind: "case".into(),
            name: name.into(),
            tags: tags.iter().map(|tag| (*tag).into()).collect(),
            skipped: false,
            skip_reason: None,
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

    #[test]
    fn runtime_selection_matches_names_and_any_requested_tag() {
        let selected = select_cases(
            vec![
                case("json::parseSmall", &["smoke"]),
                case("json::encodeSmall", &["slow"]),
            ],
            Some("JSON.Parse"),
            &["SMOKE".into(), "io".into()],
        );
        assert_eq!(selected.len(), 1);
        assert_eq!(selected[0].name, "json::parseSmall");
    }

    #[test]
    fn protocol_validation_rejects_version_drift_and_incomplete_success() {
        let mut version_drift = case("json::parse", &[]);
        version_drift.protocol_version = 2;
        assert!(validate_protocol_record(&version_drift, "case").is_err());

        let mut incomplete = case("json::parse", &[]);
        incomplete.kind = "result".into();
        incomplete.status = Some("ok".into());
        assert!(BenchmarkResult::from_protocol(incomplete, 20).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn timeout_kills_and_reaps_the_child() {
        let mut child = Command::new("/bin/sh")
            .args(["-c", "while :; do :; done"])
            .spawn()
            .expect("spawn shell loop");
        let Ok(outcome) = wait_with_timeout(&mut child, Duration::from_millis(20)) else {
            panic!("wait should succeed");
        };
        assert!(matches!(outcome, ProcessOutcome::TimedOut));
        assert!(child.try_wait().expect("poll reaped child").is_some());
    }
}
