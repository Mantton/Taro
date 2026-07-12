use std::collections::VecDeque;
use std::env::VarError;
use std::sync::Mutex;
use std::time::Instant;

const DEFAULT_TRACE_CAPACITY: usize = 4096;
const MAX_TRACE_CAPACITY: usize = 65_536;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct RuntimeDiagnosticsConfig {
    pub stats: bool,
    pub trace: bool,
    pub trace_capacity: usize,
}

impl Default for RuntimeDiagnosticsConfig {
    fn default() -> Self {
        Self {
            stats: false,
            trace: false,
            trace_capacity: DEFAULT_TRACE_CAPACITY,
        }
    }
}

impl RuntimeDiagnosticsConfig {
    #[cfg(test)]
    pub(crate) fn disabled() -> Self {
        Self::default()
    }

    pub(crate) fn from_env() -> Result<Self, String> {
        let stats = parse_flag("TARO_RUNTIME_STATS")?;
        let trace = parse_flag("TARO_RUNTIME_TRACE")?;
        let trace_capacity =
            parse_positive_usize("TARO_RUNTIME_TRACE_CAPACITY", DEFAULT_TRACE_CAPACITY)?;
        validate_trace_capacity(trace_capacity)?;
        Ok(Self {
            stats,
            trace,
            trace_capacity,
        })
    }
}

fn validate_trace_capacity(capacity: usize) -> Result<(), String> {
    if capacity <= MAX_TRACE_CAPACITY {
        Ok(())
    } else {
        Err(format!(
            "TARO_RUNTIME_TRACE_CAPACITY must be at most {MAX_TRACE_CAPACITY}; got `{capacity}`"
        ))
    }
}

fn parse_flag(name: &str) -> Result<bool, String> {
    let raw = match std::env::var(name) {
        Ok(raw) => raw,
        Err(VarError::NotPresent) => return Ok(false),
        Err(VarError::NotUnicode(_)) => {
            return Err(format!("{name} must contain valid Unicode"));
        }
    };
    parse_flag_value(name, Some(&raw))
}

fn parse_flag_value(name: &str, raw: Option<&str>) -> Result<bool, String> {
    let Some(raw) = raw else {
        return Ok(false);
    };
    match raw.trim().to_ascii_lowercase().as_str() {
        "1" | "true" | "yes" => Ok(true),
        "0" | "false" | "no" => Ok(false),
        _ => Err(format!(
            "{name} must be one of 1, 0, true, false, yes, or no; got `{raw}`"
        )),
    }
}

fn parse_positive_usize(name: &str, default: usize) -> Result<usize, String> {
    let raw = match std::env::var(name) {
        Ok(raw) => raw,
        Err(VarError::NotPresent) => return Ok(default),
        Err(VarError::NotUnicode(_)) => {
            return Err(format!("{name} must contain valid Unicode"));
        }
    };
    parse_positive_usize_value(name, Some(&raw), default)
}

fn parse_positive_usize_value(
    name: &str,
    raw: Option<&str>,
    default: usize,
) -> Result<usize, String> {
    let Some(raw) = raw else {
        return Ok(default);
    };
    raw.parse::<usize>()
        .ok()
        .filter(|value| *value > 0)
        .ok_or_else(|| format!("{name} must be a positive integer; got `{raw}`"))
}

pub(crate) struct RuntimeDiagnostics {
    pub stats_enabled: bool,
    trace: Option<TraceRecorder>,
}

impl RuntimeDiagnostics {
    pub(crate) fn new(config: RuntimeDiagnosticsConfig) -> Self {
        Self {
            stats_enabled: config.stats,
            trace: config
                .trace
                .then(|| TraceRecorder::new(config.trace_capacity)),
        }
    }

    #[cfg(test)]
    pub(crate) fn disabled() -> Self {
        Self::new(RuntimeDiagnosticsConfig::disabled())
    }

    #[inline]
    pub(crate) fn record(&self, event: &'static str, fields: impl FnOnce() -> String) {
        if let Some(trace) = self.trace.as_ref() {
            trace.record(event, fields());
        }
    }

    pub(crate) fn trace_report(&self, worker_count: usize) -> Option<String> {
        self.trace.as_ref().map(|trace| trace.render(worker_count))
    }

    pub(crate) fn is_enabled(&self) -> bool {
        self.stats_enabled || self.trace.is_some()
    }
}

struct TraceEvent {
    elapsed_micros: u64,
    event: &'static str,
    fields: String,
}

#[derive(Default)]
struct TraceBuffer {
    events: VecDeque<TraceEvent>,
    dropped: u64,
}

struct TraceRecorder {
    started: Instant,
    capacity: usize,
    buffer: Mutex<TraceBuffer>,
}

impl TraceRecorder {
    fn new(capacity: usize) -> Self {
        Self {
            started: Instant::now(),
            capacity,
            buffer: Mutex::new(TraceBuffer {
                events: VecDeque::with_capacity(capacity),
                dropped: 0,
            }),
        }
    }

    fn record(&self, event: &'static str, fields: String) {
        let mut buffer = self.buffer.lock().unwrap();
        if buffer.events.len() == self.capacity {
            let _ = buffer.events.pop_front();
            buffer.dropped = buffer.dropped.saturating_add(1);
        }
        let elapsed_micros = self.started.elapsed().as_micros().min(u64::MAX as u128) as u64;
        buffer.events.push_back(TraceEvent {
            elapsed_micros,
            event,
            fields,
        });
    }

    fn render(&self, worker_count: usize) -> String {
        use std::fmt::Write as _;

        let buffer = self.buffer.lock().unwrap();
        let mut output = String::new();
        let _ = writeln!(
            output,
            "runtime trace: workers={worker_count} events={} capacity={} dropped={}",
            buffer.events.len(),
            self.capacity,
            buffer.dropped
        );
        for event in &buffer.events {
            let _ = write!(
                output,
                "  t={}us event={}",
                event.elapsed_micros, event.event
            );
            if !event.fields.is_empty() {
                let _ = write!(output, " {}", event.fields);
            }
            output.push('\n');
        }
        output
    }
}

pub(crate) fn quote_field(value: &str) -> String {
    let mut output = String::with_capacity(value.len() + 2);
    output.push('"');
    for ch in value.chars() {
        match ch {
            '\\' => output.push_str("\\\\"),
            '"' => output.push_str("\\\""),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            _ => output.push(ch),
        }
    }
    output.push('"');
    output
}

#[cfg(test)]
mod tests {
    use super::{
        RuntimeDiagnostics, RuntimeDiagnosticsConfig, parse_flag_value, parse_positive_usize_value,
        quote_field, validate_trace_capacity,
    };

    #[test]
    fn diagnostic_values_are_validated() {
        for enabled in ["1", "true", "TRUE", " yes "] {
            assert_eq!(parse_flag_value("FLAG", Some(enabled)), Ok(true));
        }
        for disabled in ["0", "false", "FALSE", " no "] {
            assert_eq!(parse_flag_value("FLAG", Some(disabled)), Ok(false));
        }
        assert_eq!(parse_flag_value("FLAG", None), Ok(false));
        assert!(parse_flag_value("FLAG", Some("sometimes")).is_err());

        assert_eq!(parse_positive_usize_value("SIZE", None, 8), Ok(8));
        assert_eq!(parse_positive_usize_value("SIZE", Some("16"), 8), Ok(16));
        assert!(parse_positive_usize_value("SIZE", Some("0"), 8).is_err());
        assert!(parse_positive_usize_value("SIZE", Some("many"), 8).is_err());
        assert_eq!(validate_trace_capacity(65_536), Ok(()));
        assert!(validate_trace_capacity(65_537).is_err());
    }

    #[test]
    fn trace_ring_keeps_the_newest_events_and_reports_drops() {
        let diagnostics = RuntimeDiagnostics::new(RuntimeDiagnosticsConfig {
            stats: false,
            trace: true,
            trace_capacity: 2,
        });
        diagnostics.record("first", String::new);
        diagnostics.record("second", || "task=2".into());
        diagnostics.record("third", || "task=3".into());

        let report = diagnostics.trace_report(4).unwrap();
        assert!(report.contains("workers=4 events=2 capacity=2 dropped=1"));
        assert!(!report.contains("event=first"));
        assert!(report.contains("event=second task=2"));
        assert!(report.contains("event=third task=3"));
    }

    #[test]
    fn disabled_trace_does_not_evaluate_event_fields() {
        let diagnostics = RuntimeDiagnostics::disabled();
        let mut evaluated = false;
        diagnostics.record("disabled", || {
            evaluated = true;
            String::new()
        });
        assert!(!evaluated);
    }

    #[test]
    fn trace_fields_are_quoted_for_single_line_output() {
        assert_eq!(quote_field("a\n\"b\\c"), "\"a\\n\\\"b\\\\c\"");
    }
}
