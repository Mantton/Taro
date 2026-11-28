use crate::{
    compile::source::{DiskSources, SourceProvider, SourceText},
    error::ReportedError,
    interner::SessionInterner,
    span::{FileID, Span, Symbol},
};
use colored::{ColoredString, Colorize};
use ecow::EcoString;
use index_vec::IndexVec;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    cell::{Cell, RefCell},
    panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
    path::PathBuf,
    rc::Rc,
    sync::Arc,
};
use unicode_width::UnicodeWidthChar;

pub struct DiagCtx {
    cwd: PathBuf,
    sources: Rc<dyn SourceProvider>,
    cancelled: Option<Box<dyn Fn() -> bool>>,
    /// Keep checking after reported errors; see `with_error_recovery`.
    recover_errors: bool,
    /// Recorded diagnostics a strict session would have reported before
    /// stopping, once a recovering session passes that point.
    strict_stop: Cell<Option<usize>>,
    inner: RefCell<DiagCtxInner>,
    pub(crate) symbols: Rc<SessionInterner>,
    #[cfg(test)]
    pub(crate) analysis_work: AnalysisWork,
}

struct AnalysisCancelled;

/// Catch cancellation at the boundary of one disposable analysis session.
/// Other unwinds propagate so the caller can handle a failed worker.
pub fn run_cancellable<T>(analyze: impl FnOnce() -> T) -> Option<T> {
    match catch_unwind(AssertUnwindSafe(analyze)) {
        Ok(value) => Some(value),
        Err(payload) if payload.is::<AnalysisCancelled>() => None,
        Err(payload) => resume_unwind(payload),
    }
}

/// Whether an unwind is the cancellation of an analysis session rather than
/// a compiler failure.
pub fn is_cancellation(payload: &(dyn std::any::Any + Send)) -> bool {
    payload.is::<AnalysisCancelled>()
}

/// Work counters at the pass entry points used by the full-analysis oracle.
#[cfg(test)]
#[derive(Default)]
pub(crate) struct AnalysisWork {
    pub parsed_files: Cell<usize>,
    pub summarized_files: Cell<usize>,
    pub summarized_source_bytes: Cell<usize>,
    pub collected_callable_headers: Cell<usize>,
    pub checked_function_bodies: Cell<usize>,
    pub indexed_declarations: Cell<usize>,
    pub copied_occurrences: Cell<usize>,
}

impl DiagCtx {
    pub fn new(cwd: PathBuf) -> DiagCtx {
        Self::with_sources(cwd, Rc::new(DiskSources))
    }

    /// Keep discovery, parsing and diagnostics on the same source view.
    pub fn with_sources(cwd: PathBuf, sources: Rc<dyn SourceProvider>) -> DiagCtx {
        DiagCtx {
            cwd,
            sources,
            cancelled: None,
            recover_errors: false,
            strict_stop: Cell::new(None),
            inner: RefCell::new(Default::default()),
            symbols: Rc::default(),
            #[cfg(test)]
            analysis_work: AnalysisWork::default(),
        }
    }

    pub fn sources(&self) -> &dyn SourceProvider {
        &*self.sources
    }

    /// Use only in a disposable session wrapped by `run_cancellable`.
    pub fn with_cancellation(mut self, cancelled: impl Fn() -> bool + 'static) -> Self {
        self.cancelled = Some(Box::new(cancelled));
        self
    }

    /// Let every phase run even after an earlier one reported an error, as
    /// an editor needs facts for the parts of a package that still check.
    /// Errors become `Resolution::Error` and the `<<error>>` type instead of
    /// stopping the pipeline. Never use it for a build.
    pub fn with_error_recovery(mut self) -> Self {
        self.recover_errors = true;
        self
    }

    pub fn recovers_errors(&self) -> bool {
        self.recover_errors
    }

    /// How many recorded diagnostics a strict session reports. Errors after
    /// that point may follow from the earlier ones, so editors show the
    /// command line's diagnostics and use recovery only for navigation.
    pub fn strict_diagnostic_count(&self) -> Option<usize> {
        self.strict_stop.get()
    }

    pub(crate) fn cancellation_point(&self) {
        if self.cancelled.as_ref().is_some_and(|cancelled| cancelled()) {
            // Solver frames contain partially computed types. Unwind them all
            // and release the scratch session before giving control back.
            resume_unwind(Box::new(AnalysisCancelled));
        }
    }
    pub fn add_file_mapping(&self, path: PathBuf) -> FileID {
        self.inner.borrow_mut().file_mappings.push(path)
    }

    pub fn file_path(&self, id: FileID) -> Option<PathBuf> {
        self.inner.borrow().file_mappings.get(id).cloned()
    }

    pub fn all_file_mappings(&self) -> Vec<(FileID, PathBuf)> {
        self.inner
            .borrow()
            .file_mappings
            .iter_enumerated()
            .map(|(id, path)| (id, path.clone()))
            .collect()
    }

    pub fn register_function_span(&self, body: Span, name: Symbol) {
        self.inner
            .borrow_mut()
            .functions
            .entry(body.file)
            .or_default()
            .push((body, name));
    }

    /// Lowering registers outer bodies before their nested declarations.
    pub fn enclosing_function(&self, span: Span) -> Option<Symbol> {
        let inner = self.inner.borrow();
        inner
            .functions
            .get(&span.file)?
            .iter()
            .rev()
            .find_map(|(body, name)| {
                (body.start <= span.start && span.end <= body.end).then_some(*name)
            })
    }

    pub fn has_error(&self) -> bool {
        self.inner.borrow().has_error.get()
    }

    pub fn error_count(&self) -> usize {
        self.inner.borrow().error_count.get()
    }

    /// The gate between phases: `Err` once an error was reported, unless this
    /// session recovers from errors.
    pub fn ok(&self) -> Result<(), ReportedError> {
        self.cancellation_point();
        if self.has_error() {
            self.stop()
        } else {
            Ok(())
        }
    }

    /// A phase reported an error that ends a strict session. A recovering
    /// session notes where it would have stopped and continues.
    pub fn stop(&self) -> Result<(), ReportedError> {
        if !self.recover_errors {
            return Err(ReportedError);
        }
        if self.strict_stop.get().is_none() {
            self.strict_stop
                .set(Some(self.inner.borrow().recorded.len()));
        }
        Ok(())
    }

    /// Resolve a syntactically ambiguous branch without publishing its errors.
    /// The selected branch explicitly replays its diagnostics through emit;
    /// discarded branches never affect counts, deduplication or stderr. Nested
    /// captures and unwinding restore the surrounding diagnostic context.
    pub(crate) fn with_deferred_diagnostics<T>(
        &self,
        action: impl FnOnce() -> T,
    ) -> (T, Vec<Diagnostic>) {
        let depth = self.inner.borrow().deferred.len();
        self.inner.borrow_mut().deferred.push(vec![]);
        let mut guard = DeferredDiagnostics {
            context: self,
            depth,
            active: true,
        };
        let value = action();
        let diagnostics = self
            .inner
            .borrow_mut()
            .deferred
            .pop()
            .expect("diagnostic capture");
        guard.active = false;
        (value, diagnostics)
    }
}

struct DeferredDiagnostics<'a> {
    context: &'a DiagCtx,
    depth: usize,
    active: bool,
}
impl Drop for DeferredDiagnostics<'_> {
    fn drop(&mut self) {
        if self.active {
            self.context
                .inner
                .borrow_mut()
                .deferred
                .truncate(self.depth);
        }
    }
}

impl DiagCtx {
    pub fn record_source(&self, file: FileID, source: Arc<SourceText>) {
        self.inner
            .borrow_mut()
            .file_content_mappings
            .insert(file, source);
    }

    /// Translate the compiler's scalar endpoints using this file's line index.
    pub fn source_text(&self, span: Span) -> Option<EcoString> {
        let text = self.get_file_content(span.file)?;
        let start = text.byte_offset(span.start)?;
        let end = text.byte_offset(span.end)?;
        Some(text.text().get(start..end)?.into())
    }

    pub(crate) fn get_file_content(&self, id: FileID) -> Option<Arc<SourceText>> {
        if let Some(stored) = self.inner.borrow().file_content_mappings.get(&id) {
            return Some(Arc::clone(stored));
        }
        let path = self.file_path(id)?;
        let content = self.sources.read_text(&path).ok()?;
        self.record_source(id, Arc::clone(&content));
        Some(content)
    }
}

impl DiagCtx {
    fn dedup_key(diagnostic: &Diagnostic) -> String {
        if let Some(span) = diagnostic.span {
            format!(
                "{:?}|{}|{}|{}:{}|{}:{}",
                diagnostic.level,
                diagnostic.message,
                span.file.raw(),
                span.start.line,
                span.start.offset,
                span.end.line,
                span.end.offset
            )
        } else {
            format!("{:?}|{}|<no-span>", diagnostic.level, diagnostic.message)
        }
    }

    pub fn emit(&self, diagnostic: Diagnostic) {
        let mut inner = self.inner.borrow_mut();
        if let Some(buffer) = inner.deferred.last_mut() {
            buffer.push(diagnostic);
            return;
        }
        let key = Self::dedup_key(&diagnostic);

        // Avoid emitting the exact same diagnostic multiple times. Include the
        // severity in the key so a warning upgraded to an error is retained.
        if !inner.emitted_diagnostic_keys.insert(key) {
            return;
        }

        if matches!(diagnostic.level, DiagnosticLevel::Error) {
            inner.has_error.set(true);
            let count = inner.error_count.get();
            inner.error_count.set(count + 1);
        }
        if matches!(diagnostic.level, DiagnosticLevel::Warn) {
            inner.warnings.push((
                diagnostic.message.clone(),
                diagnostic.span,
                diagnostic.suggestion.clone(),
            ));
        }
        if let Some(suggestion) = &diagnostic.suggestion {
            inner.suggestions.push(suggestion.clone());
        }
        drop(inner);

        let recording = self.inner.borrow().recording;
        if recording {
            self.inner.borrow_mut().recorded.push(diagnostic);
        } else {
            if let Some(message) = self.format(&diagnostic, false) {
                eprintln!("{}", message);
                if let Some(suggestion) = &diagnostic.suggestion {
                    eprintln!("help: {}", suggestion.message);
                }
                for note in &diagnostic.children {
                    if let Some(m) = self.format(&note, false) {
                        eprintln!("{}", m);
                    }
                }
            } else {
                println!("no msg?")
            }
        }
    }
    pub fn emit_error(&self, message: String, span: Option<Span>) {
        self.emit(Diagnostic::new(message, span, DiagnosticLevel::Error));
    }

    pub fn emit_info(&self, message: String, span: Option<Span>) {
        self.emit(Diagnostic::new(message, span, DiagnosticLevel::Info));
    }

    pub fn emit_warning(&self, message: String, span: Option<Span>) {
        self.emit(Diagnostic::new(message, span, DiagnosticLevel::Warn));
    }

    pub fn emit_warning_with_suggestion(
        &self,
        message: String,
        span: Option<Span>,
        suggestion: Option<Suggestion>,
    ) {
        let mut diag = Diagnostic::new(message, span, DiagnosticLevel::Warn);
        diag.suggestion = suggestion;
        self.emit(diag);
    }

    pub fn suggestions(&self) -> Vec<Suggestion> {
        self.inner.borrow().suggestions.clone()
    }

    pub fn machine_applicable_suggestions(&self) -> Vec<Suggestion> {
        self.inner
            .borrow()
            .suggestions
            .iter()
            .filter(|s| s.applicability == Applicability::MachineApplicable)
            .cloned()
            .collect()
    }

    /// The number of warnings emitted so far; a mark for `warnings_since`.
    pub fn warning_count(&self) -> usize {
        self.inner.borrow().warnings.len()
    }

    /// The warnings emitted after `mark`, in order.
    pub fn warnings_since(&self, mark: usize) -> Vec<(String, Option<Span>)> {
        self.inner
            .borrow()
            .warnings
            .get(mark..)
            .map(|slice| {
                slice
                    .iter()
                    .map(|(msg, span, _)| (msg.clone(), *span))
                    .collect()
            })
            .unwrap_or_default()
    }

    /// The warnings and optional fix suggestions emitted after `mark`, in order.
    pub fn warnings_with_suggestions_since(
        &self,
        mark: usize,
    ) -> Vec<(String, Option<Span>, Option<Suggestion>)> {
        self.inner
            .borrow()
            .warnings
            .get(mark..)
            .map(<[_]>::to_vec)
            .unwrap_or_default()
    }
}

impl DiagCtx {
    pub fn format(&self, diag: &Diagnostic, is_note: bool) -> Option<String> {
        if let Some(span) = diag.span {
            let file_id = span.file;
            let file = { self.inner.borrow().file_mappings.get(file_id).cloned() };
            let Some(file) = file else {
                println!("Unable to locate file with id – '{}'", file_id.raw());
                return None;
            };

            let absolute_path = file.as_path();
            let relative_path = absolute_path
                .strip_prefix(self.cwd.as_path())
                .unwrap_or(absolute_path)
                .to_string_lossy();

            let mut message = format!(
                "\n{}: {}\n -> {}:{}:{}\n",
                if is_note {
                    "note".into()
                } else {
                    diag.level.to_string()
                },
                diag.message.as_str().bold(),
                relative_path,
                span.start.line + 1,
                span.start.offset,
            );

            if let Some(content) = self.get_file_content(span.file) {
                message.push_str(&print_span_error(content.text(), span, diag.level));
            }

            Some(message)
        } else {
            let message = format!(
                "\n{}: {}\n",
                if is_note {
                    "note".into()
                } else {
                    diag.level.to_string()
                },
                diag.message.as_str().bold(),
            );

            Some(message)
        }
    }
}

#[derive(Default)]
struct DiagCtxInner {
    has_error: Cell<bool>,
    error_count: Cell<usize>,
    functions: FxHashMap<FileID, Vec<(Span, Symbol)>>,
    file_mappings: IndexVec<FileID, PathBuf>,
    file_content_mappings: FxHashMap<FileID, Arc<SourceText>>,
    emitted_diagnostic_keys: FxHashSet<String>,
    recording: bool,
    recorded: Vec<Diagnostic>,
    deferred: Vec<Vec<Diagnostic>>,
    /// Every warning emitted, in order, so a package's warnings can be stored
    /// with its cached metadata and replayed when the cache is reused.
    warnings: Vec<(String, Option<Span>, Option<Suggestion>)>,
    suggestions: Vec<Suggestion>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Applicability {
    /// Safe to apply automatically with `taro fix`.
    MachineApplicable,
    /// Advisory replacement for humans; never applied automatically.
    MaybeIncorrect,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Suggestion {
    pub message: String,
    pub span: Span,
    pub replacement: String,
    pub applicability: Applicability,
}

#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub message: String,
    pub code: Option<usize>,
    pub level: DiagnosticLevel,
    pub span: Option<Span>,
    pub children: Vec<Diagnostic>,
    pub suggestion: Option<Suggestion>,
}

/// Both syntactic readings of a member bracket suffix are resolved, but only
/// semantic member selection may publish the chosen branch's diagnostics.
#[derive(Debug, Clone, Default)]
pub struct BracketDiagnostics {
    pub types: Vec<Diagnostic>,
    pub index: Vec<Diagnostic>,
}

impl Diagnostic {
    pub fn new(message: String, span: Option<Span>, level: DiagnosticLevel) -> Diagnostic {
        Diagnostic {
            message,
            code: None,
            level,
            span,
            children: vec![],
            suggestion: None,
        }
    }

    pub fn error(message: String, span: Option<Span>) -> Diagnostic {
        Diagnostic::new(message, span, DiagnosticLevel::Error)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum DiagnosticLevel {
    Warn,
    Info,
    Error,
}

impl DiagnosticLevel {
    fn message(&self, str: String) -> ColoredString {
        match self {
            DiagnosticLevel::Warn => str.yellow().bold(),
            DiagnosticLevel::Info => str.cyan().bold(),
            DiagnosticLevel::Error => str.red().bold(),
        }
    }
}

impl std::fmt::Display for DiagnosticLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            DiagnosticLevel::Warn => "warning".yellow().bold(),
            DiagnosticLevel::Info => "info".cyan().bold(),
            DiagnosticLevel::Error => "error".red().bold(),
        };
        write!(f, "{}", str)
    }
}

impl DiagCtx {
    pub fn enable_recording(&self) {
        self.inner.borrow_mut().recording = true;
    }

    pub fn take_recorded_diagnostics(&self) -> Vec<Diagnostic> {
        std::mem::take(&mut self.inner.borrow_mut().recorded)
    }
}

pub fn print_span_error(content: &str, span: Span, level: DiagnosticLevel) -> String {
    // `split('\n')` preserves an empty final line, which lets EOF spans in a
    // newline-terminated or empty file render without special casing.
    let lines: Vec<&str> = content
        .split('\n')
        .map(|line| line.strip_suffix('\r').unwrap_or(line))
        .collect();

    if span.start.line >= lines.len()
        || span.end.line >= lines.len()
        || span.start.line > span.end.line
        || (span.start.line == span.end.line && span.start.offset > span.end.offset)
    {
        return format!(
            "\t<source unavailable for span {}:{} to {}:{}>",
            span.start.line + 1,
            span.start.offset + 1,
            span.end.line + 1,
            span.end.offset + 1,
        );
    }

    let mut base: Vec<String> = vec![];
    // Span line indices and the source line array are both 0-based.
    let start_line_index = span.start.line;
    let end_line_index = span.end.line;
    // If start and end are on the same line
    if start_line_index == end_line_index {
        let line_text = lines[start_line_index];
        base.push(format!("\t{}", line_text));

        // Span columns are character offsets, while `str::len` is bytes. Work
        // in characters and convert to terminal display columns only when
        // constructing the caret line.
        let line_chars = line_text.chars().count();
        let clamped_start_offset = span.start.offset.min(line_chars);
        let clamped_end_offset = span.end.offset.min(line_chars);

        // Minimum highlight length is 1 caret
        let highlight_len =
            display_width_between(line_text, clamped_start_offset, clamped_end_offset).max(1);

        // Build a caret line (spaces + ^^^^)
        let mut caret_line = caret_prefix(line_text, clamped_start_offset);
        caret_line.push_str(&"^".repeat(highlight_len));

        // Print in red
        base.push(format!("\t{}", level.message(caret_line)));
    } else {
        //
        // Multi-line span case
        //

        // 1) Print the start line
        let start_line_text = lines[start_line_index];
        base.push(format!("{}", start_line_text));

        // Highlight from start.offset to the end of the start line
        let start_line_chars = start_line_text.chars().count();
        let clamped_start_offset = span.start.offset.min(start_line_chars);
        let highlight_len =
            display_width_between(start_line_text, clamped_start_offset, start_line_chars).max(1);

        let mut caret_line = caret_prefix(start_line_text, clamped_start_offset);
        caret_line.push_str(&"^".repeat(highlight_len));
        base.push(format!("{}", level.message(caret_line)));

        // 2) Print any lines in between without highlighting
        for line_index in (start_line_index + 1)..end_line_index {
            base.push(format!("{}", lines[line_index]));
        }

        // 3) Print the end line
        let end_line_text = lines[end_line_index];

        base.push(format!("{}", end_line_text));

        // Place a single caret at the end offset
        let clamped_end_offset = span.end.offset.min(end_line_text.chars().count());

        let mut end_caret_line = caret_prefix(end_line_text, clamped_end_offset);
        end_caret_line.push('^');
        base.push(format!("{}", level.message(end_caret_line)));
    }

    base.join("\n")
}

fn caret_prefix(line: &str, character_offset: usize) -> String {
    let mut prefix = String::new();
    for character in line.chars().take(character_offset) {
        if character == '\t' {
            // Retaining tabs lets the terminal apply the same tab stops as it
            // did for the source line.
            prefix.push('\t');
        } else {
            prefix.push_str(&" ".repeat(character.width().unwrap_or(1)));
        }
    }
    prefix
}

fn display_width_between(line: &str, start: usize, end: usize) -> usize {
    line.chars()
        .skip(start)
        .take(end.saturating_sub(start))
        .map(|character| character.width().unwrap_or(1))
        .sum()
}

#[cfg(test)]
mod tests {
    use super::{DiagnosticLevel, caret_prefix, display_width_between, print_span_error};
    use crate::span::{FileID, Position, Span};

    #[test]
    fn cancellation_drops_scratch_and_other_panics_propagate() {
        use super::{DiagCtx, run_cancellable};
        use std::{
            cell::RefCell,
            panic::{AssertUnwindSafe, catch_unwind, resume_unwind},
            rc::Rc,
        };

        let symbols = RefCell::new(None);
        let cancelled = run_cancellable(|| {
            let diagnostics = DiagCtx::new(std::env::temp_dir()).with_cancellation(|| true);
            symbols.replace(Some(Rc::downgrade(&diagnostics.symbols)));
            assert!(diagnostics.ok().is_ok());
        });
        assert_eq!(cancelled, None);
        assert!(symbols.into_inner().unwrap().upgrade().is_none());
        assert_eq!(run_cancellable(|| 42), Some(42));

        let panic = catch_unwind(AssertUnwindSafe(|| {
            run_cancellable(|| resume_unwind(Box::new("unexpected worker failure")));
        }))
        .unwrap_err();
        assert_eq!(
            panic.downcast_ref::<&str>(),
            Some(&"unexpected worker failure")
        );
    }

    #[test]
    fn warnings_since_a_mark_are_the_later_distinct_warnings() {
        let context = super::DiagCtx::new(std::path::PathBuf::from("."));
        context.enable_recording();
        context.emit_warning("earlier".into(), None);
        let mark = context.warning_count();
        context.emit_error("not a warning".into(), None);
        context.emit_warning("later".into(), None);
        context.emit_warning("later".into(), None);
        let (_, discarded) =
            context.with_deferred_diagnostics(|| context.emit_warning("discarded".into(), None));
        assert_eq!(discarded.len(), 1);
        assert_eq!(
            context.warnings_since(mark),
            vec![("later".to_string(), None)]
        );
        assert!(context.warnings_since(mark + 5).is_empty());
    }

    #[test]
    fn deferred_diagnostics_commit_only_the_selected_branch_and_restore_after_panic() {
        let context = super::DiagCtx::new(std::path::PathBuf::from("."));
        context.enable_recording();
        let (_, discarded) =
            context.with_deferred_diagnostics(|| context.emit_error("discarded".into(), None));
        assert_eq!(discarded.len(), 1);
        assert_eq!(context.error_count(), 0);
        assert!(!context.has_error());
        assert!(context.take_recorded_diagnostics().is_empty());
        let (_, selected) = context.with_deferred_diagnostics(|| {
            context.emit_error("selected".into(), None);
            let (_, nested) =
                context.with_deferred_diagnostics(|| context.emit_warning("nested".into(), None));
            for diagnostic in nested {
                context.emit(diagnostic);
            }
        });
        assert_eq!(selected.len(), 2);
        assert_eq!(context.error_count(), 0);
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            context.with_deferred_diagnostics(|| {
                context.emit_error("unwound".into(), None);
                panic!("discard speculative branch");
            });
        }));
        assert!(panic.is_err());
        for diagnostic in selected {
            context.emit(diagnostic);
        }
        context.emit_error("selected".into(), None);
        assert_eq!(
            context.error_count(),
            1,
            "only committed errors count and deduplicate"
        );
        let records = context.take_recorded_diagnostics();
        assert_eq!(
            records
                .iter()
                .map(|record| record.message.as_str())
                .collect::<Vec<_>>(),
            ["selected", "nested"]
        );
    }

    fn span(start: (usize, usize), end: (usize, usize)) -> Span {
        Span {
            start: Position {
                line: start.0,
                offset: start.1,
            },
            end: Position {
                line: end.0,
                offset: end.1,
            },
            file: FileID::from_raw(0),
        }
    }

    #[test]
    fn caret_columns_use_unicode_display_width() {
        assert_eq!(caret_prefix("a猫b", 2), "   ");
        assert_eq!(display_width_between("a猫b", 1, 2), 2);
    }

    #[test]
    fn eof_span_in_empty_content_is_renderable() {
        let rendered = print_span_error("", span((0, 0), (0, 0)), DiagnosticLevel::Error);
        assert!(rendered.contains('^'), "{rendered}");
    }

    #[test]
    fn stale_span_returns_fallback_instead_of_panicking() {
        let rendered = print_span_error("one line", span((4, 0), (4, 1)), DiagnosticLevel::Error);
        assert!(
            rendered.contains("source unavailable for span"),
            "{rendered}"
        );
    }

    #[test]
    fn reversed_span_returns_fallback_instead_of_panicking() {
        let rendered = print_span_error("text", span((0, 3), (0, 1)), DiagnosticLevel::Error);
        assert!(
            rendered.contains("source unavailable for span"),
            "{rendered}"
        );
    }
}
