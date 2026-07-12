use crate::{
    error::ReportedError,
    span::{FileID, Span},
};
use colored::{ColoredString, Colorize};
use ecow::EcoString;
use index_vec::IndexVec;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{
    cell::{Cell, RefCell},
    fs,
    path::{Path, PathBuf},
};
use unicode_width::UnicodeWidthChar;

pub struct DiagCtx {
    cwd: PathBuf,
    inner: RefCell<DiagCtxInner>,
}

impl DiagCtx {
    pub fn new(cwd: PathBuf) -> DiagCtx {
        DiagCtx {
            cwd,
            inner: RefCell::new(Default::default()),
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

    pub fn has_error(&self) -> bool {
        self.inner.borrow().has_error.get()
    }

    pub fn error_count(&self) -> usize {
        self.inner.borrow().error_count.get()
    }

    pub fn ok(&self) -> Result<(), ReportedError> {
        if self.has_error() {
            return Err(ReportedError);
        } else {
            Ok(())
        }
    }
}

impl DiagCtx {
    fn get_file_content(&self, id: FileID) -> Option<EcoString> {
        let stored = { self.inner.borrow().file_content_mappings.get(&id).cloned() };

        if stored.is_some() {
            return stored;
        }

        let file = { self.inner.borrow().file_mappings.get(id).cloned() };
        let Some(file) = file else { return None };
        let content: Option<EcoString> = fs::read_to_string(file).ok().and_then(|f| Some(f.into()));

        if let Some(content) = &content {
            self.inner
                .borrow_mut()
                .file_content_mappings
                .insert(id, content.clone());
        }

        content
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
        let key = Self::dedup_key(&diagnostic);
        let mut inner = self.inner.borrow_mut();

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
        drop(inner);

        let recording = self.inner.borrow().recording;
        if recording {
            let related_info = diagnostic
                .children
                .iter()
                .map(|child| RelatedDiagnosticInfo {
                    message: child.message.clone(),
                    span: child.span,
                })
                .collect();
            self.inner.borrow_mut().recorded.push(DiagnosticRecord {
                message: diagnostic.message.clone(),
                span: diagnostic.span,
                level: diagnostic.level,
                code: diagnostic.code,
                stage: DiagnosticStage::General,
                related_info,
            });
        } else {
            if let Some(message) = self.format(&diagnostic, false) {
                eprintln!("{}", message);
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
                message.push_str(&print_span_error(&content, span, diag.level));
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
    file_mappings: IndexVec<FileID, PathBuf>,
    file_content_mappings: FxHashMap<FileID, EcoString>,
    emitted_diagnostic_keys: FxHashSet<String>,
    content_overrides: FxHashMap<PathBuf, String>,
    recording: bool,
    recorded: Vec<DiagnosticRecord>,
}

pub struct Diagnostic {
    pub message: String,
    pub code: Option<usize>,
    pub level: DiagnosticLevel,
    pub span: Option<Span>,
    pub children: Vec<Diagnostic>,
}

impl Diagnostic {
    pub fn new(message: String, span: Option<Span>, level: DiagnosticLevel) -> Diagnostic {
        Diagnostic {
            message,
            code: None,
            level,
            span,
            children: vec![],
        }
    }

    pub fn error(message: String, span: Option<Span>) -> Diagnostic {
        Diagnostic::new(message, span, DiagnosticLevel::Error)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

// --- IDE diagnostic types ---

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticStage {
    Parse,
    Resolve,
    Typecheck,
    PostTypecheck,
    Thir,
    Mir,
    Entry,
    General,
}

#[derive(Debug, Clone)]
pub struct RelatedDiagnosticInfo {
    pub message: String,
    pub span: Option<Span>,
}

#[derive(Debug, Clone)]
pub struct DiagnosticRecord {
    pub message: String,
    pub span: Option<Span>,
    pub level: DiagnosticLevel,
    pub code: Option<usize>,
    pub stage: DiagnosticStage,
    pub related_info: Vec<RelatedDiagnosticInfo>,
}

// --- Recording & content override methods ---

impl DiagCtx {
    pub fn enable_recording(&self) {
        self.inner.borrow_mut().recording = true;
    }

    pub fn take_recorded_diagnostics(&self) -> Vec<DiagnosticRecord> {
        std::mem::take(&mut self.inner.borrow_mut().recorded)
    }

    pub fn set_content_override(&self, path: PathBuf, content: String) {
        self.inner
            .borrow_mut()
            .content_overrides
            .insert(path, content);
    }

    pub fn content_override(&self, path: &Path) -> Option<String> {
        self.inner.borrow().content_overrides.get(path).cloned()
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
