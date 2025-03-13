use colored::{ColoredString, Colorize};
use std::{cell::RefCell, fmt::Display, path::PathBuf};
use taroc_error::{CompileError, CompileResult};
use taroc_span::{Span, with_session_globals};

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

impl Display for DiagnosticLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            DiagnosticLevel::Warn => "warning".yellow().bold(),
            DiagnosticLevel::Info => "info".cyan().bold(),
            DiagnosticLevel::Error => "error".red().bold(),
        };
        write!(f, "{}", str)
    }
}

pub struct Diagnostic {
    message: String,
    span: Span,
    level: DiagnosticLevel,
    note: Option<String>,
}

impl Diagnostic {
    pub fn new(message: String, span: Span, level: DiagnosticLevel) -> Self {
        Self {
            message,
            span,
            level,
            note: None,
        }
    }
    pub fn new_with_note(
        message: String,
        span: Span,
        level: DiagnosticLevel,
        note: String,
    ) -> Self {
        Self {
            message,
            span,
            level,
            note: Some(note),
        }
    }
}

#[derive(Default)]
pub struct DiagnosticContext {
    errors: RefCell<bool>,
    cwd: PathBuf,
}

impl DiagnosticContext {
    pub fn new(cwd: PathBuf) -> DiagnosticContext {
        Self {
            errors: RefCell::new(false),
            cwd,
        }
    }

    pub fn message(&self, message: String, span: Span, level: DiagnosticLevel) {
        let diagnostic = Diagnostic::new(message, span, level);
        if level == DiagnosticLevel::Error {
            *self.errors.borrow_mut() = true;
        }
        self.emit_diagnostic(diagnostic)
    }

    pub fn info(&self, message: String, span: Span) {
        self.message(message, span, DiagnosticLevel::Info);
    }
    pub fn warn(&self, message: String, span: Span) {
        self.message(message, span, DiagnosticLevel::Warn);
    }
    pub fn error(&self, message: String, span: Span) {
        self.message(message, span, DiagnosticLevel::Error);
    }

    pub fn has_errors(&self) -> bool {
        *self.errors.borrow()
    }

    pub fn report(&self) -> CompileResult<()> {
        if self.has_errors() {
            return Err(CompileError::Reported);
        }

        return Ok(());
    }

    pub fn reset_errors(&self) {
        *self.errors.borrow_mut() = false;
    }
}

impl DiagnosticContext {
    fn emit_diagnostic(&self, entry: Diagnostic) {
        let file = with_session_globals(|session| session.get_file(entry.span.file));

        let Ok(content) = file.content() else {
            eprintln!("Failed to Read File Content");
            return;
        };

        let aboslute_path = file.path().as_path();
        let relative_path = aboslute_path
            .strip_prefix(self.cwd.as_path())
            .unwrap_or(aboslute_path)
            .to_string_lossy();

        eprintln!(
            "\n{}: {}\n -> {}:{}:{}\n",
            entry.level,
            entry.message.as_str().bold(),
            relative_path,
            entry.span.start.line + 1,
            entry.span.start.offset,
        );

        print_span_error(&content, &entry.span, entry.level);
        if let Some(_) = entry.note {
            todo!("notes")
        }
    }
}

pub fn print_span_error(content: &str, span: &Span, level: DiagnosticLevel) {
    // Split content by lines
    let lines: Vec<&str> = content.lines().collect();

    if span.start.line > lines.len() || span.end.line > lines.len() {
        println!("{:?} {:?}", lines.len(), span.end.line);
        unreachable!("span lines are out of range for the given content");
    }

    // Because lines are 1-indexed in `Span`, adjust for 0-indexed `lines` array
    let start_line_index = span.start.line;
    let end_line_index = span.end.line;
    // If start and end are on the same line
    if start_line_index == end_line_index {
        let line_text = lines[start_line_index];
        eprintln!("\t{}", line_text);

        // Clamp offsets if they're out of line range
        let clamped_start_offset = span.start.offset.min(line_text.len());
        let clamped_end_offset = span.end.offset.min(line_text.len());

        // Minimum highlight length is 1 caret
        let highlight_len = (clamped_end_offset - clamped_start_offset).max(1);

        // Build a caret line (spaces + ^^^^)
        let mut caret_line = String::new();
        caret_line.push_str(&" ".repeat(clamped_start_offset));
        caret_line.push_str(&"^".repeat(highlight_len));

        // Print in red
        eprintln!("\t{}", level.message(caret_line));
    } else {
        //
        // Multi-line span case
        //

        // 1) Print the start line
        let start_line_text = lines[start_line_index];
        eprintln!("{}", start_line_text);

        // Highlight from start.offset to the end of the start line
        let mut caret_line = String::new();
        let clamped_start_offset = span.start.offset.min(start_line_text.len());
        let highlight_len = (start_line_text.len() - clamped_start_offset).max(1);

        caret_line.push_str(&" ".repeat(clamped_start_offset));
        caret_line.push_str(&"^".repeat(highlight_len));
        eprintln!("{}", level.message(caret_line));

        // 2) Print any lines in between without highlighting
        for line_index in (start_line_index + 1)..end_line_index {
            eprintln!("{}", lines[line_index]);
        }

        // 3) Print the end line
        let end_line_text = if lines.len() <= end_line_index {
            lines.last().unwrap()
        } else {
            lines[end_line_index]
        };

        eprintln!("{}", end_line_text);

        // Place a single caret at the end offset
        let clamped_end_offset = span.end.offset.min(end_line_text.len());

        let mut end_caret_line = String::new();
        end_caret_line.push_str(&" ".repeat(clamped_end_offset));
        end_caret_line.push('^');
        eprintln!("{}", level.message(end_caret_line));
    }
}
