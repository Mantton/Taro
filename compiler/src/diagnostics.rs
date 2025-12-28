use crate::{
    error::ReportedError,
    span::{FileID, Span},
};
use colored::{ColoredString, Colorize};
use ecow::EcoString;
use index_vec::IndexVec;
use rustc_hash::FxHashMap;
use std::{
    cell::{Cell, RefCell},
    fs,
    path::PathBuf,
};

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

    pub fn has_error(&self) -> bool {
        self.inner.borrow().has_error.get()
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
    pub fn emit(&self, diagnostic: Diagnostic) {
        if matches!(diagnostic.level, DiagnosticLevel::Error) {
            self.inner.borrow().has_error.set(true);
        }

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
    pub fn emit_error(&self, message: String, span: Option<Span>) {
        self.emit(Diagnostic::new(message, span, DiagnosticLevel::Error));
    }

    pub fn emit_info(&self, message: String, span: Option<Span>) {
        self.emit(Diagnostic::new(message, span, DiagnosticLevel::Info));
    }

    pub fn emit_warning(&self, message: String, span: Option<Span>) {
        self.emit(Diagnostic::new(message, span, DiagnosticLevel::Info));
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

            let aboslute_path = file.as_path();
            let relative_path = aboslute_path
                .strip_prefix(self.cwd.as_path())
                .unwrap_or(aboslute_path)
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
    file_mappings: IndexVec<FileID, PathBuf>,
    file_content_mappings: FxHashMap<FileID, EcoString>,
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

pub fn print_span_error(content: &str, span: Span, level: DiagnosticLevel) -> String {
    // Split content by lines
    let lines: Vec<&str> = content.lines().collect();

    if span.start.line > lines.len() || span.end.line > lines.len() {
        println!("{:?} {:?}", lines.len(), span.end.line);
        unreachable!("span lines are out of range for the given content");
    }

    let mut base: Vec<String> = vec![];
    // Because lines are 1-indexed in `Span`, adjust for 0-indexed `lines` array
    let start_line_index = span.start.line;
    let end_line_index = span.end.line;
    // If start and end are on the same line
    if start_line_index == end_line_index {
        let line_text = lines[start_line_index];
        base.push(format!("\t{}", line_text));

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
        base.push(format!("\t{}", level.message(caret_line)));
    } else {
        //
        // Multi-line span case
        //

        // 1) Print the start line
        let start_line_text = lines[start_line_index];
        base.push(format!("{}", start_line_text));

        // Highlight from start.offset to the end of the start line
        let mut caret_line = String::new();
        let clamped_start_offset = span.start.offset.min(start_line_text.len());
        let highlight_len = (start_line_text.len() - clamped_start_offset).max(1);

        caret_line.push_str(&" ".repeat(clamped_start_offset));
        caret_line.push_str(&"^".repeat(highlight_len));
        base.push(format!("{}", level.message(caret_line)));

        // 2) Print any lines in between without highlighting
        for line_index in (start_line_index + 1)..end_line_index {
            base.push(format!("{}", lines[line_index]));
        }

        // 3) Print the end line
        let end_line_text = if lines.len() <= end_line_index {
            lines.last().unwrap()
        } else {
            lines[end_line_index]
        };

        base.push(format!("{}", end_line_text));

        // Place a single caret at the end offset
        let clamped_end_offset = span.end.offset.min(end_line_text.len());

        let mut end_caret_line = String::new();
        end_caret_line.push_str(&" ".repeat(clamped_end_offset));
        end_caret_line.push('^');
        base.push(format!("{}", level.message(end_caret_line)));
    }

    base.join("\n")
}
