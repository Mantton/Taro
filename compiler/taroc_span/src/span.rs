use super::FileID;
use std::fmt::Display;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: Position,
    pub end: Position,
    pub file: FileID,
}

impl Span {
    pub fn empty(file: FileID) -> Span {
        Span {
            start: Position::default(),
            end: Position::default(),
            file,
        }
    }

    pub fn module() -> Span {
        Span {
            start: Position::default(),
            end: Position::default(),
            file: FileID::new(0),
        }
    }
}

impl Span {
    pub fn to(&self, span: Span) -> Span {
        assert!(span.file == span.file, "files must match");
        Span {
            start: self.start,
            end: span.end,
            file: span.file,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct Position {
    pub line: usize,
    pub offset: usize,
}

impl Position {
    pub fn to(&self, end: Position, file: FileID) -> Span {
        Span {
            start: *self,
            end,
            file,
        }
    }
}

#[derive(Debug)]
pub struct SpannedMessage {
    pub message: String,
    pub span: Span,
}

impl SpannedMessage {
    pub fn new(message: String, span: Span) -> Self {
        Self { message, span }
    }
}

impl Display for SpannedMessage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Spanned<Value> {
    pub span: Span,
    pub value: Value,
}

impl<Value> Spanned<Value> {
    pub fn new(value: Value, span: Span) -> Self {
        Self { span, value }
    }
}
