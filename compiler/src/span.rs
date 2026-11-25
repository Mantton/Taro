use index_vec::define_index_type;

index_vec::define_index_type! {
    pub struct PackageIndex = u32;
}

define_index_type! {
    pub struct FileID = u32;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
}

impl Span {
    pub fn to(&self, span: Span) -> Span {
        assert!(self.file == span.file, "files must match");
        Span {
            start: self.start,
            end: span.end,
            file: span.file,
        }
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, serde::Serialize, serde::Deserialize)]
pub struct Position {
    /// 0-based line number.
    pub line: usize,
    /// 0-based character offset within the line (i.e. a column, not a byte
    /// offset into the file); the lexer resets it to 0 at every newline.
    pub offset: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct Spanned<T> {
    pub value: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(value: T, span: Span) -> Spanned<T> {
        Spanned { value, span }
    }
}

pub use crate::interner::{InternedBytes, Symbol};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Identifier {
    pub symbol: Symbol,
    pub span: Span,
}

impl Identifier {
    pub(crate) fn empty(file: FileID, symbols: &crate::interner::SessionInterner) -> Self {
        Identifier {
            span: Span::empty(file),
            symbol: symbols.intern(""),
        }
    }

    pub fn new(symbol: Symbol, span: Span) -> Self {
        Identifier { span, symbol }
    }
}
