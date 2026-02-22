use index_vec::define_index_type;
use internment::Intern;
use std::fmt;

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
        assert!(span.file == span.file, "files must match");
        Span {
            start: self.start,
            end: span.end,
            file: span.file,
        }
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Position {
    pub line: usize,
    #[allow(unused)]
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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(Intern<String>);

impl Default for Symbol {
    fn default() -> Self {
        Self::empty()
    }
}

impl Symbol {
    pub fn empty() -> Symbol {
        Symbol(Intern::new(String::new()))
    }

    pub fn new(value: &str) -> Symbol {
        Symbol(Intern::new(value.to_owned()))
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl From<&str> for Symbol {
    fn from(value: &str) -> Self {
        Symbol::new(value)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Identifier {
    pub symbol: Symbol,
    pub span: Span,
}

impl Identifier {
    pub fn emtpy(file: FileID) -> Self {
        Identifier {
            span: Span::empty(file),
            symbol: Symbol::empty(),
        }
    }

    pub fn new(symbol: Symbol, span: Span) -> Self {
        Identifier { span, symbol }
    }
}
