use index_vec::define_index_type;

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
