use taroc_span::Symbol;
use taroc_token::Base;

#[derive(Debug)]
pub enum LiteralKind {
    Bool(bool),
    Rune,
    String,
    Integer(Base),
    Float,
    Nil,
}

#[derive(Debug)]
pub struct Literal {
    pub kind: LiteralKind,
    pub content: Symbol,
}
