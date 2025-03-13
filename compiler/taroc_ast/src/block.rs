use taroc_span::Span;

use super::statement::Statement;

#[derive(Debug)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub has_declarations: bool,
    pub span: Span,
}
