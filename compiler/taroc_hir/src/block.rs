use super::{NodeID, statement::Statement};
use taroc_span::Span;

#[derive(Debug)]
pub struct Block {
    pub id: NodeID,
    pub statements: Vec<Statement>,
    pub has_declarations: bool,
    pub span: Span,
}
