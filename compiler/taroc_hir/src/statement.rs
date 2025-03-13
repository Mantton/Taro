use taroc_span::{Identifier, Span};

use super::{
    NodeID, block::Block, declaration::Declaration, expression::Expression, label::Label,
    local::Local,
};

#[derive(Debug)]
pub struct Statement {
    pub id: NodeID,
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum StatementKind {
    Declaration(Declaration),
    Expression(Box<Expression>),
    Variable(Local),
    Break(Option<Identifier>),
    Continue(Option<Identifier>),
    Return(Option<Box<Expression>>),
    Loop(Option<Label>, Block),
    Defer(Block),
}

#[derive(Debug)]
pub struct LoopStatement {
    pub label: Option<Label>,
    pub block: Block,
}
