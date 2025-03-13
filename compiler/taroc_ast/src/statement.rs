use taroc_span::{Identifier, Span};

use super::{
    block::Block, declaration::Declaration, expression::Expression, label::Label, local::Local,
    pattern::BindingPattern,
};

#[derive(Debug)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum StatementKind {
    Declaration(Declaration),
    Expression(Box<Expression>), // Expression With SemiColon
    Variable(Local),
    Break(Option<Identifier>),
    Continue(Option<Identifier>),
    Return(Option<Box<Expression>>),
    Loop(LoopStatement),
    While(WhileStatement),
    For(ForStatement),
    Defer(Block),
    Guard(GuardStatement),
}

#[derive(Debug)]
pub struct LoopStatement {
    pub label: Option<Label>,
    pub block: Block,
}

#[derive(Debug)]
pub struct WhileStatement {
    pub label: Option<Label>,
    pub conditions: StatementConditionList,
    pub block: Block,
}

#[derive(Debug)]
pub struct ForStatement {
    pub label: Option<Label>,
    pub pattern: BindingPattern,
    pub iterator: Box<Expression>,
    pub clause: Option<Box<Expression>>,
    pub block: Block,
}

#[derive(Debug)]
pub struct GuardStatement {
    pub conditions: StatementConditionList,
    pub block: Block,
}

#[derive(Debug)]
pub struct StatementConditionList {
    pub conditions: Vec<Box<Expression>>,
    pub span: Span,
}
