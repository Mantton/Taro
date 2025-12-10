use crate::{
    ast::Identifier,
    hir::NodeID,
    sema::models::{CalleeOrigin, Ty},
    span::Span,
};

mod apply;
mod constraint;
mod context;
mod solver;
mod unify;

#[derive(Debug, Clone)]
pub enum Goal<'ctx> {
    Equal(Ty<'ctx>, Ty<'ctx>),
    Apply(ApplicationGoal<'ctx>),
}

#[derive(Debug, Clone)]
pub struct Obligation<'ctx> {
    pub location: Span,
    pub goal: Goal<'ctx>,
}

pub use context::ObligationCtx;

#[derive(Debug, Clone)]
pub struct ApplicationGoal<'ctx> {
    pub callee_ty: Ty<'ctx>,
    pub caller_span: Span,
    pub callee_origin: Option<CalleeOrigin>,
    pub call_id: NodeID,
    pub callee_id: NodeID,
    pub arguments: Vec<ApplicationArgument<'ctx>>,
    pub result: Ty<'ctx>,
    pub expected: Option<Ty<'ctx>>,
}

#[derive(Debug, Clone, Copy)]
pub struct ApplicationArgument<'ctx> {
    pub id: NodeID,
    pub label: Option<Identifier>,
    pub ty: Ty<'ctx>,
    pub span: Span,
}
