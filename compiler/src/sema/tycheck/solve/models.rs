use crate::{
    ast::Identifier,
    hir::NodeID,
    sema::{error::SpannedErrorList, models::Ty, resolve::models::DefinitionID},
    span::Span,
};

#[derive(Debug, Clone)]
pub enum Goal<'ctx> {
    Equal(Ty<'ctx>, Ty<'ctx>),
    Apply(ApplyGoalData<'ctx>),
    BindOverload(BindOverloadGoalData<'ctx>),
    Disjunction(Vec<DisjunctionBranch<'ctx>>),
}

#[derive(Debug, Clone)]
pub struct Obligation<'ctx> {
    pub location: Span,
    pub goal: Goal<'ctx>,
}

#[derive(Debug, Clone)]
pub struct DisjunctionBranch<'ctx> {
    pub goal: Goal<'ctx>,
    pub source: Option<DefinitionID>,
}

#[derive(Debug, Clone)]
pub struct BindOverloadGoalData<'ctx> {
    pub var_ty: Ty<'ctx>,
    pub candidate_ty: Ty<'ctx>,
    pub source: DefinitionID,
}

pub enum SolverResult<'ctx> {
    Deferred,
    Solved(Vec<Obligation<'ctx>>), // Solved, With Sub-Obligations
    Error(SpannedErrorList<'ctx>), // Failed, With Errors
}

#[derive(Debug, Clone)]
pub struct ApplyGoalData<'ctx> {
    pub call_span: Span,
    pub callee_ty: Ty<'ctx>,
    pub callee_source: Option<DefinitionID>,
    pub result_ty: Ty<'ctx>,
    pub expect_ty: Option<Ty<'ctx>>,
    pub arguments: Vec<ApplyArgument<'ctx>>,
}

#[derive(Debug, Clone, Copy)]
pub struct ApplyArgument<'ctx> {
    pub id: NodeID,
    pub label: Option<Identifier>,
    pub ty: Ty<'ctx>,
    pub span: Span,
}
