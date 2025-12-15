use crate::{
    ast::Identifier,
    hir::{BinaryOperator, NodeID, UnaryOperator},
    sema::{error::SpannedErrorList, models::Ty, resolve::models::DefinitionID},
    span::Span,
};

#[derive(Debug, Clone)]
pub enum Adjustment<'ctx> {
    /// Apply a single autoderef step (e.g. from `&T` to `T`).
    Dereference,
    BorrowMutable,
    BorrowImmutable,
    Ignore(&'ctx ()),
}

#[derive(Debug, Clone)]
pub enum Goal<'ctx> {
    Equal(Ty<'ctx>, Ty<'ctx>),
    Apply(ApplyGoalData<'ctx>),
    BindOverload(BindOverloadGoalData<'ctx>),
    Disjunction(Vec<DisjunctionBranch<'ctx>>),
    BinaryOp(BinOpGoalData<'ctx>),
    UnaryOp(UnOpGoalData<'ctx>),
    Coerce { from: Ty<'ctx>, to: Ty<'ctx> },
    Member(MemberGoalData<'ctx>),
    MethodCall(MethodCallData<'ctx>),
    StructLiteral(StructLiteralGoalData<'ctx>),
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

#[derive(Debug, Clone)]
pub struct MemberGoalData<'ctx> {
    pub node_id: NodeID,
    pub receiver: Ty<'ctx>,
    pub name: Identifier,
    pub result: Ty<'ctx>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct MethodCallData<'ctx> {
    pub node_id: NodeID,
    pub receiver: Ty<'ctx>,
    pub reciever_span: Span,
    pub reciever_node: NodeID,
    pub name: Identifier,
    pub arguments: Vec<ApplyArgument<'ctx>>,
    pub result: Ty<'ctx>,
    pub method_ty: Ty<'ctx>,
    pub expect_ty: Option<Ty<'ctx>>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy)]
pub struct ApplyArgument<'ctx> {
    pub id: NodeID,
    pub label: Option<Identifier>,
    pub ty: Ty<'ctx>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnOpGoalData<'ctx> {
    pub lhs: Ty<'ctx>,
    pub rho: Ty<'ctx>,
    pub expectation: Option<Ty<'ctx>>,
    pub operator: UnaryOperator,
    pub span: Span,
    pub node_id: NodeID,
    pub rhs_id: NodeID,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BinOpGoalData<'ctx> {
    pub lhs: Ty<'ctx>,
    pub rhs: Ty<'ctx>,
    pub rho: Ty<'ctx>,
    pub expectation: Option<Ty<'ctx>>,
    pub operator: BinaryOperator,
    pub span: Span,
    pub assigning: bool,
}

#[derive(Debug, Clone)]
pub struct StructLiteralGoalData<'ctx> {
    pub ty_span: Span,
    pub span: Span,
    pub struct_ty: Ty<'ctx>,
    pub fields: Vec<StructLiteralField<'ctx>>,
}

#[derive(Debug, Clone, Copy)]
pub struct StructLiteralField<'ctx> {
    pub name: crate::span::Symbol,
    pub ty: Ty<'ctx>,
    pub value_span: Span,
    pub label_span: Span,
}
