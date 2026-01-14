use crate::{
    ast::Identifier,
    hir::{BinaryOperator, NodeID, UnaryOperator},
    sema::{
        error::SpannedErrorList,
        models::{GenericArguments, InterfaceReference, Ty},
        resolve::models::DefinitionID,
    },
    span::Span,
};

#[derive(Debug, Clone)]
pub enum Adjustment<'ctx> {
    Dereference,
    BorrowMutable,
    BorrowImmutable,
    BoxExistential {
        from: Ty<'ctx>,
        interfaces: &'ctx [InterfaceReference<'ctx>],
    },
    ExistentialUpcast {
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    },
    /// Wrap value in Optional: some(value) if is_some=true, none if is_some=false
    OptionalWrap {
        is_some: bool,
        generic_args: GenericArguments<'ctx>,
    },
    /// Coerce a non-capturing closure to a function pointer
    ClosureToFnPointer {
        closure_def_id: DefinitionID,
    },
    Ignore(&'ctx ()),
}

#[derive(Debug, Clone)]
pub enum Goal<'ctx> {
    Equal(Ty<'ctx>, Ty<'ctx>),
    ConstraintEqual(Ty<'ctx>, Ty<'ctx>),
    Conforms {
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    },
    Apply(ApplyGoalData<'ctx>),
    BindOverload(BindOverloadGoalData<'ctx>),
    BindInterfaceMethod(BindInterfaceMethodGoalData<'ctx>),
    /// Binds a method overload with associated receiver adjustments.
    /// Used when multiple overloads with different receiver mutabilities exist.
    BindMethodOverload(BindMethodOverloadGoalData<'ctx>),
    Disjunction(Vec<DisjunctionBranch<'ctx>>),
    BinaryOp(BinOpGoalData<'ctx>),
    UnaryOp(UnOpGoalData<'ctx>),
    AssignOp(AssignOpGoalData<'ctx>),
    Coerce {
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
    },
    Cast {
        node_id: NodeID,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
        is_unsafe: bool,
    },
    Member(MemberGoalData<'ctx>),
    InferredStaticMember(InferredStaticMemberGoalData<'ctx>),
    MethodCall(MethodCallData<'ctx>),
    StructLiteral(StructLiteralGoalData<'ctx>),
    TupleAccess(TupleAccessGoalData<'ctx>),
    Deref(DerefGoalData<'ctx>),
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
    /// Cost of auto-reference applied to reach this candidate.
    /// Lower is better: None=0, Immutable=1, Mutable=2.
    /// Used for ranking candidates when multiple match.
    pub autoref_cost: u8,
    /// Whether the candidate's return type matches the expected type (e.g. mutability expectations).
    /// Used for ranking: true gives a significant score bonus (+1000).
    pub matches_expectation: bool,
    /// Number of dereferences performed on the receiver to find this candidate.
    /// Used for ranking method candidates found via autoderef loops.
    /// Candidates with fewer dereferences (closer to the original type) are preferred.
    pub deref_steps: usize,
}

#[derive(Debug, Clone)]
pub struct BindOverloadGoalData<'ctx> {
    pub node_id: NodeID,
    pub var_ty: Ty<'ctx>,
    pub candidate_ty: Ty<'ctx>,
    pub source: DefinitionID,
    pub instantiation_args: Option<GenericArguments<'ctx>>,
}

#[derive(Debug, Clone, Copy)]
pub struct InterfaceCallInfo {
    pub root_interface: DefinitionID,
    pub method_interface: DefinitionID,
    pub method_id: DefinitionID,
    pub slot: usize,
    pub table_index: usize,
}

#[derive(Debug, Clone)]
pub struct BindInterfaceMethodGoalData<'ctx> {
    pub node_id: NodeID,
    pub var_ty: Ty<'ctx>,
    pub candidate_ty: Ty<'ctx>,
    pub call_info: InterfaceCallInfo,
    pub instantiation_args: Option<GenericArguments<'ctx>>,
}

/// Binds a method overload with associated receiver type and adjustments.
/// This is used when method resolution needs to consider multiple overloads
/// with different receiver mutabilities (e.g., `at(&self)` vs `at(&mut self)`).
#[derive(Debug, Clone)]
pub struct BindMethodOverloadGoalData<'ctx> {
    /// The node ID of the method call expression
    pub node_id: NodeID,
    /// The receiver node ID (for recording adjustments)
    pub receiver_node_id: NodeID,
    /// The type variable representing the method type
    pub var_ty: Ty<'ctx>,
    /// The type of the method candidate
    pub candidate_ty: Ty<'ctx>,
    /// The adjusted receiver type (after auto-ref)
    pub receiver_ty: Ty<'ctx>,
    /// The type variable used for the receiver in the Apply goal
    /// When this overload is selected, we equate receiver_ty_var = receiver_ty
    pub receiver_ty_var: Ty<'ctx>,
    /// The method's definition ID
    pub source: DefinitionID,
    /// Optional instantiation arguments
    pub instantiation_args: Option<GenericArguments<'ctx>>,
    /// Adjustments to apply to the receiver (deref, borrow, etc.)
    pub adjustments: Vec<Adjustment<'ctx>>,
}

pub enum SolverResult<'ctx> {
    Deferred,
    Solved(Vec<Obligation<'ctx>>), // Solved, With Sub-Obligations
    Error(SpannedErrorList<'ctx>), // Failed, With Errors
}

#[derive(Debug, Clone)]
pub struct ApplyGoalData<'ctx> {
    pub call_node_id: NodeID,
    pub call_span: Span,
    pub callee_ty: Ty<'ctx>,
    pub callee_source: Option<DefinitionID>,
    pub result_ty: Ty<'ctx>,
    pub _expect_ty: Option<Ty<'ctx>>,
    pub arguments: Vec<ApplyArgument<'ctx>>,
    /// If true, skip label validation (used for operator calls)
    pub skip_labels: bool,
}

#[derive(Debug, Clone)]
pub struct MemberGoalData<'ctx> {
    pub node_id: NodeID,
    pub receiver_node: NodeID,
    pub receiver: Ty<'ctx>,
    pub name: Identifier,
    pub result: Ty<'ctx>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct InferredStaticMemberGoalData<'ctx> {
    pub node_id: NodeID,
    pub name: Identifier,
    pub expr_ty: Ty<'ctx>,
    pub base_hint: Option<Ty<'ctx>>,
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
    pub node_id: NodeID,
    pub lhs_id: NodeID,
    pub rhs_id: NodeID,
}

/// Goal data for compound assignment operations (+=, -=, etc.)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignOpGoalData<'ctx> {
    /// Type of the LHS (must be a mutable place)
    pub lhs: Ty<'ctx>,
    /// Type of the RHS value
    pub rhs: Ty<'ctx>,
    /// The base binary operator (Add for +=, Sub for -=, etc.)
    pub operator: BinaryOperator,
    pub span: Span,
    pub node_id: NodeID,
    pub lhs_id: NodeID,
    pub rhs_id: NodeID,
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
    pub node_id: NodeID,
    pub ty: Ty<'ctx>,
    pub value_span: Span,
    pub label_span: Span,
}

#[derive(Debug, Clone)]
pub struct TupleAccessGoalData<'ctx> {
    pub node_id: NodeID,
    pub receiver: Ty<'ctx>,
    pub index: usize,
    pub result: Ty<'ctx>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct DerefGoalData<'ctx> {
    pub operand_ty: Ty<'ctx>,
    pub result_ty: Ty<'ctx>,
    pub span: Span,
}
