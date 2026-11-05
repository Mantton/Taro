use crate::{
    ast::Identifier,
    hir::{BinaryOperator, NodeID, UnaryOperator},
    sema::{
        error::SpannedErrorList,
        models::{Const, Constraint, GenericArgument, GenericArguments, InterfaceReference, Ty},
        resolve::models::DefinitionID,
    },
    span::Span,
};

#[derive(Debug, Clone)]
pub enum Adjustment<'ctx> {
    Dereference,
    /// Call the Deref requirement through its normal conformance witness.
    DerefCall {
        method: DefinitionID,
        arguments: GenericArguments<'ctx>,
        result: Ty<'ctx>,
    },
    /// Weaken raw-pointer permission while preserving its unchecked provenance.
    PointerToConst,
    /// Contextual nil literal with the selected raw-pointer type.
    NullPointer {
        to: Ty<'ctx>,
    },
    ClassUpcast {
        to: Ty<'ctx>,
    },
    Reference,
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
    /// Contextual success injection, after the payload's ordinary coercions.
    ResultOkWrap {
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
    /// Constructor inference binds Self through a Result's success slot.
    ConstructorResult(Ty<'ctx>, Ty<'ctx>),
    /// Delegation initializes storage on success and yields Result[(), E].
    InitializerStatement(Ty<'ctx>, Ty<'ctx>),
    ConstraintEqual(Ty<'ctx>, Ty<'ctx>),
    /// Recheck after defaults resolve; hidden payload requirements are witnessed.
    ExistentialConstraint(Constraint<'ctx>),
    Conforms {
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    },
    /// A direct inferred generic call may open one hidden payload. This is
    /// deliberately not an ordinary conformance of its owning container.
    OpenedConforms {
        source: DefinitionID,
        arguments: GenericArguments<'ctx>,
        template: InterfaceReference<'ctx>,
        ty: Ty<'ctx>,
        interface: InterfaceReference<'ctx>,
    },
    ValidateOpening {
        source: DefinitionID,
        arguments: GenericArguments<'ctx>,
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
    BindMethodValue(BindMethodValueGoalData<'ctx>),
    MethodValueSignature(MethodValueSignatureGoalData<'ctx>),
    InferredStaticMember(InferredStaticMemberGoalData<'ctx>),
    MethodCall(MethodCallData<'ctx>),
    IndexAccess(IndexAccessGoalData<'ctx>),
    StructLiteral(StructLiteralGoalData<'ctx>),
    CollectionLiteral {
        ty: Ty<'ctx>,
        element: Ty<'ctx>,
        len: Const<'ctx>,
    },
    TupleAccess(TupleAccessGoalData<'ctx>),
    Deref(DerefGoalData<'ctx>),
    DefaultFallback(DefaultFallbackGoalData<'ctx>),
}

#[derive(Debug, Clone)]
pub struct DefaultFallbackGoalData<'ctx> {
    pub infer_var: GenericArgument<'ctx>,
    pub default: GenericArgument<'ctx>,
    pub span: Span,
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
    /// Lower is better: no automatic reference=0, reference=1.
    /// Used for ranking candidates when multiple match.
    pub autoref_cost: u8,
    /// Whether the candidate matches async/sync preference from call context.
    /// Used for ranking overloads between same-shape sync/async candidates.
    pub matches_async_preference: bool,
    /// Number of dereferences performed on the receiver to find this candidate.
    /// Used for ranking method candidates found via autoderef loops.
    /// Candidates with fewer dereferences (closer to the original type) are preferred.
    pub deref_steps: usize,
}

#[derive(Debug, Clone)]
pub struct BindOverloadGoalData<'ctx> {
    /// Class type used for qualified static lookup; ancestor arguments stay fixed.
    pub static_owner: Option<Ty<'ctx>>,
    pub node_id: NodeID,
    pub var_ty: Ty<'ctx>,
    pub candidate_ty: Ty<'ctx>,
    pub source: DefinitionID,
    pub instantiation_args: Option<GenericArguments<'ctx>>,
}

/// Resolution record for a method call dispatched through an interface
/// (existential receiver or generic bound). Deliberately does NOT carry a
/// witness-table slot: the slot is computed at monomorphization time from
/// `ref_ops::interface_method_slot` so that exactly one place encodes table
/// layout. (A `slot` previously stored here was never read downstream and
/// could silently drift from the real layout.)
#[derive(Debug, Clone, Copy)]
pub struct InterfaceCallInfo {
    pub root_interface: DefinitionID,
    pub method_interface: DefinitionID,
    pub method_id: DefinitionID,
    pub table_index: usize,
}

#[derive(Debug, Clone, Copy)]
pub struct ResolvedPropertyRead {
    pub getter_id: DefinitionID,
}

#[derive(Debug, Clone)]
pub struct BindInterfaceMethodGoalData<'ctx> {
    pub node_id: NodeID,
    pub var_ty: Ty<'ctx>,
    pub candidate_ty: Ty<'ctx>,
    pub call_info: InterfaceCallInfo,
    pub instantiation_args: Option<GenericArguments<'ctx>>,
}

/// Bind a selected method and publish only its receiver adjustments.
#[derive(Debug, Clone)]
pub struct BindMethodOverloadGoalData<'ctx> {
    pub binding: Box<Goal<'ctx>>,
    pub receiver_node_id: NodeID,
    pub receiver_constraint: Option<(Ty<'ctx>, Ty<'ctx>)>,
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
    /// Direct callable expression; implicit method/operator goals have none.
    pub callee_node_id: Option<NodeID>,
    pub call_span: Span,
    pub callee_ty: Ty<'ctx>,
    pub callee_source: Option<DefinitionID>,
    pub is_unsafe_context: bool,
    pub result_ty: Ty<'ctx>,
    pub arguments: Vec<ApplyArgument<'ctx>>,
    /// If true, skip label validation (used for operator calls)
    pub skip_labels: bool,
    /// Operator overload probes compare receiver and arguments. The selected
    /// conformance's output is checked afterwards against result context.
    pub input_only_selection: bool,
}

#[derive(Debug, Clone)]
pub struct MemberGoalData<'ctx> {
    pub classify_only: bool,
    pub receiver_addressable: bool,
    pub explicit_arguments: Option<crate::hir::TypeArguments>,
    pub node_id: NodeID,
    pub receiver_node: NodeID,
    pub receiver: Ty<'ctx>,
    pub name: Identifier,
    pub result: Ty<'ctx>,
    pub span: Span,
    pub signature_hint: Option<Ty<'ctx>>,
}

/// Select an ordinary method first, then expose its receiverless signature for
/// a closure that will capture the receiver. No environment is created in an
/// overload probe, so rejected branches cannot publish synthetic definitions.
#[derive(Debug, Clone)]
pub struct BindMethodValueGoalData<'ctx> {
    pub explicit_arguments: Option<crate::hir::TypeArguments>,
    pub node_id: NodeID,
    pub var_ty: Ty<'ctx>,
    pub candidate_ty: Ty<'ctx>,
    pub source: DefinitionID,
    pub instantiation_args: Option<GenericArguments<'ctx>>,
    pub call_info: Option<InterfaceCallInfo>,
    pub receiver: Ty<'ctx>,
    pub signature_hint: Option<Ty<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct MethodValueSignatureGoalData<'ctx> {
    pub node_id: NodeID,
    pub source: DefinitionID,
    pub method_ty: Ty<'ctx>,
    pub callback_ty: Ty<'ctx>,
    pub receiver: Ty<'ctx>,
    pub signature_hint: Option<Ty<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct InferredStaticMemberGoalData<'ctx> {
    pub node_id: NodeID,
    pub name: Identifier,
    pub expr_ty: Ty<'ctx>,
    pub base_hint: Option<Ty<'ctx>>,
    pub allow_unsafe_callable_values: bool,
    pub prefer_async: bool,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct IndexAccessGoalData<'ctx> {
    pub receiver_addressable: bool,
    pub nodes: crate::hir::IndexCallNodes,
    pub receiver: Ty<'ctx>,
    pub keys: Vec<ApplyArgument<'ctx>>,
    pub output: Ty<'ctx>,
    pub method_ty: Ty<'ctx>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct MethodCallData<'ctx> {
    pub receiver_addressable: bool,
    pub selected: Option<(DefinitionID, GenericArguments<'ctx>)>,
    pub node_id: NodeID,
    pub receiver: Ty<'ctx>,
    pub reciever_span: Span,
    pub reciever_node: NodeID,
    pub is_unsafe_context: bool,
    pub name: Identifier,
    pub arguments: Vec<ApplyArgument<'ctx>>,
    pub result: Ty<'ctx>,
    pub method_ty: Ty<'ctx>,
    pub prefer_async: bool,
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
    pub receiver_addressable: bool,
    pub lhs: Ty<'ctx>,
    pub rho: Ty<'ctx>,
    pub operator: UnaryOperator,
    pub span: Span,
    pub node_id: NodeID,
    pub rhs_id: NodeID,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BinOpGoalData<'ctx> {
    pub receiver_addressable: bool,
    pub lhs: Ty<'ctx>,
    pub rhs: Ty<'ctx>,
    pub rho: Ty<'ctx>,
    pub operator: BinaryOperator,
    pub span: Span,
    pub node_id: NodeID,
    pub lhs_id: NodeID,
    pub rhs_id: NodeID,
}

/// Goal data for compound assignment operations (+=, -=, etc.)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignOpGoalData<'ctx> {
    pub receiver_addressable: bool,
    /// Receiver type; reference implementations require existing storage.
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

#[derive(Debug, Clone, Copy)]
pub enum LiteralConstructor {
    Struct,
    Variant(crate::hir::DefinitionID),
    /// Context can arrive from a later assignment or generic call obligation.
    InferredVariant {
        node_id: NodeID,
        name: Identifier,
    },
}

#[derive(Debug, Clone)]
pub struct StructLiteralGoalData<'ctx> {
    pub ty_span: Span,
    pub span: Span,
    pub struct_ty: Ty<'ctx>,
    pub constructor: LiteralConstructor,
    pub fields: Vec<StructLiteralField<'ctx>>,
    pub base_span: Option<Span>,
}

#[derive(Debug, Clone, Copy)]
pub struct StructLiteralField<'ctx> {
    /// Deferred constructors supply field context once the enum type resolves.
    pub expectation: Option<Ty<'ctx>>,
    pub name: crate::span::Symbol,
    pub node_id: NodeID,
    pub ty: Ty<'ctx>,
    pub value_span: Span,
    pub label_span: Span,
}

#[derive(Debug, Clone)]
pub struct TupleAccessGoalData<'ctx> {
    pub receiver_addressable: bool,
    /// The `.N` access node that owns the resolved field index.
    pub node_id: NodeID,
    /// The receiver expression that must receive any autoderef adjustments.
    pub receiver_node_id: NodeID,
    pub receiver: Ty<'ctx>,
    pub index: usize,
    pub result: Ty<'ctx>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct DerefGoalData<'ctx> {
    pub operand_node: NodeID,
    pub receiver_addressable: bool,
    pub operand_ty: Ty<'ctx>,
    pub is_unsafe_context: bool,
    pub result_ty: Ty<'ctx>,
    pub span: Span,
}
