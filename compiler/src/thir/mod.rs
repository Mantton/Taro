mod erased_async_self;
use crate::{
    hir::{DefinitionID, NodeID},
    mir::{BinaryOperator, LogicalOperator, UnaryOperator},
    sema::models::{
        AdtDef, CaptureKind, EnumVariant, GenericArguments, GenericParameter, InterfaceReference,
        Ty,
    },
    span::{Span, Symbol},
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

pub mod match_tree;
pub mod package;
pub mod passes;
pub mod pattern;
pub mod synthesize;

index_vec::define_index_type! {
    pub struct BlockId = u32;
}

index_vec::define_index_type! {
    pub struct StmtId = u32;
}
index_vec::define_index_type! {
    pub struct ExprId = u32;
}

index_vec::define_index_type! {
    pub struct VariantIndex = u32;
}

index_vec::define_index_type! {
    pub struct FieldIndex = u32;
}

index_vec::define_index_type! {
    pub struct ArmId = u32;
}

#[derive(Debug)]
pub struct ThirPackage<'a> {
    pub functions: FxHashMap<DefinitionID, ThirFunction<'a>>,
    pub entry: Option<DefinitionID>,
}

#[derive(Debug)]
pub struct ThirFunction<'a> {
    pub id: DefinitionID,
    pub body: Option<BlockId>,
    pub constructor_self: Option<crate::hir::NodeID>,
    pub span: Span,
    pub params: Vec<Param<'a>>,
    pub stmts: IndexVec<StmtId, Stmt<'a>>,
    pub blocks: IndexVec<BlockId, Block>,
    pub exprs: IndexVec<ExprId, Expr<'a>>,
    pub arms: IndexVec<ArmId, Arm<'a>>,
    pub match_reports: FxHashMap<ExprId, match_tree::MatchReport<'a>>,
    pub is_async: bool,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub id: BlockId,
    pub stmts: Vec<StmtId>,
    pub expr: Option<ExprId>,
}

#[derive(Debug, Clone)]
pub struct Expr<'a> {
    pub kind: ExprKind<'a>,
    pub ty: Ty<'a>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExprKind<'a> {
    /// Use of a local variable
    Local(NodeID),
    /// Address-of / reference expression
    Reference {
        expr: ExprId,
    },
    /// Dereference `*expr`
    Deref(ExprId),
    /// If expression
    If {
        cond: ExprId,
        then_expr: ExprId,
        else_expr: Option<ExprId>,
    },
    /// `return` / `return value`
    Return {
        value: Option<ExprId>,
    },
    /// `break`
    Break,
    /// `continue`
    Continue,
    Assign {
        target: ExprId,
        value: ExprId,
    },
    /// Compound assignment operator (+=, -=, etc.) for intrinsics
    AssignOp {
        op: BinaryOperator,
        target: ExprId,
        value: ExprId,
    },
    /// Literal constant
    Literal(Constant<'a>),
    /// Array literal
    Array {
        elements: Vec<ExprId>,
    },
    /// List literal in list-typed context, e.g. `[1, 2, 3]` where expected type is `List[T]`
    ListLiteral {
        elements: Vec<ExprId>,
        element_ty: Ty<'a>,
    },
    /// Repeat literal `[expr; len]`
    Repeat {
        element: ExprId,
        count: usize,
    },
    /// Unary op
    Unary {
        op: UnaryOperator,
        operand: ExprId,
    },
    ClassUpcast {
        value: ExprId,
    },
    /// Narrow a proven subclass-preserving owned Self result.
    ClassSelfResult {
        value: ExprId,
    },
    /// `value as T`
    Cast {
        value: ExprId,
    },
    /// `value as? Target`
    ExistentialTryCast {
        value: ExprId,
        target: Ty<'a>,
    },
    /// `value is Target`
    ExistentialTypeIs {
        value: ExprId,
        target: Ty<'a>,
    },
    /// Non-overloadable identity of two owned strong class-handle snapshots.
    ClassIdentity {
        lhs: ExprId,
        rhs: ExprId,
        equal: bool,
    },
    /// Binary op
    Binary {
        op: BinaryOperator,
        lhs: ExprId,
        rhs: ExprId,
    },
    Logical {
        op: LogicalOperator,
        lhs: ExprId,
        rhs: ExprId,
    },
    /// Call to a resolved definition
    Call {
        callee: ExprId,
        args: Vec<ExprId>,
        /// ABI argument positions in evaluation order. Supplied expressions
        /// keep source order; omitted defaults follow in declaration order.
        /// None is the identity order. Kept separate from parameter positions.
        argument_evaluation_order: Option<Vec<usize>>,
        is_async: bool,
    },
    /// Box a concrete value into a Swift-style existential container
    BoxExistential {
        value: ExprId,
        interfaces: &'a [InterfaceReference<'a>],
    },
    /// Upcast an existential to a subset or superface existential
    ExistentialUpcast {
        value: ExprId,
        to: Ty<'a>,
    },
    /// Block expression
    Block(BlockId),
    Adt(AdtExpression<'a>),
    Field {
        lhs: ExprId,
        index: FieldIndex,
    },
    Tuple {
        fields: Vec<ExprId>,
    },
    Match {
        scrutinee: ExprId,
        arms: Vec<ArmId>,
        binding_condition: bool,
    },
    Zst {
        id: DefinitionID,
        /// Generic arguments for this definition (if generic)
        generic_args: Option<GenericArguments<'a>>,
    },
    /// Closure expression
    Closure {
        /// Closure definition ID
        def_id: DefinitionID,
        /// Captured variables with their capture expressions
        captures: Vec<ClosureCapture>,
        /// The closure's callable kind.
        kind: crate::sema::models::ClosureKind,
    },
    /// Access to a captured variable (upvar) within a closure body
    /// This is lowered to a field access on the closure's self parameter
    Upvar {
        /// Field index in the closure environment struct
        field_index: FieldIndex,
        /// How this variable is captured.
        capture_kind: CaptureKind,
    },
    /// Coerce a non-capturing closure to a function pointer
    /// The closure must have no captures for this to be valid
    ClosureToFnPointer {
        /// The closure expression
        closure: ExprId,
        /// The closure's definition ID (to get the body function)
        closure_def_id: DefinitionID,
    },
    /// `await future` — suspend until the future completes
    Await {
        /// The future expression being awaited
        future: ExprId,
    },
}

/// A captured variable in a closure
#[derive(Debug, Clone, Copy)]
pub struct ClosureCapture {
    /// The captured variable's source NodeID
    pub source_id: NodeID,
    /// Expression to evaluate for capture (ref creation or value copy/move)
    pub capture_expr: ExprId,
    /// How this variable is captured.
    pub capture_kind: crate::sema::models::CaptureKind,
    /// Field index in the environment struct
    pub field_index: FieldIndex,
}

#[derive(Debug, Clone)]
pub struct Constant<'a> {
    pub ty: Ty<'a>,
    pub value: ConstantKind,
}

#[derive(Debug, Clone)]
pub enum ConstantKind {
    Bool(bool),
    Rune(char),
    String(crate::span::Symbol),
    Integer(u64),
    Float(f64),
    Unit,
    ConstParam(GenericParameter),
}

#[derive(Debug, Clone)]
pub enum StmtKind<'a> {
    Let {
        id: NodeID,
        pattern: Pattern<'a>,
        expr: Option<ExprId>,
        ty: Ty<'a>,
        mutable: bool,
    },
    Return {
        value: Option<ExprId>,
    },
    Break,
    Continue,
    Defer(BlockId),
    /// Successful bindings live in the enclosing lexical scope.
    Guard {
        condition: ExprId,
        else_block: BlockId,
    },
    Loop {
        block: BlockId,
    },
    Expr(ExprId),
}

#[derive(Debug, Clone)]
pub struct Stmt<'a> {
    pub kind: StmtKind<'a>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Param<'a> {
    pub id: NodeID,
    pub name: Symbol,
    pub ty: Ty<'a>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FieldExpression {
    pub index: FieldIndex,
    pub expression: ExprId,
}

#[derive(Debug, Clone)]
pub struct AdtExpression<'a> {
    /// Evaluated after explicit fields; only its omitted fields are copied.
    pub base: Option<ExprId>,
    pub definition: AdtDef,
    pub variant_index: Option<VariantIndex>,
    pub generic_args: GenericArguments<'a>,
    pub fields: Vec<FieldExpression>,
}

#[derive(Debug, Clone)]
pub struct Pattern<'ctx> {
    pub ty: Ty<'ctx>,
    pub span: Span,
    pub kind: PatternKind<'ctx>,
}

#[derive(Debug, Clone)]
pub enum PatternKind<'ctx> {
    Wild,
    Binding {
        name: Symbol,
        local: NodeID,
        ty: Ty<'ctx>,
    },
    Leaf {
        subpatterns: Vec<FieldPattern<'ctx>>,
    },
    Constant {
        value: Constant<'ctx>,
    },
    Variant {
        definition: AdtDef,
        variant: EnumVariant<'ctx>,
        subpatterns: Vec<FieldPattern<'ctx>>,
    },
    Or(Vec<Pattern<'ctx>>),
}

#[derive(Debug, Clone)]
pub struct FieldPattern<'ctx> {
    pub index: FieldIndex,
    pub pattern: Pattern<'ctx>,
}

pub type Pat<'ctx> = Pattern<'ctx>;

#[derive(Debug, Clone)]
pub struct Arm<'ctx> {
    pub pattern: Box<Pat<'ctx>>,
    pub guard: Option<ExprId>,
    pub body: ExprId,
    pub span: Span,
}
