use crate::{
    hir::{BindingMode, DefinitionID, NodeID},
    mir::{BinaryOperator, LogicalOperator, UnaryOperator},
    sema::models::{
        AdtDef, EnumVariant, GenericArguments, GenericParameter, InterfaceReference, Ty,
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
    pub span: Span,
    pub params: Vec<Param<'a>>,
    pub stmts: IndexVec<StmtId, Stmt<'a>>,
    pub blocks: IndexVec<BlockId, Block>,
    pub exprs: IndexVec<ExprId, Expr<'a>>,
    pub arms: IndexVec<ArmId, Arm<'a>>,
    pub match_trees: FxHashMap<ExprId, match_tree::MatchTree<'a>>,
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
        mutable: bool,
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
    /// `value as T`
    Cast {
        value: ExprId,
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
    Make {
        value: ExprId,
    },
    Match {
        scrutinee: ExprId,
        arms: Vec<ArmId>,
    },
    Zst {
        id: DefinitionID,
        /// Generic arguments for this definition (if generic)
        generic_args: Option<GenericArguments<'a>>,
    },
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
        mode: BindingMode,
    },
    Deref {
        pattern: Box<Pattern<'ctx>>,
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
