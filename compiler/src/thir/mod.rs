use crate::{
    hir::{BinaryOperator, DefinitionID, NodeID, UnaryOperator},
    sema::models::{AdtDef, Ty},
    span::{Span, Symbol},
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

pub mod package;

index_vec::define_index_type! {
    pub struct BlockId = u32;
}

index_vec::define_index_type! {
    pub struct StmtId = u32;
}
index_vec::define_index_type! {
    pub struct ExprId = u32;
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
}

#[derive(Debug, Clone)]
pub struct Block {
    pub id: BlockId,
    pub stmts: Vec<StmtId>,
    pub expr: Option<ExprId>,
}

#[derive(Debug, Clone)]
pub struct Expr<'a> {
    pub id: ExprId,
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
    /// Literal constant
    Literal(Constant<'a>),
    /// Unary op
    Unary {
        op: UnaryOperator,
        operand: ExprId,
    },
    /// Binary op
    Binary {
        op: BinaryOperator,
        lhs: ExprId,
        rhs: ExprId,
    },
    /// Call to a resolved definition
    Call {
        callee: DefinitionID,
        args: Vec<ExprId>,
    },
    /// Block expression
    Block(BlockId),
    Adt(AdtExpression),
    Field {
        lhs: ExprId,
        index: FieldIndex,
    },
    Tuple {
        fields: Vec<ExprId>,
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
}

#[derive(Debug, Clone)]
pub enum StmtKind<'a> {
    Let {
        id: NodeID,
        pattern: NodeID,
        name: Option<Symbol>,
        mutable: bool,
        expr: Option<ExprId>,
        ty: Ty<'a>,
    },
    Assign {
        target: ExprId,
        value: ExprId,
    },
    Return {
        value: Option<ExprId>,
    },
    Break,
    Continue,
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

pub type FieldIndex = usize;

#[derive(Debug, Clone)]
pub struct AdtExpression {
    pub definition: AdtDef,
    pub fields: Vec<FieldExpression>,
}
