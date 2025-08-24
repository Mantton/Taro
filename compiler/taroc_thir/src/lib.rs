use index_vec::{IndexVec, define_index_type};
use taroc_hir::{Mutability, NodeID};
use taroc_sema::ty::{FieldIndex, Ty, VariantIndex};
use taroc_span::{Span, Spanned};

define_index_type! {
    pub struct ParameterID = u32;
}

define_index_type! {
    pub struct StatementID = u32;
}

define_index_type! {
    pub struct ExpressionID = u32;
}

define_index_type! {
    pub struct BlockID = u32;
}

#[derive(Default)]
pub struct ThirBody<'ctx> {
    pub blocks: IndexVec<BlockID, Block>,
    pub expressions: IndexVec<ExpressionID, Expression<'ctx>>,
    pub statements: IndexVec<StatementID, Statement>,
    pub parameters: IndexVec<ParameterID, Parameter<'ctx>>,
}

pub struct Parameter<'ctx> {
    pub ty: Ty<'ctx>,
}
pub struct Statement {
    pub kind: StatementKind,
}
pub enum StatementKind {
    Expression(ExpressionID),
    Let {
        initializer: Option<ExpressionID>,
        span: Span,
    },
    Break,
    Return(Option<ExpressionID>),
    Loop(BlockID),
    Continue,
}

pub struct Expression<'ctx> {
    pub ty: Ty<'ctx>,
    pub span: Span,
    pub kind: ExpressionKind<'ctx>,
}

pub enum ExpressionKind<'ctx> {
    Literal {
        value: Spanned<taroc_hir::Literal>,
        negate: bool,
    },
    VariableReference(NodeID),
    If {
        condition: ExpressionID,
        then_block: ExpressionID,
        else_block: Option<ExpressionID>,
    },

    Call {
        fn_ty: Ty<'ctx>,
        func: ExpressionID,
        arguments: Vec<ExpressionID>,
        from_overload: bool,
        fn_span: Span,
    },
    Dereference(ExpressionID),
    Binary {
        op: BinaryOperator,
        lhs: ExpressionID,
        rhs: ExpressionID,
    },
    LogicalOp {
        op: LogicalOperator,
        lhs: ExpressionID,
        rhs: ExpressionID,
    },

    Unary {
        op: UnaryOp,
        rhs: ExpressionID,
    },
    Cast(ExpressionID),
    Loop(ExpressionID),
    Block(BlockID),
    Assign(ExpressionID, ExpressionID),
    AssignOp(usize, ExpressionID, ExpressionID),
    FieldAccess(ExpressionID, VariantIndex, FieldIndex),
    Reference(Mutability, ExpressionID),
    Array(Vec<ExpressionID>),
    Tuple(Vec<ExpressionID>),
    // TODO
    Adt,
    Match,
    Placeholder,
}

pub enum BinaryOperator {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Lt,
    Leq,
    Neq,
    Geq,
    Gt,
}

pub enum LogicalOperator {
    And,
    Or,
}

pub enum UnaryOp {
    Not,
    Neg,
    BitNot,
}

pub struct Block {
    pub span: Span,
    pub statments: Vec<StatementID>,
}
