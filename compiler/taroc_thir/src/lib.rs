use index_vec::{IndexVec, define_index_type};
use rustc_hash::FxHashMap;
use taroc_hir::{DefinitionID, Mutability, NodeID};
use taroc_sema::ty::{FieldIndex, Ty, VariantIndex};
use taroc_span::{Span, Spanned};

pub type Package<'ctx> = FxHashMap<DefinitionID, ThirBody<'ctx>>;
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
    Defer(BlockID),
    Continue,
}

pub struct Expression<'ctx> {
    pub ty: Ty<'ctx>,
    pub span: Span,
    pub kind: ExpressionKind<'ctx>,
}

pub enum Callee<'ctx> {
    // Statically known function definition; no callee value materialized
    Direct {
        def: DefinitionID,
        fn_ty: Ty<'ctx>,
    },
    // Thin function value (code pointer only)
    Thin {
        ptr: ExpressionID,
        fn_ty: Ty<'ctx>,
    },
    // Thick function value (code pointer + environment) TODO!
    Thick {
        code: ExpressionID,
        env: ExpressionID,
        fn_ty: Ty<'ctx>,
    },
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
        callee: Callee<'ctx>,
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
    AssignOp {
        op: AssignmentOperator,
        lhs: ExpressionID,
        rhs: ExpressionID,
    },
    FieldAccess(ExpressionID, VariantIndex, FieldIndex),
    Reference(Mutability, ExpressionID),
    Array(Vec<ExpressionID>),
    Tuple(Vec<ExpressionID>),
    ZST(Ty<'ctx>),
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
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Eq,
    Lt,
    Leq,
    Neq,
    Geq,
    Gt,
}

pub enum AssignmentOperator {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Xor,
    And,
    Or,
    Shl,
    Shr,
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
    pub statements: Vec<StatementID>,
}
