use index_vec::{IndexVec, define_index_type};
use rustc_hash::FxHashMap;
use taroc_hir::{DefinitionID, Mutability, NodeID};
use taroc_sema::ty::{FieldIndex, GenericArguments, Ty, VariantIndex};
use taroc_span::{Span, Spanned, Symbol};

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

define_index_type! {
    pub struct ArmID = u32;
}

#[derive(Default)]
pub struct ThirBody<'ctx> {
    pub blocks: IndexVec<BlockID, Block>,
    pub expressions: IndexVec<ExpressionID, Expression<'ctx>>,
    pub statements: IndexVec<StatementID, Statement>,
    pub parameters: IndexVec<ParameterID, Parameter<'ctx>>,
    pub arms: IndexVec<ArmID, MatchArm<'ctx>>,
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
    // TODO: Thick function value (code pointer + environment) !
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
    Adt(AdtData<'ctx>),
    Match {
        scrutinee: ExpressionID,
        arms: Vec<ArmID>,
    },
    Placeholder,
}

pub struct AdtData<'ctx> {
    pub def_id: DefinitionID,
    pub variant: VariantIndex,
    pub arguments: GenericArguments<'ctx>,
    pub fields: Vec<AdtFieldExpression>,
}

pub struct AdtFieldExpression {
    pub index: FieldIndex,
    pub expression: ExpressionID,
}

pub struct MatchArm<'ctx> {
    pub pat: Pattern<'ctx>,
    pub guard: Option<ExpressionID>,
    pub body: ExpressionID,
    pub span: Span,
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

pub struct Pattern<'ctx> {
    pub ty: Ty<'ctx>,
    pub span: Span,
    pub kind: PatternKind<'ctx>,
}

pub enum PatternKind<'ctx> {
    Wildcard,
    Binding {
        name: Symbol,
        ty: Ty<'ctx>,
    },
    Variant {
        id: DefinitionID,
        arguments: GenericArguments<'ctx>,
        index: VariantIndex,
        fields: Vec<FieldPattern<'ctx>>,
    },
    Leaf {
        fields: Vec<FieldPattern<'ctx>>,
    },
    Constant,
    Or(Vec<Pattern<'ctx>>),
    Placeholder,
}

pub struct FieldPattern<'tcx> {
    pub field: FieldIndex,
    pub pattern: Pattern<'tcx>,
}
