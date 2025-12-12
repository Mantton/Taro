use crate::{
    hir::{BinaryOperator, DefinitionID, UnaryOperator},
    sema::models::Ty,
    span::{Span, Symbol},
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

pub mod builder;
pub mod package;

index_vec::define_index_type! {
    pub struct LocalId = u32;
}

index_vec::define_index_type! {
    pub struct BasicBlockId = u32;
}

#[derive(Debug, Default)]
pub struct MirPackage<'ctx> {
    pub functions: FxHashMap<DefinitionID, &'ctx Body<'ctx>>,
    pub entry: Option<DefinitionID>,
}

#[derive(Debug, Clone)]
pub struct Body<'ctx> {
    pub locals: IndexVec<LocalId, LocalDecl<'ctx>>,
    pub basic_blocks: IndexVec<BasicBlockId, BasicBlock<'ctx>>,
    pub start_block: BasicBlockId,
    pub return_local: LocalId,
}

#[derive(Debug, Clone)]
pub struct LocalDecl<'ctx> {
    pub ty: Ty<'ctx>,
    pub kind: LocalKind,
    pub name: Option<Symbol>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalKind {
    Param,
    User,
    Temp,
    Return,
}

#[derive(Debug, Clone)]
pub struct BasicBlock<'ctx> {
    pub statements: Vec<Statement<'ctx>>,
    pub terminator: Option<Terminator<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct Statement<'ctx> {
    pub kind: StatementKind<'ctx>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum StatementKind<'ctx> {
    Assign(Place, Rvalue<'ctx>),
    StorageLive(LocalId),
    StorageDead(LocalId),
    Nop,
}

#[derive(Debug, Clone)]
pub struct Terminator<'ctx> {
    pub kind: TerminatorKind<'ctx>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum TerminatorKind<'ctx> {
    Goto {
        target: BasicBlockId,
    },
    SwitchInt {
        discr: Operand<'ctx>,
        targets: Vec<(u128, BasicBlockId)>,
        otherwise: BasicBlockId,
    },
    Return,
    Unreachable,
    Call {
        func: Operand<'ctx>,
        args: Vec<Operand<'ctx>>,
        destination: Place,
        target: BasicBlockId,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Place {
    pub local: LocalId,
}

#[derive(Debug, Clone)]
pub enum Operand<'ctx> {
    Copy(Place),
    Move(Place),
    Constant(Constant<'ctx>),
}

#[derive(Debug, Clone)]
pub struct Constant<'ctx> {
    pub ty: Ty<'ctx>,
    pub value: ConstantKind<'ctx>,
}

#[derive(Debug, Clone)]
pub enum ConstantKind<'ctx> {
    Bool(bool),
    Rune(char),
    String(Symbol),
    Integer(u64),
    Float(f64),
    Unit,
    Function(crate::hir::DefinitionID, Ty<'ctx>),
}

#[derive(Debug, Clone)]
pub enum Rvalue<'ctx> {
    Use(Operand<'ctx>),
    UnaryOp {
        op: UnaryOperator,
        operand: Operand<'ctx>,
    },
    BinaryOp {
        op: BinaryOperator,
        lhs: Operand<'ctx>,
        rhs: Operand<'ctx>,
    },
    Cast {
        operand: Operand<'ctx>,
        ty: Ty<'ctx>,
    },
}
