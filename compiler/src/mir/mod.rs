use crate::{
    hir::DefinitionID,
    sema::models::Ty,
    span::{Span, Symbol},
    thir::{self, FieldIndex, VariantIndex},
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

pub mod builder;
pub mod optimize;
pub mod package;
pub mod pretty;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirPhase {
    /// Freshly built by the MIR builder. High-level rvalues and structural debris may exist.
    Built,
    /// After basic CFG cleanup (unreachable pruning, trivial gotos removed).
    CfgClean,
    /// After lowering high-level rvalues like aggregates.
    Lowered,
}

#[derive(Debug, Clone)]
pub struct Body<'ctx> {
    pub locals: IndexVec<LocalId, LocalDecl<'ctx>>,
    pub basic_blocks: IndexVec<BasicBlockId, BasicBlockData<'ctx>>,
    pub start_block: BasicBlockId,
    pub return_local: LocalId,
    pub escape_locals: Vec<bool>,
    pub phase: MirPhase,
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
pub struct BasicBlockData<'ctx> {
    pub note: Option<String>,
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
    Assign(Place<'ctx>, Rvalue<'ctx>),
    GcSafepoint,
    Nop,
    SetDiscriminant {
        place: Place<'ctx>,
        variant_index: VariantIndex,
    },
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
    /// Temporary terminator used during building; must be patched to a real edge.
    UnresolvedGoto,
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
        destination: Place<'ctx>,
        target: BasicBlockId,
    },
}

impl<'a> TerminatorKind<'a> {
    #[inline]
    pub fn if_(cond: Operand<'a>, t: BasicBlockId, e: BasicBlockId) -> TerminatorKind<'a> {
        TerminatorKind::SwitchInt {
            discr: cond,
            // `SwitchInt` branches on integer values. For booleans, `0` is `false`
            // and any non-zero value is `true` (LLVM `i1` uses `0/1`).
            targets: vec![(0, e)],
            otherwise: t,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Place<'ctx> {
    pub local: LocalId,
    pub projection: Vec<PlaceElem<'ctx>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlaceElem<'ctx> {
    Deref,
    Field(FieldIndex, Ty<'ctx>),
    VariantDowncast { name: Symbol, index: VariantIndex },
}

#[derive(Debug, Clone)]
pub enum Operand<'ctx> {
    Copy(Place<'ctx>),
    Move(Place<'ctx>),
    Constant(Constant<'ctx>),
}

#[derive(Debug, Clone)]
pub struct Constant<'ctx> {
    pub ty: Ty<'ctx>,
    pub value: ConstantKind<'ctx>,
}

use crate::sema::models::GenericArguments;

#[derive(Debug, Clone)]
pub enum ConstantKind<'ctx> {
    Bool(bool),
    Rune(char),
    String(Symbol),
    Integer(u64),
    Float(f64),
    Unit,
    Function(DefinitionID, GenericArguments<'ctx>, Ty<'ctx>),
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
        kind: CastKind,
    },
    Ref {
        mutable: bool,
        place: Place<'ctx>,
    },
    Discriminant {
        place: Place<'ctx>,
    },
    Alloc {
        ty: Ty<'ctx>,
    },
    Aggregate {
        kind: AggregateKind<'ctx>,
        fields: IndexVec<FieldIndex, Operand<'ctx>>,
    },
    /// Repeat the same operand `count` times into an array.
    Repeat {
        operand: Operand<'ctx>,
        count: usize,
        element: Ty<'ctx>,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum CastKind {
    Numeric,
    BoxExistential,
    ExistentialUpcast,
}

#[derive(Debug, Clone)]
pub enum AggregateKind<'ctx> {
    Tuple,
    Adt {
        def_id: DefinitionID,
        variant_index: Option<VariantIndex>,
        generic_args: GenericArguments<'ctx>,
    },
    Array {
        len: usize,
        element: Ty<'ctx>,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOperator {
    LogicalNot,
    Negate,
    BitwiseNot,
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOperator {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
    /// `%`
    Rem,
    /// `&`
    BitAnd,
    /// `|`
    BitOr,
    /// `^`
    BitXor,
    /// `<<`
    BitShl,
    /// `>>`
    BitShr,
    /// `==`
    Eql,
    /// `<`
    Lt,
    /// `>`
    Gt,
    /// `<=`
    Leq,
    /// `>=`
    Geq,
    /// `!=`
    Neq,
}

#[derive(Debug, Clone, Copy)]
pub enum LogicalOperator {
    /// &&
    And,
    /// ||
    Or,
}

/// The `BlockAnd` "monad" packages up the new basic block along with a
/// produced value (sometimes just unit, of course). The `unpack!`
/// macro (and methods below) makes working with `BlockAnd` much more
/// convenient.
#[must_use = "if you don't use one of these results, you're leaving a dangling edge"]
pub struct BlockAnd<T>(BasicBlockId, T);

impl BlockAnd<()> {
    /// Unpacks `BlockAnd<()>` into a [`BasicBlock`].
    #[must_use]
    fn into_block(self) -> BasicBlockId {
        let Self(block, ()) = self;
        block
    }
}

pub trait BlockAndExtension {
    fn and<T>(self, v: T) -> BlockAnd<T>;
    fn unit(self) -> BlockAnd<()>;
}

impl BlockAndExtension for BasicBlockId {
    fn and<T>(self, v: T) -> BlockAnd<T> {
        BlockAnd(self, v)
    }

    fn unit(self) -> BlockAnd<()> {
        BlockAnd(self, ())
    }
}

/// Update a block pointer and return the value.
/// Use it like `let x = unpack!(block = self.foo(block, foo))`.
#[macro_export]
macro_rules! unpack {
    ($x:ident = $c:expr) => {{
        let BlockAnd(b, v) = $c;
        $x = b;
        v
    }};
}

impl<'ctx> Place<'ctx> {
    pub fn from_local(id: LocalId) -> Place<'ctx> {
        Place {
            local: id,
            projection: Vec::new(),
        }
    }

    pub fn return_place() -> Place<'ctx> {
        Place {
            local: LocalId { _raw: 0 },
            projection: vec![],
        }
    }
}

#[derive(Debug, PartialEq)]
pub(crate) enum Category {
    /// An assignable memory location like `x`, `x.f`, `foo()[3]`, that
    /// sort of thing. Something that could appear on the LHS of an `=`
    /// sign.
    Place,

    /// A literal like `23` or `"foo"`. Does not include constant
    /// expressions like `3 + 5`.
    Constant,

    /// Something that generates a new value at runtime, like `x + y`
    /// or `foo()`.
    Rvalue(RvalueFunc),
}

/// Rvalues fall into different "styles" that will determine which fn
/// is best suited to generate them.
#[derive(Debug, PartialEq)]
pub(crate) enum RvalueFunc {
    /// Best generated by `into`. This is generally exprs that
    /// cause branching, like `match`, but also includes calls.
    Into,

    /// Best generated by `as_rvalue`. This is usually the case.
    AsRvalue,
}

impl Category {
    pub fn of(k: &thir::ExprKind) -> Category {
        match k {
            thir::ExprKind::Deref(..)
            | thir::ExprKind::Local(..)
            | thir::ExprKind::Field { .. } => Category::Place,

            thir::ExprKind::Reference { .. }
            | thir::ExprKind::If { .. }
            | thir::ExprKind::Match { .. }
            | thir::ExprKind::Call { .. }
            | thir::ExprKind::BoxExistential { .. }
            | thir::ExprKind::ExistentialUpcast { .. }
            | thir::ExprKind::Block(..)
            | thir::ExprKind::Adt(..) => Category::Rvalue(RvalueFunc::Into),

            thir::ExprKind::Assign { .. }
            | thir::ExprKind::AssignOp { .. }
            | thir::ExprKind::Binary { .. }
            | thir::ExprKind::Logical { .. }
            | thir::ExprKind::Unary { .. }
            | thir::ExprKind::Cast { .. }
            | thir::ExprKind::Tuple { .. }
            | thir::ExprKind::Array { .. }
            | thir::ExprKind::Repeat { .. }
            | thir::ExprKind::Make { .. } => Category::Rvalue(RvalueFunc::AsRvalue),

            thir::ExprKind::Literal(..) | thir::ExprKind::Zst { .. } => Category::Constant,
        }
    }
}
