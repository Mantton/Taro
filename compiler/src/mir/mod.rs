use crate::{
    hir::DefinitionID,
    sema::models::Ty,
    span::{Span, Symbol},
    thir::{self, FieldIndex, VariantIndex},
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

pub mod analysis;
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

/// Describes how a function parameter can escape.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ParamEscapeInfo {
    /// Parameter leaks to heap (stored in global, escapes through called function, etc.)
    pub leaks_to_heap: bool,
    /// Parameter flows to the return value
    pub flows_to_return: bool,
}

/// Escape summary for an entire function.
/// Describes how each parameter's references escape (or don't).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EscapeSummary {
    /// Escape info for each parameter (indexed by parameter position)
    pub params: Vec<ParamEscapeInfo>,
}

#[derive(Debug, Clone)]
pub struct Body<'ctx> {
    pub owner: DefinitionID,
    pub locals: IndexVec<LocalId, LocalDecl<'ctx>>,
    pub basic_blocks: IndexVec<BasicBlockId, BasicBlockData<'ctx>>,
    pub start_block: BasicBlockId,
    pub return_local: LocalId,
    pub escape_locals: Vec<bool>,
    pub phase: MirPhase,
    pub is_async: bool,
}

#[derive(Debug, Clone)]
pub struct LocalDecl<'ctx> {
    pub ty: Ty<'ctx>,
    pub kind: LocalKind,
    pub mutable: bool,
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
    ShadowResync(Vec<LocalId>),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallUnwindAction {
    Cleanup(BasicBlockId),
    Terminate,
}

#[derive(Debug, Clone)]
pub struct DevirtHint<'ctx> {
    pub impl_def_id: DefinitionID,
    pub impl_args: GenericArguments<'ctx>,
    pub concrete_self_ty: Ty<'ctx>,
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
    ResumeUnwind,
    Unreachable,
    Call {
        func: Operand<'ctx>,
        args: Vec<Operand<'ctx>>,
        devirt_hint: Option<DevirtHint<'ctx>>,
        destination: Place<'ctx>,
        target: BasicBlockId,
        unwind: CallUnwindAction,
    },
    /// Suspend point for async/await. Marks where an async function
    /// yields control back to the executor while awaiting a future.
    /// The state machine transform (Phase 5) will expand this into
    /// poll calls and state transitions.
    Yield {
        /// The future being awaited
        value: Operand<'ctx>,
        /// Block to jump to when resumed with the ready value
        resume: BasicBlockId,
        /// Place to write the awaited value into on resume
        resume_arg: Place<'ctx>,
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

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CopyModifiers {
    pub take: bool,
    pub init: bool,
}

#[derive(Debug, Clone)]
pub enum Operand<'ctx> {
    Copy(Place<'ctx>),
    Move(Place<'ctx>),
    CopyWith(Place<'ctx>, CopyModifiers),
    Constant(Constant<'ctx>),
}

impl<'ctx> Operand<'ctx> {
    #[inline]
    pub fn copy(place: Place<'ctx>) -> Self {
        Self::Copy(place)
    }

    #[inline]
    pub fn move_(place: Place<'ctx>) -> Self {
        Self::Move(place)
    }

    #[inline]
    pub fn copy_with(place: Place<'ctx>, modifiers: CopyModifiers) -> Self {
        if modifiers.take || modifiers.init {
            Self::CopyWith(place, modifiers)
        } else {
            Self::Copy(place)
        }
    }

    #[inline]
    pub fn as_copy(&self) -> Option<(&Place<'ctx>, CopyModifiers)> {
        match self {
            Self::Copy(place) => Some((place, CopyModifiers::default())),
            Self::CopyWith(place, modifiers) => Some((place, *modifiers)),
            Self::Move(_) | Self::Constant(_) => None,
        }
    }

    #[inline]
    pub fn modifiers_or_default(&self) -> CopyModifiers {
        self.as_copy().map(|(_, m)| m).unwrap_or_default()
    }
}

#[derive(Debug, Clone)]
pub struct Constant<'ctx> {
    pub ty: Ty<'ctx>,
    pub value: ConstantKind<'ctx>,
}

use crate::sema::models::{GenericArguments, GenericParameter};

#[derive(Debug, Clone)]
pub enum ConstantKind<'ctx> {
    Bool(bool),
    Rune(char),
    String(Symbol),
    Integer(u64),
    Float(f64),
    Unit,
    Function(DefinitionID, GenericArguments<'ctx>, Ty<'ctx>),
    GlobalVariableAddress(DefinitionID),
    ConstParam(GenericParameter),
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
        kind: CastKind<'ctx>,
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

pub fn for_each_function_constant_in_body<'ctx>(
    body: &Body<'ctx>,
    mut visit: impl FnMut(DefinitionID, GenericArguments<'ctx>),
) {
    for block in &body.basic_blocks {
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Assign(_, rvalue) => {
                    for_each_function_constant_in_rvalue(rvalue, &mut visit);
                }
                StatementKind::ShadowResync(_)
                | StatementKind::GcSafepoint
                | StatementKind::Nop
                | StatementKind::SetDiscriminant { .. } => {}
            }
        }

        if let Some(terminator) = &block.terminator {
            match &terminator.kind {
                TerminatorKind::Call { func, args, .. } => {
                    for_each_function_constant_in_operand(func, &mut visit);
                    for argument in args {
                        for_each_function_constant_in_operand(argument, &mut visit);
                    }
                }
                TerminatorKind::Yield { value, .. } => {
                    for_each_function_constant_in_operand(value, &mut visit);
                }
                _ => {}
            }
        }
    }
}

fn for_each_function_constant_in_rvalue<'ctx>(
    rvalue: &Rvalue<'ctx>,
    visit: &mut impl FnMut(DefinitionID, GenericArguments<'ctx>),
) {
    match rvalue {
        Rvalue::Use(operand) => for_each_function_constant_in_operand(operand, visit),
        Rvalue::UnaryOp { operand, .. } => for_each_function_constant_in_operand(operand, visit),
        Rvalue::BinaryOp { lhs, rhs, .. } => {
            for_each_function_constant_in_operand(lhs, visit);
            for_each_function_constant_in_operand(rhs, visit);
        }
        Rvalue::Cast { operand, .. } => for_each_function_constant_in_operand(operand, visit),
        Rvalue::Aggregate { fields, .. } => {
            for field in fields.iter() {
                for_each_function_constant_in_operand(field, visit);
            }
        }
        Rvalue::Repeat { operand, .. } => for_each_function_constant_in_operand(operand, visit),
        Rvalue::Ref { .. } | Rvalue::Discriminant { .. } | Rvalue::Alloc { .. } => {}
    }
}

fn for_each_function_constant_in_operand<'ctx>(
    operand: &Operand<'ctx>,
    visit: &mut impl FnMut(DefinitionID, GenericArguments<'ctx>),
) {
    if let Operand::Constant(constant) = operand {
        if let ConstantKind::Function(def_id, args, _) = constant.value {
            visit(def_id, args);
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum CastKind<'ctx> {
    Numeric,
    BoxExistential,
    ExistentialUpcast,
    /// Runtime type test: `value is Target`.
    ExistentialTypeIs {
        target: Ty<'ctx>,
    },
    /// Runtime assertion cast: `value as? Target`.
    ExistentialTryCast {
        target: Ty<'ctx>,
    },
    Pointer,
    /// Coerce a non-capturing closure to a function pointer
    ClosureToFnPointer,
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
    /// Closure environment construction
    Closure {
        def_id: DefinitionID,
        captured_generics: GenericArguments<'ctx>,
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
            | thir::ExprKind::Upvar { .. }
            | thir::ExprKind::Field { .. } => Category::Place,

            thir::ExprKind::Reference { .. }
            | thir::ExprKind::If { .. }
            | thir::ExprKind::Match { .. }
            | thir::ExprKind::Return { .. }
            | thir::ExprKind::Break
            | thir::ExprKind::Continue
            | thir::ExprKind::Call { .. }
            | thir::ExprKind::BoxExistential { .. }
            | thir::ExprKind::ExistentialUpcast { .. }
            | thir::ExprKind::Block(..)
            | thir::ExprKind::Adt(..)
            | thir::ExprKind::Closure { .. }
            | thir::ExprKind::ListLiteral { .. }
            | thir::ExprKind::Await { .. } => Category::Rvalue(RvalueFunc::Into),

            thir::ExprKind::Assign { .. }
            | thir::ExprKind::AssignOp { .. }
            | thir::ExprKind::Binary { .. }
            | thir::ExprKind::Logical { .. }
            | thir::ExprKind::Unary { .. }
            | thir::ExprKind::Cast { .. }
            | thir::ExprKind::ExistentialTryCast { .. }
            | thir::ExprKind::ExistentialTypeIs { .. }
            | thir::ExprKind::ClosureToFnPointer { .. }
            | thir::ExprKind::Tuple { .. }
            | thir::ExprKind::Array { .. }
            | thir::ExprKind::Repeat { .. }
            | thir::ExprKind::Make { .. } => Category::Rvalue(RvalueFunc::AsRvalue),

            thir::ExprKind::Literal(..) | thir::ExprKind::Zst { .. } => Category::Constant,
        }
    }
}
