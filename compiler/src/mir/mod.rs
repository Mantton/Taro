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

pub(crate) mod class_defaults;
pub mod const_eval;
pub mod copy_clone;
pub(crate) mod function_pointer_call;

pub(crate) mod gc_lowering;

pub mod optimize;
pub mod package;
pub mod pretty;
pub(crate) mod primitive_operators;
pub(crate) mod tuple_conformances;
#[cfg(test)]
pub(crate) mod test_support;
#[cfg(test)]
mod tests;
pub(crate) mod vet;

index_vec::define_index_type! {
    pub struct LocalId = u32;
}

index_vec::define_index_type! {
    pub struct BasicBlockId = u32;
}

index_vec::define_index_type! {
    pub struct SourceScopeId = u32;
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

/// Conservative call effects measured in dereferences from one argument.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ParamEscapeSummary {
    /// `Some(0)` retains the argument; `Some(n)` retains its nth pointee.
    pub heap_deref: Option<u8>,
    pub return_deref: Option<u8>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InstanceEscapeSummary {
    pub params: Vec<ParamEscapeSummary>,
}

#[derive(Debug, Clone)]
pub struct Body<'ctx> {
    /// Concrete-instance escape placement; recomputed rather than serialized.
    pub escape_locals: Vec<bool>,

    pub owner: DefinitionID,
    /// Logical source functions represented in this physical MIR body.
    /// Scope zero is always the physical function itself.
    pub source_scopes: IndexVec<SourceScopeId, SourceScopeData>,
    pub locals: IndexVec<LocalId, LocalDecl<'ctx>>,
    pub basic_blocks: IndexVec<BasicBlockId, BasicBlockData<'ctx>>,
    pub start_block: BasicBlockId,
    pub return_local: LocalId,
    pub phase: MirPhase,
    pub is_async: bool,
    /// Present on pre-transform synchronous generator bodies; cleared once
    /// `GeneratorTransform` lowers the body into a constructor + step thunk.
    pub generator_element_ty: Option<Ty<'ctx>>,
}

impl<'ctx> Body<'ctx> {
    /// Resolve a place in the body's generic context. Field projections carry
    /// their instantiated type; enum downcasts recover the payload tuple from
    /// the enum's arguments. Codegen applies its instance substitution afterward.
    pub fn place_ty(
        &self,
        gcx: crate::compile::context::Gcx<'ctx>,
        place: &Place<'ctx>,
    ) -> Ty<'ctx> {
        self.place_ty_with(gcx, place, |ty| {
            crate::sema::tycheck::utils::normalize_aliases(gcx, ty)
        })
    }

    /// Resolve each base before applying its projection. Concrete instances
    /// must substitute a generic enum before selecting the variant payload;
    /// substituting an Error produced by an earlier symbolic downcast is too late.
    pub(crate) fn place_ty_with(
        &self,
        gcx: crate::compile::context::Gcx<'ctx>,
        place: &Place<'ctx>,
        mut normalize: impl FnMut(Ty<'ctx>) -> Ty<'ctx>,
    ) -> Ty<'ctx> {
        let mut ty = self.locals[place.local].ty;
        for projection in &place.projection {
            ty = normalize(ty);
            ty = match projection {
                PlaceElem::Deref => ty.dereference().unwrap_or_else(|| Ty::error(gcx)),
                PlaceElem::Field(_, field_ty) => *field_ty,
                PlaceElem::VariantDowncast { index, .. } => {
                    let crate::sema::models::TyKind::Adt(def, args) = ty.kind() else {
                        return Ty::error(gcx);
                    };
                    if def.kind != crate::sema::models::AdtKind::Enum {
                        return Ty::error(gcx);
                    }
                    enum_variant_tuple_ty(gcx, def.id, *index, args)
                }
            };
        }
        normalize(ty)
    }

    pub fn operand_ty(
        &self,
        gcx: crate::compile::context::Gcx<'ctx>,
        operand: &Operand<'ctx>,
    ) -> Ty<'ctx> {
        match operand {
            Operand::Constant(constant) => constant.ty,
            Operand::Copy(place) | Operand::CopyWith(place, _) => self.place_ty(gcx, place),
        }
    }

    /// Incoming control-flow edges, preserving edge order and duplicate targets.
    pub fn predecessors(&self) -> IndexVec<BasicBlockId, Vec<BasicBlockId>> {
        let mut predecessors = IndexVec::from(vec![Vec::new(); self.basic_blocks.len()]);
        for (block, data) in self.basic_blocks.iter_enumerated() {
            if let Some(terminator) = &data.terminator {
                for successor in terminator.kind.successors() {
                    predecessors[successor].push(block);
                }
            }
        }
        predecessors
    }

    pub fn initial_source_scopes(owner: DefinitionID) -> IndexVec<SourceScopeId, SourceScopeData> {
        let mut scopes: IndexVec<SourceScopeId, SourceScopeData> = IndexVec::new();
        let root: SourceScopeId = scopes.push(SourceScopeData {
            definition: owner,
            callsite: None,
            parent: None,
        });
        debug_assert_eq!(root.index(), 0);
        scopes
    }
}

/// The selected enum payload, instantiated in the enum's generic context.
pub(crate) fn enum_variant_tuple_ty<'ctx>(
    gcx: crate::compile::context::Gcx<'ctx>,
    def_id: DefinitionID,
    variant_index: VariantIndex,
    args: GenericArguments<'ctx>,
) -> Ty<'ctx> {
    use crate::sema::{
        models::{EnumVariantKind, TyKind},
        tycheck::utils::instantiate::instantiate_ty_with_args,
    };

    let variant = &gcx.get_enum_definition(def_id).variants[variant_index.index()];
    match variant.kind {
        EnumVariantKind::Unit => gcx.types.void,
        EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) => Ty::new(
            TyKind::Tuple(
                gcx.store.interners.intern_ty_list(
                    fields
                        .iter()
                        .map(|field| instantiate_ty_with_args(gcx, field.ty, args))
                        .collect(),
                ),
            ),
            gcx,
        ),
    }
}

/// One logical function scope represented inside a physical MIR body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceScopeData {
    pub definition: DefinitionID,
    /// Source location at which this scope was inlined into its parent.
    /// The physical root has no callsite.
    pub callsite: Option<Span>,
    pub parent: Option<SourceScopeId>,
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
    /// Private value-initializer storage. Its fields start uninitialized;
    /// readonly stores require a separate once-only control-flow proof.
    ConstructorSelf,
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

/// Compiler-inserted cooperation point; never a source-language operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum GcSafepointKind {
    Entry,
    Loop,
}

#[derive(Debug, Clone)]
pub enum StatementKind<'ctx> {
    /// Switches the logical source scope for subsequent operations in this
    /// basic block. Code generation resets to scope zero at every block.
    SourceScope(SourceScopeId),
    /// Starts a new source-level binding lifetime for `local`.
    ///
    /// Unlike an assignment, this marker runs again whenever control re-enters
    /// a declaration (for example, on each loop iteration). Passes that move a
    /// local to stable storage use it to distinguish rebinding from mutation.
    StorageLive(LocalId),
    /// Ends the source storage lifetime after lexical cleanup. This is not a
    /// destructor call and does not end borrows of other storage carried by it.
    StorageDead(LocalId),
    /// Publishes that a compiler-lowered aggregate store
    /// sequence has fully initialized `local`.
    ///
    /// This is an initialization-analysis fact only and emits no machine code.
    /// Earlier partial field stores are not a complete value.
    SetInitialized(LocalId),
    Assign(Place<'ctx>, Rvalue<'ctx>),

    /// A compiler-only use that extends an operand's lifetime without
    /// generating machine code.
    KeepAlive(Operand<'ctx>),
    Nop,
    SetDiscriminant {
        place: Place<'ctx>,
        variant_index: VariantIndex,
    },
    GcSafepoint(GcSafepointKind),
}

#[derive(Debug, Clone)]
pub struct Terminator<'ctx> {
    pub kind: TerminatorKind<'ctx>,
    pub span: Span,
}

impl StatementKind<'_> {
    /// Only these markers may separate scanner lifetime start from a full
    /// overwrite. New statements must explicitly choose the conservative side.
    #[cfg(feature = "llvm")]
    pub(crate) fn scanner_copy_marker(&self, destination: LocalId) -> bool {
        match self {
            Self::SourceScope(_) | Self::Nop => true,
            Self::StorageLive(local) => *local != destination,
            Self::StorageDead(_)
            | Self::SetInitialized(_)
            | Self::Assign(..)
            | Self::KeepAlive(_)
            | Self::SetDiscriminant { .. }
            | Self::GcSafepoint(_) => false,
        }
    }
}

impl<'ctx> TerminatorKind<'ctx> {
    /// Address-taking analysis must classify new native control-flow effects.
    #[cfg(feature = "llvm")]
    pub(crate) fn call_arguments(&self) -> Option<&[Operand<'ctx>]> {
        match self {
            Self::Call { args, .. } => Some(args),
            Self::Goto { .. }
            | Self::UnresolvedGoto
            | Self::SwitchInt { .. }
            | Self::Return
            | Self::ResumeUnwind
            | Self::Unreachable
            | Self::Yield { .. }
            | Self::GeneratorYield { .. } => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallUnwindAction {
    Cleanup(BasicBlockId),
    Terminate,
}

/// Whether and how a call participates in GC coordination.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallEffect {
    Direct,
    Taro,
    Callback,
    Blocking,
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
        /// Checked Task.result may complete without initializing a T. This
        /// executable edge carries no destination initialization/drop flag.
        no_result: Option<BasicBlockId>,
        /// Normal control-flow path that runs the active cleanup chain when a
        /// suspended task is cancelled. The async transform replaces the
        /// terminal marker at the end of this path with a cancelled poll
        /// return.
        cancel: BasicBlockId,
        /// Terminal marker reached after the cancellation cleanup chain has
        /// completed normally.
        cancel_complete: BasicBlockId,
        /// Unwind path for a panic raised while polling or destroying the
        /// awaited child future. This preserves the same active defer chain
        /// that surrounded the source-level `await`.
        unwind: CallUnwindAction,
    },

    /// Suspend point for a generator `yield value`.
    GeneratorYield {
        /// The yielded element value
        value: Operand<'ctx>,
        /// Block to jump to on the next `next()` resume
        resume: BasicBlockId,
        /// Cleanup path run when the generator is closed while suspended here
        cancel: BasicBlockId,
        /// Terminal marker reached after `cancel` cleanup finishes
        cancel_complete: BasicBlockId,
    },
}

impl<'a> TerminatorKind<'a> {
    /// Ordered control-flow edges, including cleanup and cancellation paths.
    /// Keep duplicate switch targets: consumers decide whether to deduplicate.
    /// `cancel_complete` names a later marker, not an immediate yield successor.
    pub fn successors(&self) -> Vec<BasicBlockId> {
        match self {
            Self::Goto { target } => vec![*target],
            Self::SwitchInt {
                targets, otherwise, ..
            } => targets
                .iter()
                .map(|(_, target)| *target)
                .chain(std::iter::once(*otherwise))
                .collect(),
            Self::Call { target, unwind, .. } => {
                let mut edges = vec![*target];
                if let CallUnwindAction::Cleanup(cleanup) = unwind {
                    edges.push(*cleanup);
                }
                edges
            }
            Self::Yield {
                resume,
                cancel,
                no_result,
                unwind,
                ..
            } => {
                let mut edges = vec![*resume, *cancel];
                if let CallUnwindAction::Cleanup(cleanup) = unwind {
                    edges.push(*cleanup);
                }
                edges.extend(no_result.iter().copied());
                edges
            }
            Self::GeneratorYield { resume, cancel, .. } => vec![*resume, *cancel],
            Self::Return | Self::ResumeUnwind | Self::Unreachable | Self::UnresolvedGoto => {
                Vec::new()
            }
        }
    }

    /// Rewrite every stored block reference, including async cancellation
    /// metadata. Unlike `successors`, this also visits `cancel_complete`.
    pub fn map_blocks(&mut self, mut map: impl FnMut(BasicBlockId) -> BasicBlockId) {
        match self {
            Self::Goto { target } => *target = map(*target),
            Self::SwitchInt {
                targets, otherwise, ..
            } => {
                for (_, target) in targets {
                    *target = map(*target);
                }
                *otherwise = map(*otherwise);
            }
            Self::Call { target, unwind, .. } => {
                *target = map(*target);
                if let CallUnwindAction::Cleanup(cleanup) = unwind {
                    *cleanup = map(*cleanup);
                }
            }
            Self::Yield {
                resume,
                cancel,
                cancel_complete,
                no_result,
                unwind,
                ..
            } => {
                *no_result = no_result.map(&mut map);
                *resume = map(*resume);
                *cancel = map(*cancel);
                *cancel_complete = map(*cancel_complete);
                if let CallUnwindAction::Cleanup(cleanup) = unwind {
                    *cleanup = map(*cleanup);
                }
            }
            Self::GeneratorYield {
                resume,
                cancel,
                cancel_complete,
                ..
            } => {
                *resume = map(*resume);
                *cancel = map(*cancel);
                *cancel_complete = map(*cancel_complete);
            }
            Self::Return | Self::ResumeUnwind | Self::Unreachable | Self::UnresolvedGoto => {}
        }
    }

    /// Redirect one executable edge in `successors()` order. In particular,
    /// async `cancel_complete` is metadata, not a third executable yield edge.
    /// Distinct edges may share a destination and still need different cleanup.
    pub fn replace_successor(&mut self, edge: usize, replacement: BasicBlockId) -> bool {
        let slot = match self {
            Self::Goto { target } if edge == 0 => Some(target),
            Self::SwitchInt {
                targets, otherwise, ..
            } => {
                if edge < targets.len() {
                    Some(&mut targets[edge].1)
                } else if edge == targets.len() {
                    Some(otherwise)
                } else {
                    None
                }
            }
            Self::Call { target, unwind, .. } => {
                if edge == 0 {
                    Some(target)
                } else if edge == 1 {
                    match unwind {
                        CallUnwindAction::Cleanup(block) => Some(block),
                        _ => None,
                    }
                } else {
                    None
                }
            }
            Self::Yield {
                resume,
                cancel,
                no_result,
                unwind,
                ..
            } => match (edge, unwind) {
                (0, _) => Some(resume),
                (1, _) => Some(cancel),
                (2, CallUnwindAction::Cleanup(block)) => Some(block),
                (2, CallUnwindAction::Terminate) | (3, CallUnwindAction::Cleanup(_)) => {
                    no_result.as_mut()
                }
                _ => None,
            },
            Self::GeneratorYield { resume, cancel, .. } => match edge {
                0 => Some(resume),
                1 => Some(cancel),
                _ => None,
            },
            _ => None,
        };
        if let Some(slot) = slot {
            *slot = replacement;
            true
        } else {
            false
        }
    }

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
    pub init: bool,
}

#[derive(Debug, Clone)]
pub enum Operand<'ctx> {
    Copy(Place<'ctx>),
    CopyWith(Place<'ctx>, CopyModifiers),
    Constant(Constant<'ctx>),
}

impl<'ctx> Operand<'ctx> {
    #[inline]
    pub fn copy(place: Place<'ctx>) -> Self {
        Self::Copy(place)
    }

    #[inline]
    pub fn copy_with(place: Place<'ctx>, modifiers: CopyModifiers) -> Self {
        if modifiers.init {
            Self::CopyWith(place, modifiers)
        } else {
            Self::Copy(place)
        }
    }

    #[inline]
    pub fn place(&self) -> Option<&Place<'ctx>> {
        match self {
            Self::Copy(place) | Self::CopyWith(place, _) => Some(place),
            Self::Constant(_) => None,
        }
    }

    #[inline]
    pub fn place_mut(&mut self) -> Option<&mut Place<'ctx>> {
        match self {
            Self::Copy(place) | Self::CopyWith(place, _) => Some(place),
            Self::Constant(_) => None,
        }
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
    Bytes(crate::span::InternedBytes),
    ConstArray(crate::interner::InternedConstArray),
    Bool(bool),
    Rune(char),
    String(Symbol),
    Integer(u64),
    Float(f64),
    Unit,
    Function(DefinitionID, GenericArguments<'ctx>, Ty<'ctx>),
    GlobalVariableAddress(DefinitionID),
    ConstParam(GenericParameter),
    /// Select the concrete witness after substituting the caller’s generic arguments.
    InterfaceConstant(DefinitionID, GenericArguments<'ctx>),
}

#[derive(Debug, Clone)]
pub enum Rvalue<'ctx> {
    Use(Operand<'ctx>),
    /// Copy an initialized value, including independent erased payload storage.
    /// It follows ordinary value/handle semantics and never calls user Clone.
    CopyValue {
        source: Place<'ctx>,
    },
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
        place: Place<'ctx>,
    },
    /// Compiler-only address for traversing cleanup metadata. This does not
    /// read the value or revive the data dependencies of expired borrows.
    /// Produces a raw mutable pointer to the place's storage, never a borrow.
    CleanupAddress {
        place: Place<'ctx>,
    },
    Discriminant {
        place: Place<'ctx>,
    },
    /// The all-zero bit pattern for `ty`.
    ///
    /// Used for explicit zeroed storage and compiler initialization state.
    Zeroed {
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
    /// Managed storage, materialized after concrete escape placement.
    Alloc {
        ty: Ty<'ctx>,
    },
}

impl<'ctx> Rvalue<'ctx> {
    /// Every address-forming operation must be classified here. GC placement
    /// and scanner-initialization proofs must not silently miss a new variant.
    #[cfg(feature = "llvm")]
    pub(crate) fn addressed_place(&self) -> Option<&Place<'ctx>> {
        match self {
            Self::Ref { place } | Self::CleanupAddress { place } => Some(place),
            Self::Use(_)
            | Self::CopyValue { .. }
            | Self::UnaryOp { .. }
            | Self::BinaryOp { .. }
            | Self::Cast { .. }
            | Self::Discriminant { .. }
            | Self::Zeroed { .. }
            | Self::Aggregate { .. }
            | Self::Repeat { .. }
            | Self::Alloc { .. } => None,
        }
    }

    pub fn for_each_operand(&self, mut visit: impl FnMut(&Operand<'ctx>)) {
        match self {
            Self::Use(operand)
            | Self::UnaryOp { operand, .. }
            | Self::Cast { operand, .. }
            | Self::Repeat { operand, .. } => visit(operand),
            Self::BinaryOp { lhs, rhs, .. } => {
                visit(lhs);
                visit(rhs);
            }
            Self::Aggregate { fields, .. } => fields.iter().for_each(visit),
            Self::Ref { .. }
            | Self::CopyValue { .. }
            | Self::CleanupAddress { .. }
            | Self::Discriminant { .. }
            | Self::Alloc { .. }
            | Self::Zeroed { .. } => {}
        }
    }

    pub fn for_each_operand_mut(&mut self, mut visit: impl FnMut(&mut Operand<'ctx>)) {
        match self {
            Self::Use(operand)
            | Self::UnaryOp { operand, .. }
            | Self::Cast { operand, .. }
            | Self::Repeat { operand, .. } => visit(operand),
            Self::BinaryOp { lhs, rhs, .. } => {
                visit(lhs);
                visit(rhs);
            }
            Self::Aggregate { fields, .. } => fields.iter_mut().for_each(visit),
            Self::Ref { .. }
            | Self::CopyValue { .. }
            | Self::CleanupAddress { .. }
            | Self::Discriminant { .. }
            | Self::Alloc { .. }
            | Self::Zeroed { .. } => {}
        }
    }

    /// Includes address-taking and discriminant places, which are not operands.
    pub fn for_each_place(&self, mut visit: impl FnMut(&Place<'ctx>)) {
        match self {
            Self::Ref { place, .. }
            | Self::CleanupAddress { place }
            | Self::Discriminant { place } => visit(place),
            Self::CopyValue { source } => visit(source),
            _ => self.for_each_operand(|operand| {
                if let Some(place) = operand.place() {
                    visit(place);
                }
            }),
        }
    }

    pub fn for_each_place_mut(&mut self, mut visit: impl FnMut(&mut Place<'ctx>)) {
        match self {
            Self::Ref { place, .. }
            | Self::CleanupAddress { place }
            | Self::Discriminant { place } => visit(place),
            Self::CopyValue { source } => visit(source),
            _ => self.for_each_operand_mut(|operand| {
                if let Some(place) = operand.place_mut() {
                    visit(place);
                }
            }),
        }
    }
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

                StatementKind::KeepAlive(operand) => {
                    for_each_function_constant_in_operand(operand, &mut visit);
                }
                StatementKind::SourceScope(_)
                | StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::SetInitialized(_)
                | StatementKind::GcSafepoint(_)
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
                TerminatorKind::Yield { value, .. }
                | TerminatorKind::GeneratorYield { value, .. } => {
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
    if let Rvalue::Aggregate {
        kind: AggregateKind::Closure {
            def_id,
            captured_generics,
        },
        ..
    } = rvalue
    {
        visit(*def_id, *captured_generics);
    }
    rvalue.for_each_operand(|operand| for_each_function_constant_in_operand(operand, visit));
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
    /// Extract a native string/erased owner or a reference's permission control
    /// for compiler-generated cleanup. Reading a reference's control does not
    /// read its referent or extend the referent's data-access lifetime.
    /// This does not transfer an owner separately from its cleanup obligation.
    /// Unsafe object identity extraction also unwraps class-only existential
    /// payload storage. This is distinct from extracting its box for cleanup.
    ClassObjectOwner,
    /// Publish a freshly allocated object's class header and wrap it as a
    /// typed class handle.
    NativeClassHandle,
    /// Wrap the address of an already initialized object as a typed class
    /// handle, without touching its header.
    ClassFromOwner,
    ClassUpcast,
    /// Compiler-proven direct dynamic-Self class result adaptation.
    ClassSelfResult,
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

impl<'ctx> AggregateKind<'ctx> {
    /// These constructors only copy scalar values or shared handles. Keeping
    /// them whole lets codegen define inactive payload bytes at construction,
    /// without an earlier scanner clear. Inline aggregates, erased payloads
    /// and unresolved generics retain the ordinary copy/field-store path.
    pub(crate) fn noncollecting_enum_ctor(
        &self,
        gcx: crate::compile::context::Gcx<'ctx>,
    ) -> Option<DefinitionID> {
        use crate::sema::models::{EnumVariantKind, TyKind};
        use crate::sema::tycheck::utils::{
            instantiate::instantiate_ty_with_args, normalize_aliases,
        };
        let Self::Adt {
            def_id,
            variant_index: Some(index),
            generic_args,
        } = self
        else {
            return None;
        };
        if gcx.definition_kind(*def_id) != crate::hir::DefinitionKind::Enum {
            return None;
        }
        let variant = gcx.enum_variant_by_index(*def_id, *index);
        let fields = match variant.kind {
            EnumVariantKind::Unit => return Some(variant.ctor_def_id),
            EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) => fields,
        };
        fields
            .iter()
            .all(|field| {
                let ty =
                    normalize_aliases(gcx, instantiate_ty_with_args(gcx, field.ty, *generic_args));
                matches!(
                    ty.kind(),
                    TyKind::Bool
                        | TyKind::Rune
                        | TyKind::Int(_)
                        | TyKind::UInt(_)
                        | TyKind::Float(_)
                        | TyKind::String
                        | TyKind::Pointer(..)
                        | TyKind::Reference(_)
                        | TyKind::FnPointer { .. }
                )
            })
            .then_some(variant.ctor_def_id)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum UnaryOperator {
    LogicalNot,
    Negate,
    BitwiseNot,
}

/// Operators a primitive compound assignment may apply inside one class-field
/// access. The spelling travels as a constant intrinsic argument.
const COMPOUND_OPERATORS: [(BinaryOperator, &str); 10] = [
    (BinaryOperator::Add, "add"),
    (BinaryOperator::Sub, "sub"),
    (BinaryOperator::Mul, "mul"),
    (BinaryOperator::Div, "div"),
    (BinaryOperator::Rem, "rem"),
    (BinaryOperator::BitAnd, "and"),
    (BinaryOperator::BitOr, "or"),
    (BinaryOperator::BitXor, "xor"),
    (BinaryOperator::BitShl, "shl"),
    (BinaryOperator::BitShr, "shr"),
];

impl BinaryOperator {
    pub fn compound_name(self) -> Option<&'static str> {
        COMPOUND_OPERATORS
            .iter()
            .find(|(op, _)| std::mem::discriminant(op) == std::mem::discriminant(&self))
            .map(|(_, name)| *name)
    }

    pub fn from_compound_name(name: &str) -> Option<Self> {
        COMPOUND_OPERATORS
            .iter()
            .find(|(_, candidate)| *candidate == name)
            .map(|(op, _)| *op)
    }
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
            | thir::ExprKind::Loop { .. }
            | thir::ExprKind::Break { .. }
            | thir::ExprKind::Continue { .. }
            | thir::ExprKind::Call { .. }
            | thir::ExprKind::BoxExistential { .. }
            | thir::ExprKind::ExistentialUpcast { .. }
            | thir::ExprKind::Block(..)
            | thir::ExprKind::Adt(..)
            | thir::ExprKind::Closure { .. }
            | thir::ExprKind::ListLiteral { .. }
            | thir::ExprKind::Await { .. }
            | thir::ExprKind::Yield { .. }
            | thir::ExprKind::AwaitAsyncVar { .. }
            | thir::ExprKind::Select { .. } => Category::Rvalue(RvalueFunc::Into),

            thir::ExprKind::Assign { .. }
            | thir::ExprKind::AssignOp { .. }
            | thir::ExprKind::Binary { .. }
            | thir::ExprKind::ClassIdentity { .. }
            | thir::ExprKind::Logical { .. }
            | thir::ExprKind::Unary { .. }
            | thir::ExprKind::Cast { .. }
            | thir::ExprKind::ClassUpcast { .. }
            | thir::ExprKind::ClassSelfResult { .. }
            | thir::ExprKind::ExistentialTryCast { .. }
            | thir::ExprKind::ExistentialTypeIs { .. }
            | thir::ExprKind::ClosureToFnPointer { .. }
            | thir::ExprKind::Tuple { .. }
            | thir::ExprKind::Array { .. }
            | thir::ExprKind::Repeat { .. } => Category::Rvalue(RvalueFunc::AsRvalue),

            thir::ExprKind::Literal(..) | thir::ExprKind::Zst { .. } => Category::Constant,
        }
    }
}
