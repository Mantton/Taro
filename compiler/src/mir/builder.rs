use crate::{
    compile::context::Gcx,
    hir::{self, StdInterface},
    mir::{
        self, BasicBlockData, BasicBlockId, BlockAnd, BlockAndExtension, Body, LocalDecl, LocalId,
        LocalKind, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
        pretty::PrettyPrintMir,
    },
    sema::models::{AdtKind, Constraint, EnumVariantKind, LabeledFunctionSignature, Ty, TyKind},
    span::{Span, Symbol},
    thir,
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;
use std::mem;

mod block;
mod expression;

index_vec::define_index_type! {
    struct CleanupId = u32;
}

#[derive(Clone, Copy, Debug)]
struct CleanupNode {
    action: CleanupAction,
    parent: Option<CleanupId>,
    span: Span,
}

#[derive(Clone, Copy, Debug)]
enum CleanupAction {
    DeferBlock(thir::BlockId),
}

#[derive(Debug)]
struct PendingEdge {
    block: BasicBlockId,
    cleanup: Option<CleanupId>,
    _span: Span,
}

#[derive(Debug)]
struct IfThenScope {
    cleanup_at_entry: Option<CleanupId>,
    else_edges: Vec<PendingEdge>,
}

#[derive(Clone, Copy, Debug)]
pub enum BreakExit {
    /// Exits the function (after running cleanups) via a dedicated return block.
    Return,
    /// Exits to a lazily-created block (e.g. loop "after" block).
    FreshBlock,
    /// Exits to an existing target block.
    Target(BasicBlockId),
}

#[derive(Debug)]
pub struct BreakableScope {
    cleanup_at_entry: Option<CleanupId>,
    break_exit: BreakExit,
    continue_target: Option<BasicBlockId>,
    break_edges: Vec<PendingEdge>,
    continue_edges: Vec<PendingEdge>,
}

#[derive(Clone, Copy)]
pub enum EdgeKind {
    Break,
    Continue,
}

pub struct MirBuilder<'ctx, 'thir> {
    gcx: Gcx<'ctx>,
    thir: &'thir thir::ThirFunction<'ctx>,
    body: Body<'ctx>,
    locals: FxHashMap<hir::NodeID, LocalId>,
    place_bindings: FxHashMap<hir::NodeID, Place<'ctx>>,
    /// Tracks MIR locals by (arm_id, binding_name) for or-patterns.
    /// Ensures all alternatives in an or-pattern share the same local.
    arm_binding_locals: FxHashMap<(thir::ArmId, Symbol), LocalId>,
    cleanup_nodes: IndexVec<CleanupId, CleanupNode>,
    current_cleanup: Option<CleanupId>,
    resume_unwind_block: Option<BasicBlockId>,
    if_then_scope: Option<IfThenScope>,
    breakable_scopes: Vec<BreakableScope>,
}

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn build_function(gcx: Gcx<'ctx>, function: &'thir thir::ThirFunction<'ctx>) -> Body<'ctx> {
        let signature = gcx.get_signature(function.id);
        let output_ty = signature.output;
        let entry_span = function.span;

        let mut body = Body {
            owner: function.id,
            locals: Default::default(),
            basic_blocks: Default::default(),
            start_block: BasicBlockId::from_raw(0),
            return_local: LocalId::from_raw(0),
            escape_locals: Vec::new(),
            phase: mir::MirPhase::Built,
        };

        // Create return place first.
        let ret_local = body.locals.push(LocalDecl {
            ty: output_ty,
            kind: LocalKind::Return,
            mutable: true,
            name: Some(gcx.intern_symbol("$ret")),
            span: entry_span,
        });
        body.escape_locals.push(false);
        body.return_local = ret_local;

        let mut builder = MirBuilder {
            gcx,
            thir: function,
            body,
            locals: FxHashMap::default(),
            place_bindings: FxHashMap::default(),
            arm_binding_locals: FxHashMap::default(),
            cleanup_nodes: IndexVec::new(),
            current_cleanup: None,
            resume_unwind_block: None,
            if_then_scope: None,
            breakable_scopes: vec![],
        };

        builder.declare_parameters(signature);
        builder.lower_body();
        builder.finish()
    }

    fn finish(self) -> Body<'ctx> {
        self.body
    }

    fn is_type_copyable(&self, ty: Ty<'ctx>) -> bool {
        let TyKind::Parameter(param) = ty.kind() else {
            return self.gcx.is_type_copyable(ty);
        };

        let Some(copy_def) = self.gcx.std_interface_def(StdInterface::Copy) else {
            return false;
        };

        fn interface_has_copy_bound<'ctx>(
            gcx: Gcx<'ctx>,
            interface_id: hir::DefinitionID,
            copy_def: hir::DefinitionID,
            visited: &mut std::collections::HashSet<hir::DefinitionID>,
        ) -> bool {
            if interface_id == copy_def {
                return true;
            }
            if !visited.insert(interface_id) {
                return false;
            }
            let Some(def) = gcx.get_interface_definition(interface_id) else {
                return false;
            };
            def.superfaces.iter().any(|super_iface| {
                interface_has_copy_bound(gcx, super_iface.value.id, copy_def, visited)
            })
        }

        let param_ty = Ty::new(TyKind::Parameter(param), self.gcx);
        self.gcx
            .canonical_constraints_of(self.thir.id)
            .iter()
            .any(|constraint| match constraint.value {
                Constraint::Bound { ty, interface } => {
                    if ty != param_ty {
                        return false;
                    }
                    let mut visited = std::collections::HashSet::new();
                    interface_has_copy_bound(self.gcx, interface.id, copy_def, &mut visited)
                }
                Constraint::TypeEquality(_, _) => false,
            })
    }

    fn declare_parameters(&mut self, signature: &LabeledFunctionSignature<'ctx>) {
        let params: Vec<_> = self
            .thir
            .params
            .iter()
            .zip(signature.inputs.iter())
            .map(|(param, lowered)| (param.id, param.name.clone(), param.span, lowered.ty))
            .collect();
        for (id, name, span, ty) in params {
            let local = self.push_local(ty, LocalKind::Param, false, Some(name), span);
            self.locals.insert(id, local);
        }
    }

    fn lower_body(&mut self) {
        let start_block = self.new_block_with_note("entry".into());
        self.body.start_block = start_block;
        let span = self.thir.span;

        let Some(thir_block) = self.thir.body else {
            self.terminate(start_block, span, TerminatorKind::Unreachable);
            self.finalize_unterminated_blocks();
            return;
        };

        let return_block = self
            .in_breakable_scope(None, BreakExit::Return, span, |this| {
                Some(this.lower_block(Place::return_place(), start_block, thir_block))
            })
            .into_block();
        self.terminate(return_block, span, TerminatorKind::Return);
        self.finalize_unterminated_blocks();
    }

    pub(super) fn push_local(
        &mut self,
        ty: Ty<'ctx>,
        kind: LocalKind,
        mutable: bool,
        name: Option<Symbol>,
        span: Span,
    ) -> LocalId {
        let local = self.body.locals.push(LocalDecl {
            ty,
            kind,
            mutable,
            name,
            span,
        });
        self.body.escape_locals.push(false);
        local
    }

    fn new_temp_with_ty(&mut self, ty: Ty<'ctx>, span: Span) -> LocalId {
        self.push_local(ty, LocalKind::Temp, true, None, span)
    }

    fn new_block(&mut self) -> BasicBlockId {
        self.body.basic_blocks.push(BasicBlockData {
            note: None,
            statements: vec![],
            terminator: None,
        })
    }

    fn new_block_with_note(&mut self, note: String) -> BasicBlockId {
        self.body.basic_blocks.push(BasicBlockData {
            note: Some(note),
            statements: vec![],
            terminator: None,
        })
    }

    fn unit_temp_place(&mut self, span: Span) -> Place<'ctx> {
        let local = self.push_local(self.gcx.types.void, LocalKind::Temp, true, None, span);
        Place::from_local(local)
    }

    fn finalize_unterminated_blocks(&mut self) {
        let span = Span::empty(self.thir.span.file);
        for bb in self.body.basic_blocks.indices() {
            if self.body.basic_blocks[bb].terminator.is_none() {
                self.body.basic_blocks[bb].terminator = Some(Terminator {
                    kind: TerminatorKind::Unreachable,
                    span,
                });
            }
        }

        debug_assert!(
            self.body.basic_blocks.iter().all(|bb| {
                !matches!(
                    bb.terminator.as_ref().expect("terminated").kind,
                    TerminatorKind::UnresolvedGoto
                )
            }),
            "all `UnresolvedGoto` terminators must be patched before finishing"
        );
    }

    fn place_ty(&self, place: &Place<'ctx>) -> Ty<'ctx> {
        let mut ty = self.body.locals[place.local].ty;
        for elem in &place.projection {
            match elem {
                mir::PlaceElem::Deref => match ty.dereference() {
                    Some(inner) => ty = inner,
                    None => return Ty::error(self.gcx),
                },
                mir::PlaceElem::Field(_, field_ty) => ty = *field_ty,
                mir::PlaceElem::VariantDowncast { name: _, index } => {
                    let def = match ty.kind() {
                        TyKind::Adt(def, _) if def.kind == AdtKind::Enum => def,
                        _ => return Ty::error(self.gcx),
                    };
                    ty = self.enum_variant_tuple_ty(def.id, *index);
                }
            }
        }
        ty
    }

    fn enum_variant_tuple_ty(
        &self,
        def_id: hir::DefinitionID,
        variant_index: thir::VariantIndex,
    ) -> Ty<'ctx> {
        let def = self.gcx.get_enum_definition(def_id);
        let variant = def
            .variants
            .get(variant_index.index())
            .expect("enum variant index");
        match variant.kind {
            EnumVariantKind::Unit => self.gcx.types.void,
            EnumVariantKind::Tuple(fields) => {
                let mut tys = Vec::with_capacity(fields.len());
                for field in fields {
                    tys.push(field.ty);
                }
                let list = self.gcx.store.interners.intern_ty_list(tys);
                Ty::new(TyKind::Tuple(list), self.gcx)
            }
        }
    }

    fn push_assign(
        &mut self,
        block: BasicBlockId,
        place: Place<'ctx>,
        value: Rvalue<'ctx>,
        span: Span,
    ) {
        self.body.basic_blocks[block].statements.push(Statement {
            kind: StatementKind::Assign(place, value),
            span,
        });
    }

    #[track_caller]
    fn terminate(&mut self, block: BasicBlockId, span: Span, kind: TerminatorKind<'ctx>) {
        debug_assert!(
            self.body.basic_blocks[block].terminator.is_none(),
            "terminate: block  already has a terminator set",
        );
        self.body.basic_blocks[block].terminator = Some(Terminator { kind, span });
    }

    #[track_caller]
    fn goto(&mut self, source: BasicBlockId, destination: BasicBlockId, span: Span) {
        self.terminate(
            source,
            span,
            TerminatorKind::Goto {
                target: destination,
            },
        );
    }

    pub fn print_mir_body(&self) {
        let pretty = PrettyPrintMir {
            body: &self.body,
            gcx: self.gcx,
        };
        println!("{}", pretty);
    }

    /// Check if a type has Fn, FnMut, or FnOnce trait bounds
    /// in the current function's constraints.
    pub fn has_fn_trait_bound(&self, ty: Ty<'ctx>) -> bool {
        self.get_fn_trait_args_type(ty).is_some()
    }

    /// Get the Args type from a Fn/FnMut/FnOnce bound on a type parameter.
    /// Returns Some(args_ty) if the type has a Fn trait bound, None otherwise.
    pub fn get_fn_trait_args_type(&self, ty: Ty<'ctx>) -> Option<Ty<'ctx>> {
        let fn_def = self.gcx.std_interface_def(StdInterface::Fn);
        let fn_mut_def = self.gcx.std_interface_def(StdInterface::FnMut);
        let fn_once_def = self.gcx.std_interface_def(StdInterface::FnOnce);

        let constraints = self.gcx.canonical_constraints_of(self.thir.id);
        for constraint in constraints {
            if let Constraint::Bound {
                ty: bound_ty,
                interface,
            } = constraint.value
            {
                if bound_ty == ty {
                    let is_fn_trait = fn_def == Some(interface.id)
                        || fn_mut_def == Some(interface.id)
                        || fn_once_def == Some(interface.id);
                    if is_fn_trait {
                        // The Args type is the first generic argument (index 1, since index 0 is Self)
                        // Interface arguments are: [Self, Args, Output]
                        if let Some(crate::sema::models::GenericArgument::Type(args_ty)) =
                            interface.arguments.get(1)
                        {
                            return Some(*args_ty);
                        }
                    }
                }
            }
        }
        None
    }

    fn record_break_edge(&mut self, block: BasicBlockId, span: Span) -> mir::BlockAnd<()> {
        let scope_index = self
            .breakable_scopes
            .iter()
            .rposition(|scope| scope.continue_target.is_some())
            .expect("break outside loop");
        self.record_edge_for_scope(scope_index, EdgeKind::Break, block, span)
    }

    fn record_continue_edge(&mut self, block: BasicBlockId, span: Span) -> mir::BlockAnd<()> {
        let scope_index = self
            .breakable_scopes
            .iter()
            .rposition(|scope| scope.continue_target.is_some())
            .expect("continue outside loop");
        self.record_edge_for_scope(scope_index, EdgeKind::Continue, block, span)
    }

    fn record_return_edge(&mut self, block: BasicBlockId, span: Span) -> mir::BlockAnd<()> {
        self.record_edge_for_scope(0, EdgeKind::Break, block, span)
    }

    fn record_edge_for_scope(
        &mut self,
        scope_index: usize,
        kind: EdgeKind,
        block: BasicBlockId,
        span: Span,
    ) -> mir::BlockAnd<()> {
        self.terminate(block, span, TerminatorKind::UnresolvedGoto);
        let cleanup = self.current_cleanup;
        let scope = self
            .breakable_scopes
            .get_mut(scope_index)
            .expect("breakable scope missing");
        let edges = match kind {
            EdgeKind::Break => &mut scope.break_edges,
            EdgeKind::Continue => &mut scope.continue_edges,
        };
        edges.push(PendingEdge {
            block,
            cleanup,
            _span: span,
        });
        let next = self.new_block_with_note("after break_scope (unreachable)".into());
        mir::BlockAnd(next, ())
    }

    fn apply_breakable_scope(&mut self, scope: BreakableScope, break_target: Option<BasicBlockId>) {
        let cleanup_at_entry = scope.cleanup_at_entry;
        if let Some(break_target) = break_target {
            self.apply_cleanup_edges(scope.break_edges, cleanup_at_entry, break_target);
        } else {
            debug_assert!(
                scope.break_edges.is_empty(),
                "missing break target for recorded break edges"
            );
        }
        if let Some(continue_target) = scope.continue_target {
            self.apply_cleanup_edges(scope.continue_edges, cleanup_at_entry, continue_target);
        }
        self.current_cleanup = cleanup_at_entry;
    }

    fn ensure_break_exit_block(&mut self, exit: BreakExit, _: Span) -> BasicBlockId {
        match exit {
            BreakExit::Return => self.new_block_with_note("return".into()),
            BreakExit::FreshBlock => self.new_block_with_note("Break Exit".into()),
            BreakExit::Target(block) => block,
        }
    }

    fn apply_cleanup_edges(
        &mut self,
        edges: Vec<PendingEdge>,
        target_cleanup: Option<CleanupId>,
        target_block: BasicBlockId,
    ) {
        if edges.is_empty() {
            return;
        }

        let mut cache: FxHashMap<Option<CleanupId>, BasicBlockId> = FxHashMap::default();
        cache.insert(target_cleanup, target_block);

        for edge in edges {
            let entry_block =
                self.ensure_cleanup_path(edge.cleanup, target_cleanup, target_block, &mut cache);
            self.patch_unresolved(edge.block, entry_block);
        }
    }

    fn ensure_cleanup_path(
        &mut self,
        from_cleanup: Option<CleanupId>,
        target_cleanup: Option<CleanupId>,
        target_block: BasicBlockId,
        cache: &mut FxHashMap<Option<CleanupId>, BasicBlockId>,
    ) -> BasicBlockId {
        if let Some(&block) = cache.get(&from_cleanup) {
            return block;
        }
        if from_cleanup == target_cleanup {
            cache.insert(from_cleanup, target_block);
            return target_block;
        }

        let Some(idx) = from_cleanup else {
            panic!("cleanup target is not an ancestor of the current cleanup stack");
        };
        debug_assert!(
            self.is_ancestor(target_cleanup, Some(idx)),
            "cleanup target must be an ancestor"
        );
        let node = self.cleanup_nodes[idx];
        let next_block = self.ensure_cleanup_path(node.parent, target_cleanup, target_block, cache);
        let block = self.new_block_with_note("cleanup".into());
        self.lower_cleanup_action(block, &node, next_block);
        cache.insert(from_cleanup, block);
        block
    }

    fn is_ancestor(&self, ancestor: Option<CleanupId>, mut node: Option<CleanupId>) -> bool {
        if ancestor == node {
            return true;
        }
        while let Some(idx) = node {
            if Some(idx) == ancestor {
                return true;
            }
            node = self.cleanup_nodes[idx].parent;
        }
        ancestor.is_none()
    }

    fn lower_cleanup_action(
        &mut self,
        start: BasicBlockId,
        node: &CleanupNode,
        next_block: BasicBlockId,
    ) {
        let saved_cleanup = self.current_cleanup;
        self.current_cleanup = node.parent;
        match node.action {
            CleanupAction::DeferBlock(block_id) => {
                let unit = self.unit_temp_place(node.span);
                let end = self.lower_block(unit, start, block_id).into_block();
                self.goto(end, next_block, node.span);
            }
        }
        self.current_cleanup = saved_cleanup;
    }

    fn patch_unresolved(&mut self, block: BasicBlockId, target: BasicBlockId) {
        let terminator = self.body.basic_blocks[block]
            .terminator
            .as_mut()
            .expect("terminator to patch");
        debug_assert!(
            matches!(terminator.kind, TerminatorKind::UnresolvedGoto),
            "expected unresolved terminator"
        );
        terminator.kind = TerminatorKind::Goto { target };
    }

    fn push_defer_action(&mut self, block: thir::BlockId, span: Span) {
        let node = CleanupNode {
            action: CleanupAction::DeferBlock(block),
            parent: self.current_cleanup,
            span,
        };
        let idx = self.cleanup_nodes.push(node);
        self.current_cleanup = Some(idx);
    }

    pub(crate) fn call_unwind_action(&mut self, span: Span) -> mir::CallUnwindAction {
        let resume_unwind = self.ensure_resume_unwind_block(span);
        let mut cache = FxHashMap::default();
        cache.insert(None, resume_unwind);
        let cleanup_entry =
            self.ensure_cleanup_path(self.current_cleanup, None, resume_unwind, &mut cache);
        mir::CallUnwindAction::Cleanup(cleanup_entry)
    }

    fn ensure_resume_unwind_block(&mut self, span: Span) -> BasicBlockId {
        if let Some(block) = self.resume_unwind_block {
            return block;
        }
        let block = self.new_block_with_note("resume_unwind".into());
        self.terminate(block, span, TerminatorKind::ResumeUnwind);
        self.resume_unwind_block = Some(block);
        block
    }

    pub(crate) fn in_if_then_scope<F>(&mut self, _: Span, f: F) -> (BasicBlockId, BasicBlockId)
    where
        F: FnOnce(&mut Self) -> BlockAnd<()>,
    {
        let scope = IfThenScope {
            cleanup_at_entry: self.current_cleanup,
            else_edges: vec![],
        };
        let previous_scope = mem::replace(&mut self.if_then_scope, Some(scope));

        let then_block = f(self).into_block();

        let scope = mem::replace(&mut self.if_then_scope, previous_scope)
            .expect("if-then scope should exist");

        let else_block = self.new_block_with_note("else block".into());
        self.apply_cleanup_edges(scope.else_edges, scope.cleanup_at_entry, else_block);
        self.current_cleanup = scope.cleanup_at_entry;
        (then_block, else_block)
    }

    pub(crate) fn break_for_else(&mut self, block: BasicBlockId, span: Span) {
        let cleanup = self.current_cleanup;
        let Some(scope) = self.if_then_scope.as_mut() else {
            panic!("no if-then scope found")
        };
        scope.else_edges.push(PendingEdge {
            block,
            cleanup,
            _span: span,
        });
        self.terminate(block, span, TerminatorKind::UnresolvedGoto);
    }

    pub fn in_breakable_scope(
        &mut self,
        loop_target: Option<BasicBlockId>,
        break_exit: BreakExit,
        span: Span,
        build_body: impl FnOnce(&mut Self) -> Option<BlockAnd<()>>,
    ) -> BlockAnd<()> {
        let cleanup_at_entry = self.current_cleanup;
        self.breakable_scopes.push(BreakableScope {
            cleanup_at_entry,
            break_exit,
            continue_target: loop_target,
            break_edges: vec![],
            continue_edges: vec![],
        });

        let normal_exit = build_body(self);
        let scope = self
            .breakable_scopes
            .pop()
            .expect("breakable scope should exist");

        let normal_exit_block = match normal_exit {
            Some(BlockAnd(block, ())) => Some(block),
            None => None,
        };

        let break_exit_block = (!scope.break_edges.is_empty())
            .then(|| self.ensure_break_exit_block(scope.break_exit, span));

        self.apply_breakable_scope(scope, break_exit_block);

        match (normal_exit_block, break_exit_block) {
            (Some(block), None) | (None, Some(block)) => BlockAnd(block, ()),
            (None, None) => self
                .new_block_with_note("after breakable scope".into())
                .unit(),
            (Some(normal_block), Some(exit_block)) => {
                debug_assert!(
                    self.body.basic_blocks[normal_block].terminator.is_none(),
                    "normal exit block should not be terminated"
                );
                debug_assert!(
                    self.body.basic_blocks[exit_block].terminator.is_none(),
                    "exit block should not be terminated"
                );
                let target = self.new_block_with_note("Breakable Join".into());
                self.goto(normal_block, target, span);
                self.goto(exit_block, target, span);
                target.unit()
            }
        }
    }
}
