use crate::{
    compile::context::Gcx,
    hir::{self},
    mir::{
        self, BasicBlockData, BasicBlockId, BlockAnd, BlockAndExtension, Body, LocalDecl, LocalId,
        LocalKind, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    },
    sema::models::{ClosureKind, Constraint, LabeledFunctionSignature, Ty},
    span::{Span, Symbol},
    thir,
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;
use std::mem;

mod block;
mod cleanup;
mod expression;
pub(crate) mod variadic;

index_vec::define_index_type! {
    struct CleanupId = u32;
}
index_vec::define_index_type! {
    struct CleanupScopeId = u32;
}

#[derive(Clone, Copy, Debug)]
struct CleanupNode {
    scope: CleanupScopeId,
    action: CleanupAction,
    parent: Option<CleanupId>,
    span: Span,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct ScopedTaskCleanup<'ctx> {
    pub(super) token_local: LocalId,
    pub(super) awaited_local: LocalId,
    pub(super) value_ty: Ty<'ctx>,
}

#[derive(Clone, Copy, Debug)]
enum CleanupAction {
    DeferBlock(hir::DeferKind, thir::BlockId),
    ScopedTask(u32),
    EndStorage(LocalId),
}

/// Why a lexical cleanup chain is being traversed. Only Return may inspect
/// the initialized return slot; AsyncCancel runs synchronously on parent
/// cancellation while suspended.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CleanupExit {
    Scope,
    Return,
    Unwind,
    AsyncCancel,
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
pub struct BreakableScope<'ctx> {
    label: Option<Symbol>,
    cleanup_at_entry: Option<CleanupId>,
    break_exit: BreakExit,
    break_dest: Option<Place<'ctx>>,
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
    async_var_locals: FxHashMap<hir::NodeID, ScopedTaskCleanup<'ctx>>,
    scoped_task_cleanups: Vec<ScopedTaskCleanup<'ctx>>,
    /// Tracks MIR locals by (arm_id, binding_name) for or-patterns.
    /// Ensures all alternatives in an or-pattern share the same local.
    arm_binding_locals: FxHashMap<(thir::ArmId, Symbol), LocalId>,
    /// Already evaluated values for one call's arguments. Temporary override
    /// scopes keep source evaluation distinct from ABI parameter arrangement.
    prepared_call_arguments: FxHashMap<thir::ExprId, Place<'ctx>>,
    /// Fresh implicit receiver tokens awaiting their actual call handoff.
    /// Temporary owners extended by one local borrow/view initializer. A
    /// variadic call's callee expression keys its synthetic array owner.
    /// Aggregate owners whose currently supported drop recipe was registered.
    parameter_locals: Vec<LocalId>,
    cleanup_nodes: IndexVec<CleanupId, CleanupNode>,
    current_cleanup: Option<CleanupId>,
    current_cleanup_scope: CleanupScopeId,
    cleanup_scope_depths: IndexVec<CleanupScopeId, u32>,
    resume_unwind_block: Option<BasicBlockId>,
    /// Remaining cleanup chains all unwind to one resume block. Share their
    /// suffixes across calls and owned drops rather than rebuilding a tree.
    unwind_cleanup_paths: FxHashMap<Option<CleanupId>, BasicBlockId>,
    if_then_scope: Option<IfThenScope>,
    breakable_scopes: Vec<BreakableScope<'ctx>>,
}

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    fn fresh_cleanup_scope(&mut self) -> CleanupScopeId {
        let depth = self.cleanup_scope_depths[self.current_cleanup_scope]
            .checked_add(1)
            .expect("too many nested lexical cleanup scopes");
        self.cleanup_scope_depths.push(depth)
    }

    pub fn build_function(gcx: Gcx<'ctx>, function: &'thir thir::ThirFunction<'ctx>) -> Body<'ctx> {
        let signature = gcx.get_signature(function.id);
        let generator_element_ty = gcx.generator_element_ty(function.id);
        let output_ty = if generator_element_ty.is_some() {
            gcx.types.void
        } else {
            gcx.function_body_output(function.id)
        };
        let entry_span = function.span;

        let mut body = Body {
            escape_locals: Vec::new(),

            owner: function.id,
            source_scopes: Body::initial_source_scopes(function.id),
            locals: Default::default(),
            basic_blocks: Default::default(),
            start_block: BasicBlockId::from_raw(0),
            return_local: LocalId::from_raw(0),
            phase: mir::MirPhase::Built,
            is_async: function.is_async,
            generator_element_ty,
        };

        // A fallible constructor keeps partial self separate from its Result.
        let constructor_return =
            function.constructor_self.is_some() && gcx.result_parts(output_ty).is_none();
        // Create return place first.
        let ret_local = body.locals.push(LocalDecl {
            ty: output_ty,
            kind: if constructor_return {
                LocalKind::ConstructorSelf
            } else {
                LocalKind::Return
            },
            mutable: true,
            name: Some(gcx.intern_symbol(if constructor_return { "self" } else { "$ret" })),
            span: entry_span,
        });
        body.return_local = ret_local;

        let mut builder = MirBuilder {
            gcx,
            thir: function,
            body,
            locals: FxHashMap::default(),
            async_var_locals: FxHashMap::default(),
            scoped_task_cleanups: Vec::new(),
            arm_binding_locals: FxHashMap::default(),
            prepared_call_arguments: FxHashMap::default(),
            parameter_locals: Vec::new(),
            cleanup_nodes: IndexVec::new(),
            current_cleanup: None,
            current_cleanup_scope: CleanupScopeId::from_raw(0),
            cleanup_scope_depths: IndexVec::from(vec![0]),
            resume_unwind_block: None,
            unwind_cleanup_paths: FxHashMap::default(),
            if_then_scope: None,
            breakable_scopes: vec![],
        };

        builder.declare_parameters(signature);
        builder.lower_body();
        builder.finish()
    }

    pub fn build_const_initializer(
        gcx: Gcx<'ctx>,
        function: &'thir thir::ThirFunction<'ctx>,
        output_ty: Ty<'ctx>,
    ) -> Body<'ctx> {
        let entry_span = function.span;
        let mut body = Body {
            escape_locals: Vec::new(),
            owner: function.id,
            source_scopes: Body::initial_source_scopes(function.id),
            locals: Default::default(),
            basic_blocks: Default::default(),
            start_block: BasicBlockId::from_raw(0),
            return_local: LocalId::from_raw(0),
            phase: mir::MirPhase::Built,
            is_async: false,
            generator_element_ty: None,
        };
        let ret_local = body.locals.push(LocalDecl {
            ty: output_ty,
            kind: LocalKind::Return,
            mutable: true,
            name: Some(gcx.intern_symbol("$const_ret")),
            span: entry_span,
        });
        body.return_local = ret_local;

        let mut builder = MirBuilder {
            gcx,
            thir: function,
            body,
            locals: FxHashMap::default(),
            async_var_locals: FxHashMap::default(),
            scoped_task_cleanups: Vec::new(),
            arm_binding_locals: FxHashMap::default(),
            prepared_call_arguments: FxHashMap::default(),
            parameter_locals: Vec::new(),
            cleanup_nodes: IndexVec::new(),
            current_cleanup: None,
            current_cleanup_scope: CleanupScopeId::from_raw(0),
            cleanup_scope_depths: IndexVec::from(vec![0]),
            resume_unwind_block: None,
            unwind_cleanup_paths: FxHashMap::default(),
            if_then_scope: None,
            breakable_scopes: vec![],
        };
        builder.lower_body();
        builder.finish()
    }

    fn finish(mut self) -> Body<'ctx> {
        mir::analysis::constructor::complete(self.gcx, &mut self.body);
        self.body
    }

    fn declare_parameters(&mut self, signature: &LabeledFunctionSignature<'ctx>) {
        let params: Vec<_> = self
            .thir
            .params
            .iter()
            .zip(signature.inputs.iter())
            .map(|(param, lowered)| (param.id, param.name, param.span, lowered.ty))
            .collect();
        for (id, name, span, ty) in params {
            let local = self.push_local(
                ty,
                LocalKind::Param,
                self.gcx.symbol_eq(name, "self"),
                Some(name),
                span,
            );
            self.locals.insert(id, local);
            self.parameter_locals.push(local);
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

        let parameters = self.parameter_locals.clone();
        let return_block = self
            .in_breakable_scope(None, BreakExit::Return, span, |this| {
                for local in parameters {
                    this.register_storage_cleanup(local, span);
                }
                // Constructor bodies evaluate to unit; self already denotes
                // the result storage and must remain available to defer.
                let destination = if this.thir.constructor_self.is_some()
                    && this
                        .gcx
                        .result_parts(this.body.locals[this.body.return_local].ty)
                        .is_none()
                {
                    Place::from_local(this.push_local(
                        this.gcx.types.void,
                        LocalKind::Temp,
                        true,
                        None,
                        span,
                    ))
                } else {
                    Place::return_place()
                };
                let normal_exit = this
                    .lower_block(destination, start_block, thir_block)
                    .into_block();
                let _ = this.record_return_edge(normal_exit, span);
                None
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

    fn push_storage_live(&mut self, block: BasicBlockId, local: LocalId, span: Span) {
        self.body.basic_blocks[block].statements.push(Statement {
            kind: StatementKind::StorageLive(local),
            span,
        });
    }

    /// Keep semantic storage endings even for values with trivial destruction.
    fn register_storage_cleanup(&mut self, local: LocalId, span: Span) {
        let node = CleanupNode {
            scope: self.current_cleanup_scope,
            action: CleanupAction::EndStorage(local),
            parent: self.current_cleanup,
            span,
        };
        self.current_cleanup = Some(self.cleanup_nodes.push(node));
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

    fn get_callable_trait_info(
        &self,
        ty: Ty<'ctx>,
    ) -> Option<(ClosureKind, crate::sema::models::InterfaceReference<'ctx>)> {
        // Generated closure bodies inherit bounds, but publishing those bounds
        // invalidates the canonical cache. Compute it on demand: a cache miss
        // must not turn an Fn/FnMut receiver into a consuming call.
        let constraints =
            crate::sema::tycheck::constraints::canonical_constraints_of(self.gcx, self.thir.id);
        let mut best: Option<(ClosureKind, crate::sema::models::InterfaceReference<'ctx>)> = None;

        for constraint in constraints {
            let Constraint::Bound {
                ty: bound_ty,
                interface,
            } = constraint.value
            else {
                continue;
            };

            if bound_ty != ty {
                continue;
            }

            let Some(kind) = crate::sema::models::callable_kind(self.gcx, interface.id) else {
                continue;
            };

            // Interface arguments are [Self, Args, Output].
            match best {
                Some((best_kind, _)) if best_kind as usize <= kind as usize => {}
                _ => best = Some((kind, interface)),
            }
        }

        best
    }

    pub fn get_callable_trait_ref(
        &self,
        ty: Ty<'ctx>,
    ) -> Option<crate::sema::models::InterfaceReference<'ctx>> {
        self.get_callable_trait_info(ty)
            .map(|(_, interface)| interface)
    }

    /// Get the Args type from a callable bound on a type parameter.
    /// Returns Some(args_ty) if the type has a Fn trait bound, None otherwise.
    pub fn get_fn_trait_args_type(&self, ty: Ty<'ctx>) -> Option<Ty<'ctx>> {
        let interface = self.get_callable_trait_ref(ty)?;
        match interface.arguments.get(1) {
            Some(crate::sema::models::GenericArgument::Type(args_ty)) => Some(*args_ty),
            _ => None,
        }
    }

    pub fn get_callable_trait_method_id(&self, ty: Ty<'ctx>) -> Option<hir::DefinitionID> {
        let (_, interface) = self.get_callable_trait_info(ty)?;
        let requirements = self.gcx.get_interface_requirements(interface.id)?;
        let method_name = "call";
        requirements
            .methods
            .iter()
            .find(|method| self.gcx.symbol_eq(method.name, method_name))
            .map(|method| method.id)
    }

    fn find_loop_scope_index(&self, label: Option<Symbol>) -> Option<usize> {
        if let Some(label) = label {
            self.breakable_scopes
                .iter()
                .rposition(|scope| scope.continue_target.is_some() && scope.label == Some(label))
        } else {
            self.breakable_scopes
                .iter()
                .rposition(|scope| scope.continue_target.is_some())
        }
    }

    fn record_break_edge(
        &mut self,
        label: Option<Symbol>,
        value: Option<thir::ExprId>,
        mut block: BasicBlockId,
        span: Span,
    ) -> mir::BlockAnd<()> {
        let scope_index = self
            .find_loop_scope_index(label)
            .expect("break outside matching loop");
        let break_dest = self.breakable_scopes[scope_index].break_dest.clone();
        if let Some(value) = value {
            let dest = break_dest.unwrap_or_else(|| self.unit_temp_place(span));
            block = self.expr_into_dest(dest, block, value).into_block();
        } else if let Some(dest) = break_dest {
            self.push_assign_unit(block, span, dest, self.gcx);
        }
        self.record_edge_for_scope(scope_index, EdgeKind::Break, block, span)
    }

    fn record_continue_edge(
        &mut self,
        label: Option<Symbol>,
        block: BasicBlockId,
        span: Span,
    ) -> mir::BlockAnd<()> {
        let scope_index = self
            .find_loop_scope_index(label)
            .expect("continue outside matching loop");
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

    fn apply_breakable_scope(
        &mut self,
        scope: BreakableScope<'ctx>,
        break_target: Option<BasicBlockId>,
    ) {
        let cleanup_at_entry = scope.cleanup_at_entry;
        if let Some(break_target) = break_target {
            let exit = if matches!(scope.break_exit, BreakExit::Return) {
                CleanupExit::Return
            } else {
                CleanupExit::Scope
            };
            self.apply_cleanup_edges(scope.break_edges, cleanup_at_entry, break_target, exit);
        } else {
            debug_assert!(
                scope.break_edges.is_empty(),
                "missing break target for recorded break edges"
            );
        }
        if let Some(continue_target) = scope.continue_target {
            self.apply_cleanup_edges(
                scope.continue_edges,
                cleanup_at_entry,
                continue_target,
                CleanupExit::Scope,
            );
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
        exit: CleanupExit,
    ) {
        if edges.is_empty() {
            return;
        }

        let mut cache: FxHashMap<Option<CleanupId>, BasicBlockId> = FxHashMap::default();
        cache.insert(target_cleanup, target_block);

        for edge in edges {
            let entry_block = self.cleanup_path_for_exit(
                edge.cleanup,
                target_cleanup,
                target_block,
                &mut cache,
                exit,
            );
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
        self.cleanup_path_for_exit(
            from_cleanup,
            target_cleanup,
            target_block,
            cache,
            CleanupExit::Scope,
        )
    }

    fn cleanup_path_for_exit(
        &mut self,
        from_cleanup: Option<CleanupId>,
        target_cleanup: Option<CleanupId>,
        target_block: BasicBlockId,
        cache: &mut FxHashMap<Option<CleanupId>, BasicBlockId>,
        exit: CleanupExit,
    ) -> BasicBlockId {
        let unwinding = exit == CleanupExit::Unwind;
        if unwinding && let Some(&block) = self.unwind_cleanup_paths.get(&from_cleanup) {
            return block;
        }
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
        let ordered = cleanup::reorder_chain(
            &mut self.cleanup_nodes,
            &self.cleanup_scope_depths,
            from_cleanup,
            target_cleanup,
        );
        let block = self.emit_cleanup_path(ordered, target_cleanup, target_block, cache, exit);
        cache.insert(from_cleanup, block);
        if unwinding {
            self.unwind_cleanup_paths.insert(from_cleanup, block);
        }
        block
    }

    /// The chain is already in execution order. Its parents are exactly the
    /// actions that remain if the current action panics.
    fn emit_cleanup_path(
        &mut self,
        from_cleanup: Option<CleanupId>,
        target_cleanup: Option<CleanupId>,
        target_block: BasicBlockId,
        cache: &mut FxHashMap<Option<CleanupId>, BasicBlockId>,
        exit: CleanupExit,
    ) -> BasicBlockId {
        let unwinding = exit == CleanupExit::Unwind;
        if unwinding && let Some(&block) = self.unwind_cleanup_paths.get(&from_cleanup) {
            return block;
        }
        if let Some(&block) = cache.get(&from_cleanup) {
            return block;
        }
        if from_cleanup == target_cleanup {
            return target_block;
        }
        let idx = from_cleanup.expect("ordered cleanup must reach its target");
        let node = self.cleanup_nodes[idx];
        let next_block =
            self.emit_cleanup_path(node.parent, target_cleanup, target_block, cache, exit);
        let block = if matches!(
            node.action,
            CleanupAction::DeferBlock(hir::DeferKind::OnFailure, _)
        ) && !unwinding
        {
            if exit == CleanupExit::Return
                && self
                    .gcx
                    .result_parts(self.body.locals[self.body.return_local].ty)
                    .is_some()
            {
                self.error_return_cleanup(&node, next_block)
            } else {
                next_block
            }
        } else {
            self.cleanup_action_block(&node, next_block, exit)
        };
        cache.insert(from_cleanup, block);
        if unwinding {
            self.unwind_cleanup_paths.insert(from_cleanup, block);
        }
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

    /// Inspect only the tag. Ownership of either payload stays in the return slot.
    fn error_return_cleanup(&mut self, node: &CleanupNode, next: BasicBlockId) -> BasicBlockId {
        let result = self.gcx.std_item_def(hir::StdItem::Result).expect("Result");
        let err = self
            .gcx
            .std_item_def(hir::StdItem::ResultErrVariant)
            .expect("Result.err");
        let index = self
            .gcx
            .get_enum_definition(result)
            .variants
            .iter()
            .position(|variant| variant.def_id == err)
            .expect("Result.err index");
        let entry = self.new_block_with_note("check error return".into());
        let BlockAnd(block, discr) =
            self.enum_discriminant_operand(entry, &Place::return_place(), node.span);
        let action = self.cleanup_action_block(node, next, CleanupExit::Return);
        self.terminate(
            block,
            node.span,
            TerminatorKind::SwitchInt {
                discr,
                targets: vec![(index as u128, action)],
                otherwise: next,
            },
        );
        entry
    }

    fn cleanup_action_block(
        &mut self,
        node: &CleanupNode,
        next_block: BasicBlockId,
        exit: CleanupExit,
    ) -> BasicBlockId {
        let start = self.new_block_with_note("cleanup".into());
        let saved_cleanup = self.current_cleanup;
        let saved_scope = self.current_cleanup_scope;
        self.current_cleanup = node.parent;
        self.current_cleanup_scope = node.scope;
        match node.action {
            CleanupAction::EndStorage(local) => {
                self.body.basic_blocks[start].statements.push(Statement {
                    kind: StatementKind::StorageDead(local),
                    span: node.span,
                });
                self.goto(start, next_block, node.span);
            }
            CleanupAction::DeferBlock(_, block_id) => {
                let unit = self.unit_temp_place(node.span);
                let end = self.lower_block(unit, start, block_id).into_block();
                self.goto(end, next_block, node.span);
            }
            CleanupAction::ScopedTask(idx) => {
                let info = self.scoped_task_cleanups[idx as usize];
                let drain = matches!(exit, CleanupExit::Scope | CleanupExit::Return);
                self.lower_scoped_task_cleanup(start, info, drain, next_block, node.span);
            }
        }
        self.current_cleanup = saved_cleanup;
        self.current_cleanup_scope = saved_scope;
        start
    }

    fn push_scoped_task_action(&mut self, info: ScopedTaskCleanup<'ctx>, span: Span) {
        let idx = self.scoped_task_cleanups.len() as u32;
        self.scoped_task_cleanups.push(info);
        let node = CleanupNode {
            scope: self.current_cleanup_scope,
            action: CleanupAction::ScopedTask(idx),
            parent: self.current_cleanup,
            span,
        };
        let cleanup_id = self.cleanup_nodes.push(node);
        self.current_cleanup = Some(cleanup_id);
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

    fn push_defer_action(&mut self, kind: hir::DeferKind, block: thir::BlockId, span: Span) {
        let node = CleanupNode {
            scope: self.current_cleanup_scope,
            action: CleanupAction::DeferBlock(kind, block),
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
        let cleanup_entry = self.cleanup_path_for_exit(
            self.current_cleanup,
            None,
            resume_unwind,
            &mut cache,
            CleanupExit::Unwind,
        );
        mir::CallUnwindAction::Cleanup(cleanup_entry)
    }

    /// Build the ordinary control-flow cleanup path used when an async frame
    /// is cancelled while suspended. Unlike `call_unwind_action`, this path
    /// ends at a marker block rather than `ResumeUnwind`: cancellation is not
    /// itself a panic, so defer bodies run normally and may independently
    /// panic through their existing unwind edges.
    pub(crate) fn async_cancel_cleanup_target(
        &mut self,
        span: Span,
    ) -> (BasicBlockId, BasicBlockId) {
        let cancelled = self.new_block_with_note("async-cancelled".into());
        self.terminate(cancelled, span, TerminatorKind::Unreachable);

        let mut cache = FxHashMap::default();
        cache.insert(None, cancelled);
        let entry = self.cleanup_path_for_exit(
            self.current_cleanup,
            None,
            cancelled,
            &mut cache,
            CleanupExit::AsyncCancel,
        );
        (entry, cancelled)
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

    pub(crate) fn in_if_then_scope<F>(&mut self, span: Span, f: F) -> (BasicBlockId, BasicBlockId)
    where
        F: FnOnce(&mut Self) -> BlockAnd<()>,
    {
        let scope = IfThenScope {
            cleanup_at_entry: self.current_cleanup,
            else_edges: vec![],
        };
        let previous_scope = mem::replace(&mut self.if_then_scope, Some(scope));

        let mut then_block = f(self).into_block();
        // A condition can establish owned pattern bindings and temporary
        // scrutinee storage. They belong to this branch, not to a lost cleanup
        // chain after we restore the enclosing scope.
        let entry = self.if_then_scope.as_ref().unwrap().cleanup_at_entry;
        if self.current_cleanup != entry && self.body.basic_blocks[then_block].terminator.is_none()
        {
            let completed = self.new_block_with_note("if condition owners finished".into());
            let mut cache = FxHashMap::default();
            cache.insert(entry, completed);
            let cleanup =
                self.ensure_cleanup_path(self.current_cleanup, entry, completed, &mut cache);
            self.goto(then_block, cleanup, span);
            then_block = completed;
        }

        let scope = mem::replace(&mut self.if_then_scope, previous_scope)
            .expect("if-then scope should exist");

        let else_block = self.new_block_with_note("else block".into());
        self.apply_cleanup_edges(
            scope.else_edges,
            scope.cleanup_at_entry,
            else_block,
            CleanupExit::Scope,
        );
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
        self.in_breakable_scope_with(None, loop_target, break_exit, None, span, build_body)
    }

    pub fn in_loop_scope(
        &mut self,
        label: Option<Symbol>,
        loop_target: BasicBlockId,
        break_dest: Option<Place<'ctx>>,
        span: Span,
        build_body: impl FnOnce(&mut Self) -> Option<BlockAnd<()>>,
    ) -> BlockAnd<()> {
        self.in_breakable_scope_with(
            label,
            Some(loop_target),
            BreakExit::FreshBlock,
            break_dest,
            span,
            build_body,
        )
    }

    fn in_breakable_scope_with(
        &mut self,
        label: Option<Symbol>,
        loop_target: Option<BasicBlockId>,
        break_exit: BreakExit,
        break_dest: Option<Place<'ctx>>,
        span: Span,
        build_body: impl FnOnce(&mut Self) -> Option<BlockAnd<()>>,
    ) -> BlockAnd<()> {
        let cleanup_at_entry = self.current_cleanup;
        self.breakable_scopes.push(BreakableScope {
            label,
            cleanup_at_entry,
            break_exit,
            break_dest,
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
