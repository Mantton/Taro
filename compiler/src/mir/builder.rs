use crate::{
    compile::context::Gcx,
    hir,
    mir::{
        self, BasicBlockData, BasicBlockId, BlockAnd, BlockAndExtension, Body, LocalDecl, LocalId,
        LocalKind, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
        pretty::PrettyPrintMir,
    },
    sema::models::{LabeledFunctionSignature, Ty},
    span::{Span, Symbol},
    thir,
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

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
    span: Span,
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
    cleanup_nodes: IndexVec<CleanupId, CleanupNode>,
    current_cleanup: Option<CleanupId>,
    breakable_scopes: Vec<BreakableScope>,
}

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn build_function(gcx: Gcx<'ctx>, function: &'thir thir::ThirFunction<'ctx>) -> Body<'ctx> {
        gcx.dcx()
            .emit_info("Building MIR".into(), Some(function.span));
        let signature = gcx.get_signature(function.id);
        let output_ty = signature.output;
        let entry_span = function.span;

        let mut body = Body {
            locals: Default::default(),
            basic_blocks: Default::default(),
            start_block: BasicBlockId::from_raw(0),
            return_local: LocalId::from_raw(0),
        };

        // Create return place first.
        let ret_local = body.locals.push(LocalDecl {
            ty: output_ty,
            kind: LocalKind::Return,
            name: Some(Symbol::new("$ret")),
            span: entry_span,
        });
        body.return_local = ret_local;

        let mut builder = MirBuilder {
            gcx,
            thir: function,
            body,
            locals: FxHashMap::default(),
            cleanup_nodes: IndexVec::new(),
            current_cleanup: None,
            breakable_scopes: vec![],
        };

        builder.declare_parameters(signature);
        builder.lower_body();
        builder.finish()
    }

    fn finish(self) -> Body<'ctx> {
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
            let local = self.push_local(ty, LocalKind::Param, Some(name), span);
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
            self.print_mir_body();
            return;
        };

        let _ = self.in_breakable_scope(None, BreakExit::Return, span, |this| {
            let return_place = Place::from_local(this.body.return_local);
            let destination = return_place;
            let fin = this
                .lower_block(destination, start_block, thir_block)
                .into_block();
            if this.body.basic_blocks[fin].terminator.is_none() {
                let _ = this.record_return_edge(fin, span);
            }
            None
        });
        self.finalize_unterminated_blocks();
        self.print_mir_body();
    }

    fn push_local(
        &mut self,
        ty: Ty<'ctx>,
        kind: LocalKind,
        name: Option<Symbol>,
        span: Span,
    ) -> LocalId {
        self.body.locals.push(LocalDecl {
            ty,
            kind,
            name,
            span,
        })
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
        let local = self.push_local(self.gcx.types.void, LocalKind::Temp, None, span);
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
            }
        }
        ty
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
        let pretty = PrettyPrintMir { body: &self.body };
        println!("{}", pretty);
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
            span,
        });
        mir::BlockAnd(block, ())
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

    fn ensure_break_exit_block(&mut self, exit: BreakExit, span: Span) -> BasicBlockId {
        match exit {
            BreakExit::Return => {
                let block = self.new_block_with_note("return".into());
                self.terminate(block, span, TerminatorKind::Return);
                block
            }
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
