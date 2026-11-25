use crate::{
    mir::{
        self, BasicBlockId, BlockAnd, BlockAndExtension, LocalKind, Operand, Place, PlaceElem,
        Rvalue, TerminatorKind, builder::MirBuilder,
    },
    span::Span,
    thir::{self, VariantIndex},
};
use rustc_hash::FxHashMap;

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub(super) fn lower_block(
        &mut self,
        destination: Place<'ctx>,
        mir_block: mir::BasicBlockId,
        thir_block: thir::BlockId,
    ) -> BlockAnd<()> {
        let statements = &self.thir.blocks[thir_block].stmts;
        let saved_cleanup = self.current_cleanup;
        let saved_scope = self.current_cleanup_scope;
        self.current_cleanup_scope = self.fresh_cleanup_scope();
        let mut block = self
            .lower_block_statements(mir_block, statements)
            .into_block();
        // A closure body or a branch can also write the function's return value
        // directly. Blocks evaluated into a binding or temporary exit normally.
        let exit = if destination == Place::return_place() {
            super::CleanupExit::Return
        } else {
            super::CleanupExit::Scope
        };
        let dest_ty = self.body.place_ty(self.gcx, &destination);

        if let Some(expr) = self.thir.blocks[thir_block].expr {
            block = if dest_ty == self.gcx.types.void {
                self.lower_statement_expression(block, expr).into_block()
            } else {
                self.expr_into_dest(destination, block, expr).into_block()
            };
        } else if dest_ty == self.gcx.types.void {
            let span = Span::empty(self.thir.span.file);
            self.push_assign_unit(block, span, destination, self.gcx);
        }

        let cleanup_span = Span::empty(self.thir.span.file);
        let from_cleanup = self.current_cleanup;
        if from_cleanup != saved_cleanup && self.body.basic_blocks[block].terminator.is_none() {
            let next_block = self.new_block_with_note("after cleanup".into());
            let mut cache = FxHashMap::default();
            cache.insert(saved_cleanup, next_block);
            let cleanup_block = self.cleanup_path_for_exit(
                from_cleanup,
                saved_cleanup,
                next_block,
                &mut cache,
                exit,
            );
            self.goto(block, cleanup_block, cleanup_span);
            block = next_block;
        }

        self.current_cleanup = saved_cleanup;
        self.current_cleanup_scope = saved_scope;
        block.unit()
    }

    fn lower_block_statements(
        &mut self,
        mut block: BasicBlockId,
        statements: &[thir::StmtId],
    ) -> BlockAnd<()> {
        for &stmt in statements {
            block = self.lower_statement(stmt, block).into_block();
        }
        block.unit()
    }

    fn lower_statement(&mut self, stmt: thir::StmtId, block: BasicBlockId) -> BlockAnd<()> {
        let entry = self.current_cleanup;
        let parent_scope = self.current_cleanup_scope;
        let scope = self.fresh_cleanup_scope();
        self.current_cleanup_scope = scope;
        let mut block = self
            .lower_statement_inner(stmt, block, parent_scope)
            .into_block();
        let (exiting, retained) = super::cleanup::split_scope(
            &mut self.cleanup_nodes,
            &self.cleanup_scope_depths,
            self.current_cleanup,
            entry,
            scope,
        );
        if exiting != retained && self.body.basic_blocks[block].terminator.is_none() {
            let next = self.new_block_with_note("after statement temporaries".into());
            let mut cache = FxHashMap::default();
            cache.insert(retained, next);
            let cleanup = self.ensure_cleanup_path(exiting, retained, next, &mut cache);
            self.goto(block, cleanup, self.thir.stmts[stmt].span);
            block = next;
        }
        self.current_cleanup = retained;
        self.current_cleanup_scope = parent_scope;
        block.unit()
    }

    fn lower_statement_inner(
        &mut self,
        stmt: thir::StmtId,
        mut block: BasicBlockId,
        binding_scope: super::CleanupScopeId,
    ) -> BlockAnd<()> {
        let stmt = &self.thir.stmts[stmt];

        match &stmt.kind {
            thir::StmtKind::Let {
                pattern,
                expr,
                ty,
                mutable,
                ..
            } => {
                if let thir::PatternKind::Binding {
                    local: pat_id,
                    name,
                    ty: binding_ty,
                    ..
                } = &pattern.kind
                {
                    if self.thir.constructor_self == Some(*pat_id) {
                        let local = if self
                            .gcx
                            .result_parts(self.body.locals[self.body.return_local].ty)
                            .is_some()
                        {
                            self.push_local(
                                *binding_ty,
                                LocalKind::ConstructorSelf,
                                true,
                                Some(*name),
                                pattern.span,
                            )
                        } else {
                            self.body.return_local
                        };
                        self.locals.insert(*pat_id, local);
                        self.push_storage_live(block, local, pattern.span);
                        return block.unit();
                    }
                    // A whole binding can own its initializer storage directly.
                    // Publish its source name only after initialization, so a
                    // shadowing initializer still resolves the previous binding.
                    let local = self.push_local(
                        *binding_ty,
                        LocalKind::User,
                        *mutable,
                        Some(*name),
                        pattern.span,
                    );
                    self.push_storage_live(block, local, pattern.span);
                    let temporary_scope = self.current_cleanup_scope;
                    self.current_cleanup_scope = binding_scope;
                    self.register_storage_cleanup(local, pattern.span);

                    self.current_cleanup_scope = temporary_scope;
                    if let Some(init) = expr {
                        block = self
                            .expr_into_dest(Place::from_local(local), block, *init)
                            .into_block();
                    }
                    self.locals.insert(*pat_id, local);
                    return block.unit();
                }
                // Destructuring needs an independent, conditionally owned temp.
                let init_place = if let Some(init) = expr {
                    let temp = self.push_local(*ty, LocalKind::Temp, true, None, stmt.span);
                    let place = Place::from_local(temp);
                    self.push_storage_live(block, temp, stmt.span);
                    self.register_storage_cleanup(temp, stmt.span);
                    // The initializer owns storage independently of its bindings.
                    // Copy bindings duplicate it; partial construction can unwind.

                    block = self
                        .expr_into_dest(place.clone(), block, *init)
                        .into_block();
                    Some(place)
                } else {
                    None
                };

                let temporary_scope = self.current_cleanup_scope;
                self.current_cleanup_scope = binding_scope;
                block = self
                    .bind_pattern_to_place(block, pattern, init_place.as_ref(), *mutable)
                    .into_block();
                self.current_cleanup_scope = temporary_scope;
                return block.unit();
            }
            thir::StmtKind::AsyncLet {
                local: pat_id,
                name,
                ty,
                closure,
            } => {
                let temporary_scope = self.current_cleanup_scope;
                self.current_cleanup_scope = binding_scope;
                block = self
                    .lower_async_let(block, *pat_id, *name, *ty, *closure, stmt.span)
                    .into_block();
                self.current_cleanup_scope = temporary_scope;
            }
            thir::StmtKind::Break { label, value } => {
                return self.record_break_edge(*label, *value, block, stmt.span);
            }
            thir::StmtKind::Continue { label } => {
                return self.record_continue_edge(*label, block, stmt.span);
            }
            thir::StmtKind::Return { value } => {
                let place = Place::from_local(self.body.return_local);
                if let Some(&value) = value.as_ref() {
                    block = self.expr_into_dest(place, block, value).into_block();
                } else if self.thir.constructor_self.is_none() {
                    self.push_assign_unit(block, stmt.span, place, self.gcx);
                }
                return self.record_return_edge(block, stmt.span);
            }
            thir::StmtKind::Loop { label, block: node } => {
                let loop_block = self.new_block_with_note("loop block".into());
                self.goto(block, loop_block, stmt.span);

                return self.in_loop_scope(*label, loop_block, None, stmt.span, |this| {
                    let body_block = this.new_block_with_note("loop body block".into());
                    this.terminate(
                        loop_block,
                        stmt.span,
                        TerminatorKind::Goto { target: body_block },
                    );

                    let unit = this.unit_temp_place(stmt.span);
                    let block = this.lower_block(unit, body_block, *node).into_block();
                    this.goto(block, loop_block, stmt.span);
                    None
                });
            }
            thir::StmtKind::Guard {
                condition,
                else_block,
            } => {
                let success = self.new_block_with_note("guard success".into());
                let failure = self.new_block_with_note("guard failure".into());
                let temporary_scope = self.current_cleanup_scope;
                // Successful guard bindings persist after this statement.
                // Keep their backing scrutinee alongside them for borrowed
                // payloads; failed paths clean only initialized obligations.
                self.current_cleanup_scope = binding_scope;
                self.lower_condition(block, *condition, success, failure);
                let destination = self.unit_temp_place(stmt.span);
                let failed = self
                    .lower_block(destination, failure, *else_block)
                    .into_block();
                if self.body.basic_blocks[failed].terminator.is_none() {
                    self.terminate(failed, stmt.span, TerminatorKind::Unreachable);
                }
                self.current_cleanup_scope = temporary_scope;
                return success.unit();
            }
            thir::StmtKind::Defer(kind, block_id) => {
                let temporary_scope = self.current_cleanup_scope;
                self.current_cleanup_scope = binding_scope;
                self.push_defer_action(*kind, *block_id, stmt.span);
                self.current_cleanup_scope = temporary_scope;
            }
            thir::StmtKind::Expr(expr) => {
                block = self.lower_statement_expression(block, *expr).into_block();
            }
        }

        block.unit()
    }
}

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub(super) fn bind_pattern_to_place(
        &mut self,
        mut block: BasicBlockId,
        pattern: &thir::Pattern<'ctx>,
        place: Option<&Place<'ctx>>,
        mutable: bool,
    ) -> BlockAnd<()> {
        match &pattern.kind {
            thir::PatternKind::At { binding, pattern } => {
                block = self.bind_pattern_to_place(block, binding, place, mutable).into_block();
                self.bind_pattern_to_place(block, pattern, place, mutable)
            }
            thir::PatternKind::Wild => block.unit(),
            thir::PatternKind::Binding {
                local: pat_id,
                name,
                ty,
                ..
            } => {
                let local = self.push_local(
                    *ty,
                    mir::LocalKind::User,
                    mutable,
                    Some(*name),
                    pattern.span,
                );
                self.locals.insert(*pat_id, local);
                self.push_storage_live(block, local, pattern.span);
                self.register_storage_cleanup(local, pattern.span);

                if let Some(src) = place {
                    let operand = Operand::Copy(src.clone());
                    let rvalue = Rvalue::Use(operand);
                    self.push_assign(block, Place::from_local(local), rvalue, pattern.span);
                }
                block.unit()
            }
            thir::PatternKind::TypeTest { .. }
            | thir::PatternKind::Constant { .. } | thir::PatternKind::Range(_) => block.unit(),
            thir::PatternKind::Leaf { subpatterns } => {
                let Some(base_place) = place else {
                    return block.unit();
                };
                for field in subpatterns {
                    let mut proj = base_place.projection.clone();
                    proj.push(PlaceElem::Field(field.index, field.pattern.ty));
                    let field_place = Place {
                        local: base_place.local,
                        projection: proj,
                    };
                    block = self
                        .bind_pattern_to_place(block, &field.pattern, Some(&field_place), mutable)
                        .into_block();
                }
                block.unit()
            }
            thir::PatternKind::Variant {
                definition,
                variant,
                subpatterns,
            } => {
                let Some(base_place) = place else {
                    return block.unit();
                };
                let enum_def = self.gcx.get_enum_definition(definition.id);
                let variant_index = enum_def
                    .variants
                    .iter()
                    .position(|item| item.def_id == variant.def_id)
                    .map(VariantIndex::from_usize)
                    .expect("variant in enum definition");
                for field in subpatterns {
                    let mut proj = base_place.projection.clone();
                    proj.push(PlaceElem::VariantDowncast {
                        name: variant.name,
                        index: variant_index,
                    });
                    proj.push(PlaceElem::Field(field.index, field.pattern.ty));
                    let field_place = Place {
                        local: base_place.local,
                        projection: proj,
                    };
                    block = self
                        .bind_pattern_to_place(block, &field.pattern, Some(&field_place), mutable)
                        .into_block();
                }
                block.unit()
            }
            thir::PatternKind::Or(patterns) => {
                let Some(first) = patterns.first() else {
                    return block.unit();
                };
                // Resolver enforces consistent bindings across or-patterns.
                self.bind_pattern_to_place(block, first, place, mutable)
            }
        }
    }
}
