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
        let mut block = self
            .lower_block_statements(mir_block, statements)
            .into_block();
        let dest_ty = self.place_ty(&destination);


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
            let cleanup_block =
                self.ensure_cleanup_path(from_cleanup, saved_cleanup, next_block, &mut cache);
            self.goto(block, cleanup_block, cleanup_span);
            block = next_block;
        }

        self.current_cleanup = saved_cleanup;
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

    fn lower_statement(&mut self, stmt: thir::StmtId, mut block: BasicBlockId) -> BlockAnd<()> {
        let stmt = &self.thir.stmts[stmt];

        match &stmt.kind {
            thir::StmtKind::Let {
                pattern,
                expr,
                ty,
                mutable,
                ..
            } => {
                // Evaluate initializer (if any) into a temp so we can destructure.
                let init_place = if let Some(init) = expr {
                    let temp = self.push_local(*ty, LocalKind::Temp, true, None, stmt.span);
                    let place = Place::from_local(temp);
                    block = self
                        .expr_into_dest(place.clone(), block, *init)
                        .into_block();
                    Some(place)
                } else {
                    None
                };

                block = self
                    .bind_pattern_to_place(block, pattern, init_place.as_ref(), *mutable)
                    .into_block();
                return block.unit();
            }
            thir::StmtKind::Break => {
                return self.record_break_edge(block, stmt.span);
            }
            thir::StmtKind::Continue => {
                return self.record_continue_edge(block, stmt.span);
            }
            thir::StmtKind::Return { value } => {
                let place = Place::from_local(self.body.return_local);
                if let Some(&value) = value.as_ref() {
                    block = self.expr_into_dest(place, block, value).into_block();
                } else {
                    self.push_assign_unit(block, stmt.span, place, self.gcx);
                }
                return self.record_return_edge(block, stmt.span);
            }
            thir::StmtKind::Loop { block: node, .. } => {
                let loop_block = self.new_block_with_note("loop block".into());
                self.goto(block, loop_block, stmt.span);

                return self.in_breakable_scope(
                    Some(loop_block),
                    super::BreakExit::FreshBlock,
                    stmt.span,
                    |this| {
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
                    },
                );
            }
            thir::StmtKind::Defer(block_id) => {
                self.push_defer_action(*block_id, stmt.span);
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
                    Some(name.clone()),
                    pattern.span,
                );
                self.locals.insert(*pat_id, local);
                if let Some(src) = place {
                    let rvalue = Rvalue::Use(Operand::Copy(src.clone()));
                    self.push_assign(block, Place::from_local(local), rvalue, pattern.span);
                }
                block.unit()
            }
            thir::PatternKind::Deref { pattern: inner } => {
                // Deref pattern: apply deref to the place and bind the inner pattern
                if let Some(base_place) = place {
                    let mut proj = base_place.projection.clone();
                    proj.push(PlaceElem::Deref);
                    let deref_place = Place {
                        local: base_place.local,
                        projection: proj,
                    };
                    self.bind_pattern_to_place(block, inner, Some(&deref_place), mutable)
                } else {
                    block.unit()
                }
            }
            thir::PatternKind::Constant { .. } => block.unit(),
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
                        name: variant.name.clone(),
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
