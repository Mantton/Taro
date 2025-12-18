use crate::{
    mir::{
        self, BasicBlockId, BlockAnd, BlockAndExtension, Place, TerminatorKind, builder::MirBuilder,
    },
    span::Span,
    thir::{self},
};

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

        // TODO: Do we wanna break out early?
        // if self.body.basic_blocks[block].terminator.is_some() {
        //     self.current_cleanup = saved_cleanup;
        //     return block.unit();
        // }

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
                id,
                pattern,
                expr,
                ty,
            } => match &pattern.kind {
                thir::PatternKind::Binding {
                    local: pat_id,
                    name,
                    ty,
                    mutable: _,
                } => {
                    let local =
                        self.push_local(*ty, mir::LocalKind::User, Some(*name), pattern.span);
                    self.locals.insert(*pat_id, local);
                    if let Some(initializer) = expr.as_ref() {
                        block = self
                            .expr_into_dest(Place::from_local(local), block, *initializer)
                            .into_block();
                        return block.unit();
                    }
                }
                _ => {
                    unimplemented!()
                }
            },
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
