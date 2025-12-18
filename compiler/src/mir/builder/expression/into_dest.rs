use crate::{
    compile::context::Gcx,
    mir::{
        self, BasicBlockId, BlockAnd, BlockAndExtension, Category, Constant, Operand, Place,
        Rvalue, RvalueFunc, TerminatorKind, builder::MirBuilder,
    },
    span::Span,
    thir::{ExprId, ExprKind},
    unpack,
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn expr_into_dest(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        expr_id: ExprId,
    ) -> BlockAnd<()> {
        let expr = &self.thir.exprs[expr_id];
        let block_and = match &expr.kind {
            ExprKind::Local(..) => {
                let place = unpack!(block = self.as_place(block, expr_id));
                let rvalue = Rvalue::Use(Operand::Copy(place));
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Reference { mutable, expr } => todo!(),
            ExprKind::Deref(expr_id) => todo!(),
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                let destination_then = destination.clone();
                let (then_end, mut else_blk) = self.in_if_then_scope(expr.span, |this| {
                    let then_blk = this.then_else_break(block, *cond).into_block();
                    this.expr_into_dest(destination_then, then_blk, *then_expr)
                });

                if let Some(&expr) = else_expr.as_ref() {
                    else_blk = self
                        .expr_into_dest(destination, else_blk, expr)
                        .into_block();
                } else {
                    self.push_assign_unit(else_blk, expr.span, destination, self.gcx);
                }

                let join_block = self.new_block_with_note("Join Block".into());
                self.goto(then_end, join_block, expr.span);
                self.goto(else_blk, join_block, expr.span);
                join_block.unit()
            }
            ExprKind::Assign { target, value } => todo!(),
            ExprKind::Unary { op, operand } => todo!(),
            ExprKind::Call { callee, args } => {
                let function = unpack!(block = self.as_local_operand(block, *callee));
                let args: Vec<Operand<'ctx>> = args
                    .iter()
                    .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                    .collect();
                let next = self.new_block();
                let terminator = TerminatorKind::Call {
                    func: function,
                    args,
                    destination,
                    target: next,
                };
                self.terminate(block, expr.span, terminator);
                next.unit()
            }
            ExprKind::Block(block_id) => self.lower_block(destination, block, *block_id),
            ExprKind::Adt(adt_expression) => todo!(),
            ExprKind::Field { lhs, index } => todo!(),
            ExprKind::Tuple { .. }
            | ExprKind::Literal(..)
            | ExprKind::Binary { .. }
            | ExprKind::Zst { .. } => {
                debug_assert!(match Category::of(&expr.kind) {
                    // should be handled above
                    Category::Rvalue(RvalueFunc::Into) => false,

                    // must be handled above or else we get an
                    // infinite loop in the builder; see
                    // e.g., `ExprKind::VarRef` above
                    Category::Place => false,

                    _ => true,
                });

                let rvalue = unpack!(block = self.as_local_rvalue(block, expr_id));
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
        };

        block_and
    }
}

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    fn then_else_break(&mut self, mut block: BasicBlockId, condition: ExprId) -> BlockAnd<()> {
        let place = unpack!(block = self.as_temp(block, condition));
        let operand = Operand::Move(Place::from_local(place));

        let then_block = self.new_block_with_note("then block".into());
        let else_block = self.new_block_with_note("else block".into());

        let expr = &self.thir.exprs[condition];
        self.terminate(
            block,
            expr.span,
            TerminatorKind::if_(operand, then_block, else_block),
        );
        self.break_for_else(else_block, expr.span);
        then_block.unit()
    }

    pub fn push_assign_unit(
        &mut self,
        block: BasicBlockId,
        span: Span,
        place: Place<'ctx>,
        gcx: Gcx<'ctx>,
    ) {
        self.push_assign(
            block,
            place,
            Rvalue::Use(Operand::Constant(Constant {
                ty: gcx.types.void,
                value: mir::ConstantKind::Unit,
            })),
            span,
        );
    }
}
