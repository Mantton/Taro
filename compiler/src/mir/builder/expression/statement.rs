use crate::{
    mir::{BasicBlockId, BlockAnd, BlockAndExtension, Operand, Place, Rvalue, builder::MirBuilder},
    thir::{self, ExprKind},
    unpack,
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn lower_statement_expression(
        &mut self,
        mut block: BasicBlockId,
        expr_id: thir::ExprId,
    ) -> BlockAnd<()> {
        let expression = &self.thir.exprs[expr_id];

        match &expression.kind {
            ExprKind::Assign { target, value } => {
                // Materialize before any effectful destination evaluation.
                // Plain local/field/deref paths emit no code, so scalar rvalues
                // can stay directly in their final assignment without another
                // load/store temporary (important for bounded leaf inlining).
                // Dynamic access lowering must likewise acquire write access
                // only after evaluating this rvalue.
                let rhs = if self.is_static_destination(*target) && !false {
                    unpack!(block = self.as_rvalue(block, *value))
                } else {
                    Rvalue::Use(unpack!(block = self.as_operand(block, *value)))
                };
                if self.is_instant_class_field(*target) {
                    let Rvalue::Use(incoming) = rhs else {
                        unreachable!("class field assignment materializes its RHS")
                    };
                    return self.class_field_write(block, *target, incoming);
                }
                let lhs = unpack!(block = self.as_place(block, *target));
                {
                    self.push_assign(block, lhs, rhs, expression.span);
                    block.unit()
                }
            }
            ExprKind::AssignOp { op, target, value } => {
                // Primitive compound assignment snapshots the RHS first, then
                // resolves the destination exactly once. Its exclusive access
                // must not start while RHS callbacks are still running.
                let rhs_operand = unpack!(block = self.as_operand(block, *value));
                let lhs_ty = self.thir.exprs[*target].ty;
                if op.compound_name().is_some()
                    && self.thir.exprs[*value].ty == lhs_ty
                    && matches!(
                        crate::sema::tycheck::utils::normalize_aliases(self.gcx, lhs_ty).kind(),
                        crate::sema::models::TyKind::Int(_)
                            | crate::sema::models::TyKind::UInt(_)
                            | crate::sema::models::TyKind::Float(_)
                            | crate::sema::models::TyKind::Bool
                    )
                    && self.is_instant_class_field(*target)
                {
                    let checked = self.should_check_overflow(*op, lhs_ty);
                    return self.class_field_modify(block, *target, *op, checked, rhs_operand);
                }
                let lhs_place = unpack!(block = self.as_place(block, *target));

                // Read current value from LHS into a temp to avoid reusing the
                // place directly in the binary op (matches `x = x + y` path).
                let lhs_tmp = self.new_temp_with_ty(lhs_ty, expression.span);
                self.push_assign(
                    block,
                    Place::from_local(lhs_tmp),
                    Rvalue::Use(Operand::Copy(lhs_place.clone())),
                    expression.span,
                );
                let lhs_operand = Operand::Copy(Place::from_local(lhs_tmp));

                // Compute binary op result
                let result = unpack!(
                    block = self.build_binary_op(
                        block,
                        *op,
                        lhs_ty,
                        expression.span,
                        lhs_operand,
                        rhs_operand
                    )
                );

                // Assign result back to LHS
                self.push_assign(block, lhs_place, result, expression.span);
                block.unit()
            }
            _ => {
                // Evaluate for side effects; the value is discarded.
                unpack!(block = self.as_temp(block, expr_id));
                block.unit()
            }
        }
    }

    fn is_static_destination(&self, expression: thir::ExprId) -> bool {
        match &self.thir.exprs[expression].kind {
            ExprKind::Local(_) | ExprKind::Upvar { .. } => true,
            ExprKind::Field { lhs, .. } => {
                !self.is_class_field(expression) && self.is_static_destination(*lhs)
            }
            ExprKind::Deref(lhs) => self.is_static_destination(*lhs),
            _ => false,
        }
    }
}
