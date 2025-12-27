use crate::{
    mir::{BasicBlockId, BlockAnd, BlockAndExtension, Operand, builder::MirBuilder},
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
                let rhs = unpack!(block = self.as_local_rvalue(block, *value));
                let lhs = unpack!(block = self.as_place(block, *target));
                self.push_assign(block, lhs, rhs, expression.span);
                block.unit()
            }
            ExprKind::AssignOp { op, target, value } => {
                // Compound assignment: target op= value
                // Semantics: target = target op value
                let lhs_place = unpack!(block = self.as_place(block, *target));
                let rhs_operand = unpack!(block = self.as_operand(block, *value));

                // Read current value from LHS as an operand (Copy semantics)
                let lhs_operand = Operand::Copy(lhs_place.clone());

                // Compute binary op result
                let result =
                    unpack!(block = self.build_binary_op(block, *op, lhs_operand, rhs_operand));

                // Assign result back to LHS
                self.push_assign(block, lhs_place, result, expression.span);
                block.unit()
            }
            _ => {
                let _ = unpack!(block = self.as_temp(block, expr_id));
                block.unit()
            }
        }
    }
}
