use crate::{
    mir::{BasicBlockId, BlockAnd, BlockAndExtension, builder::MirBuilder},
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
            _ => {
                let _ = unpack!(block = self.as_temp(block, expr_id));
                block.unit()
            }
        }
    }
}
