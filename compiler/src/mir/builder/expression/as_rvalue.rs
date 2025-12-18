use crate::{
    mir::{
        self, BasicBlockId, BinaryOperator, BlockAnd, BlockAndExtension, Category, Operand, Rvalue,
        RvalueFunc, builder::MirBuilder,
    },
    thir::{self, ExprId, ExprKind},
    unpack,
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn as_local_rvalue(&mut self, block: BasicBlockId, expr: ExprId) -> BlockAnd<Rvalue<'ctx>> {
        self.as_rvalue(block, expr)
    }

    pub fn as_rvalue(
        &mut self,
        mut block: BasicBlockId,
        expr_id: ExprId,
    ) -> BlockAnd<Rvalue<'ctx>> {
        let expr = &self.thir.exprs[expr_id];

        match &expr.kind {
            ExprKind::Assign { target, value } => todo!(),
            ExprKind::Unary { op, operand } => todo!(),
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs = unpack!(block = self.as_operand(block, *lhs));
                let rhs = unpack!(block = self.as_operand(block, *rhs));
                self.build_binary_op(block, *op, lhs, rhs)
            }
            ExprKind::Tuple { fields } => todo!(),

            ExprKind::If { .. }
            | ExprKind::Deref(..)
            | ExprKind::Reference { .. }
            | ExprKind::Local(..)
            | ExprKind::Call { .. }
            | ExprKind::Block(..)
            | ExprKind::Adt(..)
            | ExprKind::Field { .. } => {
                debug_assert!(!matches!(
                    Category::of(&expr.kind),
                    Category::Rvalue(RvalueFunc::AsRvalue) | Category::Constant
                ));
                let operand = unpack!(block = self.as_operand(block, expr_id));
                block.and(Rvalue::Use(operand))
            }

            ExprKind::Literal(..) | ExprKind::Zst { .. } => {
                let constant = self.as_constant(expr_id);
                block.and(Rvalue::Use(Operand::Constant(constant)))
            }
        }
    }
}

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn build_binary_op(
        &mut self,
        block: BasicBlockId,
        op: BinaryOperator,
        lhs: Operand<'ctx>,
        rhs: Operand<'ctx>,
    ) -> BlockAnd<Rvalue<'ctx>> {
        let rv = match op {
            _ => Rvalue::BinaryOp { op, lhs, rhs },
        };

        block.and(rv)
    }
}
