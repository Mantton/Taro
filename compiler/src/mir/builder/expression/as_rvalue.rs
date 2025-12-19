use crate::{
    mir::{
        AggregateKind, BasicBlockId, BinaryOperator, BlockAnd, BlockAndExtension, Category,
        Constant, ConstantKind, Operand, Rvalue, RvalueFunc, builder::MirBuilder,
    },
    thir::{ExprId, ExprKind, FieldIndex},
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
            ExprKind::Assign { .. } => {
                block = self.lower_statement_expression(block, expr_id).into_block();
                block.and(Rvalue::Use(Operand::Constant(Constant {
                    ty: self.gcx.types.void,
                    value: ConstantKind::Unit,
                })))
            }
            ExprKind::Unary { op, operand } => {
                let operand = unpack!(block = self.as_operand(block, *operand));
                block.and(Rvalue::UnaryOp { op: *op, operand })
            }
            ExprKind::Make { .. } => unreachable!("make should be handled in into_dest"),
            ExprKind::Binary { op, lhs, rhs } => {
                let lhs = unpack!(block = self.as_operand(block, *lhs));
                let rhs = unpack!(block = self.as_operand(block, *rhs));
                self.build_binary_op(block, *op, lhs, rhs)
            }
            ExprKind::Tuple { fields } => {
                let mut ops = Vec::with_capacity(fields.len());
                for field in fields.iter() {
                    let op = unpack!(block = self.as_operand(block, *field));
                    ops.push(op);
                }
                let fields: index_vec::IndexVec<FieldIndex, Operand<'ctx>> =
                    index_vec::IndexVec::from_vec(ops);
                block.and(Rvalue::Aggregate {
                    kind: AggregateKind::Tuple,
                    fields,
                })
            }
            ExprKind::If { .. }
            | ExprKind::Deref(..)
            | ExprKind::Reference { .. }
            | ExprKind::Local(..)
            | ExprKind::Logical { .. }
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
