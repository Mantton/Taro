use crate::{
    mir::{
        BasicBlockId, BlockAnd, BlockAndExtension, Category, Operand, Place, builder::MirBuilder,
    },
    thir::ExprId,
    unpack,
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn as_local_operand(
        &mut self,
        block: BasicBlockId,
        expression: ExprId,
    ) -> BlockAnd<Operand<'ctx>> {
        self.as_operand(block, expression)
    }

    pub fn as_operand(
        &mut self,
        mut block: BasicBlockId,
        expr_id: ExprId,
    ) -> BlockAnd<Operand<'ctx>> {
        let expression = &self.thir.exprs[expr_id];
        let _ = Category::of(&expression.kind);
        let temp = unpack!(block = self.as_temp(block, expr_id));
        block.and(Operand::Move(Place::from_local(temp)))
    }
}
