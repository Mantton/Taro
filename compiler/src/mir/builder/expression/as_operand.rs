use crate::{
    mir::{
        BasicBlockId, BlockAnd, BlockAndExtension, Category, Operand, Place, RvalueFunc,
        builder::MirBuilder,
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
        let category = Category::of(&expression.kind);

        match category {
            Category::Constant => {
                let constant = self.as_constant(expr_id);
                block.and(Operand::Constant(constant))
            }
            Category::Place | Category::Rvalue(RvalueFunc::Into | RvalueFunc::AsRvalue) => {
                let temp = unpack!(block = self.as_temp(block, expr_id));
                block.and(Operand::Move(Place::from_local(temp)))
            }
        }
    }
}
