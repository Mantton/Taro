use crate::{
    mir::{
        BasicBlockId, BlockAnd, BlockAndExtension, Category, Operand, Place, RvalueFunc,
        builder::MirBuilder,
    },
    thir::ExprId,
    unpack,
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn as_operand(
        &mut self,
        mut block: BasicBlockId,
        expr_id: ExprId,
    ) -> BlockAnd<Operand<'ctx>> {
        // Even constants must use their prepared value: recreating a
        // noncopyable constant would leave the original owner undestroyed.
        if let Some(operand) = self.prepared_argument_operand(block, expr_id) {
            return block.and(operand);
        }
        let expression = &self.thir.exprs[expr_id];
        let category = Category::of(&expression.kind);

        match category {
            Category::Constant => {
                let constant = self.as_constant(expr_id);
                block.and(Operand::Constant(constant))
            }
            Category::Place | Category::Rvalue(RvalueFunc::Into | RvalueFunc::AsRvalue) => {
                let temp = unpack!(block = self.as_temp(block, expr_id));
                let place = Place::from_local(temp);
                block.and(Operand::Copy(place))
            }
        }
    }
}
