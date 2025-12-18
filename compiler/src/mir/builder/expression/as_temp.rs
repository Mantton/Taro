use crate::{
    mir::{self, BasicBlockId, BlockAnd, BlockAndExtension, LocalKind, Place, builder::MirBuilder},
    thir::{self},
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn as_temp(
        &mut self,
        block: BasicBlockId,
        expression: thir::ExprId,
    ) -> BlockAnd<mir::LocalId> {
        self.as_temp_inner(block, expression)
    }

    fn as_temp_inner(
        &mut self,
        mut block: BasicBlockId,
        expression: thir::ExprId,
    ) -> BlockAnd<mir::LocalId> {
        let expr = &self.thir.exprs[expression];
        let lid = self.push_local(expr.ty, LocalKind::Temp, None, expr.span);
        block = self
            .expr_into_dest(Place::from_local(lid), block, expression)
            .into_block();
        block.and(lid)
    }
}
