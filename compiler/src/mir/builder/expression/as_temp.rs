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
        self.materialize_temp(block, expression, false)
    }

    pub(super) fn as_addressable_temp(
        &mut self,
        block: BasicBlockId,
        expression: thir::ExprId,
    ) -> BlockAnd<mir::LocalId> {
        self.materialize_temp(block, expression, true)
    }

    fn materialize_temp(
        &mut self,
        mut block: BasicBlockId,
        expression: thir::ExprId,
        addressable: bool,
    ) -> BlockAnd<mir::LocalId> {
        if let Some(place) = self.prepared_call_arguments.get(&expression) {
            debug_assert!(place.projection.is_empty());
            return block.and(place.local);
        }
        let expr = &self.thir.exprs[expression];
        let lid = self.push_local(expr.ty, LocalKind::Temp, true, None, expr.span);
        if addressable {
            self.push_storage_live(block, lid, expr.span);
            self.register_storage_cleanup(lid, expr.span);
        }
        block = self
            .expr_into_dest(Place::from_local(lid), block, expression)
            .into_block();
        block.and(lid)
    }
}
