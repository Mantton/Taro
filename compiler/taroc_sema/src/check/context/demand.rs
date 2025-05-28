use crate::ty::Ty;

use super::func::FnCtx;

impl<'rcx, 'gcx> FnCtx<'rcx, 'gcx> {
    pub fn demand_coercion(
        &self,
        expression: &taroc_hir::Expression,
        expression_ty: Ty<'gcx>,
        expectation: Ty<'gcx>,
    ) -> Ty<'gcx> {
        let result = self.coerce(expression, expression_ty, expectation);
        expectation
    }
}
