use crate::{ty::Ty, utils::ty2str};

use super::func::FnCtx;

impl<'rcx, 'gcx> FnCtx<'rcx, 'gcx> {
    pub fn demand_coercion(
        &self,
        expression: &taroc_hir::Expression,
        expression_ty: Ty<'gcx>,
        expectation: Ty<'gcx>,
    ) -> Ty<'gcx> {
        let result = self.coerce(expression, expression_ty, expectation);

        match result {
            Ok(_) => return expectation,
            Err(_) => self.gcx.diagnostics.error(
                format!(
                    "type mismatch {} & {}",
                    ty2str(expression_ty, self.gcx),
                    ty2str(expectation, self.gcx)
                ),
                expression.span,
            ),
        }
        expectation
    }
}
