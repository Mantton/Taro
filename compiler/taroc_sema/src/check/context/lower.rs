use super::func::FnCtx;
use crate::lower::TypeLowerer;

impl<'tcx> TypeLowerer<'tcx> for FnCtx<'_, 'tcx> {
    fn gcx(&self) -> crate::GlobalContext<'tcx> {
        self.gcx
    }

    fn probe_ty_param_constraints(
        &self,
        def_id: taroc_hir::DefinitionID,
        assoc_ident: taroc_span::Identifier,
    ) -> &'tcx crate::ty::SpannedConstraints<'tcx> {
        todo!()
    }
}
