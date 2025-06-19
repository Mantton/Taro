use super::func::FnCtx;
use crate::lower::TypeLowerer;

impl<'ctx> TypeLowerer<'ctx> for FnCtx<'_, 'ctx> {
    fn gcx(&self) -> crate::GlobalContext<'ctx> {
        self.gcx
    }

    fn probe_ty_param_constraints(
        &self,
        def_id: taroc_hir::DefinitionID,
        assoc_ident: taroc_span::Identifier,
    ) -> &'ctx crate::ty::SpannedConstraints<'ctx> {
        todo!()
    }

    fn ty_infer(
        &self,
        _: Option<&crate::ty::GenericParameterDefinition>,
        span: taroc_span::Span,
    ) -> crate::ty::Ty<'ctx> {
        self.next_ty_var(span)
    }
}
