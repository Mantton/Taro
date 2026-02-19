use crate::{
    compile::context::GlobalContext, hir::DefinitionID, sema::tycheck::lower::TypeLowerer,
};

pub struct DefTyLoweringCtx<'ctx> {
    gcx: GlobalContext<'ctx>,
    id: DefinitionID,
}

type Ctx<'ctx> = DefTyLoweringCtx<'ctx>;

impl<'ctx> Ctx<'ctx> {
    pub fn new(id: DefinitionID, gcx: GlobalContext<'ctx>) -> Ctx<'ctx> {
        Ctx { id, gcx }
    }
}

impl<'ctx> TypeLowerer<'ctx> for Ctx<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }

    fn current_definition(&self) -> Option<DefinitionID> {
        Some(self.id)
    }

    fn ty_infer(
        &self,
        _: Option<&crate::sema::models::GenericParameterDefinition>,
        span: crate::span::Span,
    ) -> crate::sema::models::Ty<'ctx> {
        let gcx = self.gcx();
        gcx.dcx()
            .emit_error("missing generic argument".into(), Some(span));
        gcx.types.error
    }

    fn const_infer(
        &self,
        ty: crate::sema::models::Ty<'ctx>,
        _: Option<&crate::sema::models::GenericParameterDefinition>,
        span: crate::span::Span,
    ) -> crate::sema::models::Const<'ctx> {
        let gcx = self.gcx();
        gcx.dcx()
            .emit_error("missing generic argument".into(), Some(span));
        crate::sema::models::Const {
            ty,
            kind: crate::sema::models::ConstKind::Value(crate::sema::models::ConstValue::Unit),
        }
    }
}
