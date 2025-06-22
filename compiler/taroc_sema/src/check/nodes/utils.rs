use crate::{
    check::context::func::FnCtx,
    ty::{Ty, TyKind},
};
use taroc_hir::{DefinitionID, DefinitionKind};
use taroc_span::{Identifier, Span};

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn resolve_qualified_method_call(
        &self,
        method: Identifier,
        self_ty: Ty<'ctx>,
        self_ty_span: Span,
    ) -> Result<(DefinitionKind, DefinitionID), ()> {
        let gcx = self.gcx;

        // Could be Enum Variant
        if let TyKind::Adt(def, _) = self_ty.kind()
            && gcx.def_kind(def.id) == DefinitionKind::Enum
        {
            // could it though?
        }

        // Probe for associated function
        let file = self_ty_span.file;
        todo!("probe for method")
    }
}
