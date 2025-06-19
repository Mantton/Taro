use crate::GlobalContext;
use crate::ty::SpannedConstraints;

use super::TypeLowerer;

pub struct ItemCtx<'ctx> {
    pub gcx: GlobalContext<'ctx>,
}

impl<'ctx> ItemCtx<'ctx> {
    pub fn new(gcx: GlobalContext<'ctx>) -> ItemCtx<'ctx> {
        ItemCtx { gcx }
    }
}

impl<'ctx> TypeLowerer<'ctx> for ItemCtx<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }

    fn probe_ty_param_constraints(
        &self,
        def_id: taroc_hir::DefinitionID,
        _: taroc_span::Identifier,
    ) -> &'ctx SpannedConstraints<'ctx> {
        let kind = self.gcx.def_kind(def_id);

        match kind {
            taroc_hir::DefinitionKind::Interface => self.gcx.predicates_of(def_id),
            _ => {
                let param = self.gcx.type_of(def_id);
                let self_predicates = self.gcx.predicates_of(def_id);
                let parent = self.gcx.parent(def_id);
                let parent_predicates = self.gcx.predicates_of(parent);

                let resulting: Vec<_> = parent_predicates
                    .into_iter()
                    .chain(self_predicates.into_iter())
                    .filter_map(|c| match c.value {
                        crate::ty::Constraint::Bound { ty, .. } if ty == param => Some(*c),
                        _ => None,
                    })
                    .collect();

                self.gcx.store.interners.alloc(resulting)
            }
        }
    }

    fn ty_infer(
        &self,
        _: Option<&crate::ty::GenericParameterDefinition>,
        span: taroc_span::Span,
    ) -> crate::ty::Ty<'ctx> {
        let gcx = self.gcx();
        gcx.diagnostics
            .error("missing generic argument".into(), span);
        gcx.store.common_types.error
    }
}
