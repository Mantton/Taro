use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::{
        resolve::models::{DefinitionKind, TypeHead},
        tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    },
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

pub(crate) fn cache_target(context: GlobalContext<'_>, impl_id: DefinitionID, target: &hir::Type) {
    let Some(head) = context.get_impl_type_head(impl_id) else {
        return;
    };

    if let TypeHead::Nominal(target_id) = head {
        if context.definition_kind(target_id) == DefinitionKind::Interface {
            return;
        }
    }

    let ctx = DefTyLoweringCtx::new(impl_id, context);
    let ty = ctx.lowerer().lower_type(target);
    context.cache_impl_target_ty(impl_id, ty);
    // Aliases are transparent to coherence and member lookup, including
    // aliases imported from another package.
    let normalized = crate::sema::tycheck::utils::normalize_aliases(context, ty);
    if let Some(head) = crate::sema::tycheck::utils::type_head_from_value_ty(normalized) {
        context.cache_impl_type_head(impl_id, head);
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        let hir::DeclarationKind::Impl(node) = &declaration.kind else {
            return;
        };

        cache_target(self.context, declaration.id, &node.target);
    }
}
