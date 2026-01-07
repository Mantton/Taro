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

impl<'ctx> Actor<'ctx> {
    fn cache_impl_target_ty(&mut self, impl_id: DefinitionID, node: &hir::Impl) {
        let Some(head) = self.context.get_impl_type_head(impl_id) else {
            return;
        };

        if let TypeHead::Nominal(target_id) = head {
            if self.context.definition_kind(target_id) == DefinitionKind::Interface {
                return;
            }
        }

        let ctx = DefTyLoweringCtx::new(impl_id, self.context);
        let ty = ctx.lowerer().lower_type(&node.target);
        self.context.cache_impl_target_ty(impl_id, ty);
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        let hir::DeclarationKind::Impl(node) = &declaration.kind else {
            return;
        };

        self.cache_impl_target_ty(declaration.id, node);
    }
}
