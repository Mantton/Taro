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
    fn cache_extension_target_ty(&mut self, extension_id: DefinitionID, node: &hir::Extension) {
        let Some(head) = self.context.get_extension_type_head(extension_id) else {
            return;
        };

        if let TypeHead::Nominal(target_id) = head {
            if self.context.definition_kind(target_id) == DefinitionKind::Interface {
                return;
            }
        }

        let ctx = DefTyLoweringCtx::new(extension_id, self.context);
        let ty = ctx.lowerer().lower_type(&node.ty);
        self.context.cache_extension_target_ty(extension_id, ty);
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        let hir::DeclarationKind::Extension(node) = &declaration.kind else {
            return;
        };

        self.cache_extension_target_ty(declaration.id, node);
    }
}
