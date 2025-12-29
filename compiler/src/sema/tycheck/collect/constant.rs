use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
};

pub fn run(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::Constant(node) = &declaration.kind {
            self.collect_constant(declaration.id, node);
        }
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &hir::AssociatedDeclaration,
        _: hir::AssocContext,
    ) -> Self::Result {
        if let hir::AssociatedDeclarationKind::Constant(node) = &declaration.kind {
            self.collect_constant(declaration.id, node);
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_constant(&self, id: DefinitionID, node: &hir::Constant) {
        let icx = DefTyLoweringCtx::new(id, self.context);
        let ty = icx.lowerer().lower_type(&node.ty);
        self.context.cache_type(id, ty);
    }
}
