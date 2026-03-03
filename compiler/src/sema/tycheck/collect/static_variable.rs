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
        if let hir::DeclarationKind::StaticVariable(node) = &declaration.kind {
            self.collect_static(declaration.id, node);
        }

        hir::walk_declaration(self, declaration)
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_static(&self, id: DefinitionID, node: &hir::StaticVariable) {
        let icx = DefTyLoweringCtx::new(id, self.context);
        let ty = icx.lowerer().lower_type(&node.ty);
        self.context.cache_type(id, ty);
        self.context.cache_static_mutability(id, node.mutability);
    }
}
