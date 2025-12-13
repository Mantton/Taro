use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir,
    sema::models::{Ty, TyKind},
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl hir::HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        match &node.kind {
            hir::DeclarationKind::Struct(_) => {
                let ty = Ty::new(TyKind::Adt(node.id), self.context);
                self.context.cache_type(node.id, ty);
            }
            _ => {}
        }
        hir::walk_declaration(self, node)
    }
}

