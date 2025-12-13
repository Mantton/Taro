use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir,
    sema::models::{AdtDef, AdtKind, Ty, TyKind},
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
                let adt_def = AdtDef {
                    name: node.identifier.symbol,
                    kind: AdtKind::Struct,
                    id: node.id,
                };
                let ty = Ty::new(TyKind::Adt(adt_def), self.context);
                self.context.cache_type(node.id, ty);
            }
            _ => {}
        }
        hir::walk_declaration(self, node)
    }
}
