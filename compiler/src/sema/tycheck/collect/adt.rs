use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, HirVisitor},
    sema::models::{AdtDef, AdtKind, Ty, TyKind},
    span::Symbol,
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        match &node.kind {
            hir::DeclarationKind::Struct(_) => {
                self.cache_adt_type(node.id, node.identifier.symbol, AdtKind::Struct);
            }
            hir::DeclarationKind::Enum(_) => {
                self.cache_adt_type(node.id, node.identifier.symbol, AdtKind::Enum);
            }
            _ => {}
        }
        hir::walk_declaration(self, node)
    }
}

impl<'ctx> Actor<'ctx> {
    fn cache_adt_type(&self, id: hir::DefinitionID, name: Symbol, kind: AdtKind) {
        let adt_def = AdtDef { name, kind, id };
        let args = crate::sema::tycheck::utils::generics::GenericsBuilder::identity_for_item(
            self.context,
            id,
        );
        let ty = Ty::new(TyKind::Adt(adt_def, args), self.context);
        self.context.cache_type(id, ty);
    }
}
