use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
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
    fn cache_attributes(&self, id: DefinitionID, attributes: &hir::AttributeList) {
        if attributes.is_empty() {
            return;
        }
        self.context.cache_attributes(id, attributes.clone());
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        self.cache_attributes(node.id, &node.attributes);
        hir::walk_declaration(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        self.cache_attributes(node.id, &node.attributes);
        hir::walk_assoc_declaration(self, node, context)
    }

    fn visit_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        context: hir::FunctionContext,
    ) -> Self::Result {
        self.context.cache_definition_unsafe(id, node.is_unsafe);
        hir::walk_function(self, id, node, context)
    }
}
