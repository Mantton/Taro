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

    fn validate_repr_usage(
        &self,
        attributes: &hir::AttributeList,
        allow_on_this_declaration: bool,
    ) {
        for attr in attributes {
            if attr.as_known(self.context) != Some(hir::KnownAttribute::Repr) {
                continue;
            }
            if !allow_on_this_declaration {
                self.context.dcx().emit_error(
                    "@repr is only allowed on struct declarations".into(),
                    Some(attr.span),
                );
            }
        }
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        self.validate_repr_usage(
            &node.attributes,
            matches!(node.kind, hir::DeclarationKind::Struct(_)),
        );
        self.cache_attributes(node.id, &node.attributes);
        hir::walk_declaration(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        self.validate_repr_usage(&node.attributes, false);
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
