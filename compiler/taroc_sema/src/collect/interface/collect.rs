use crate::GlobalContext;
use crate::lower::{ItemCtx, LoweringRequest, TypeLowerer};
use crate::ty::{AssocTyKind, InterfaceDefinition, TyKind};
use std::collections::HashMap;
use taroc_error::CompileResult;
use taroc_hir::visitor::HirVisitor;
use taroc_span::{Identifier, Spanned};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, d: &taroc_hir::Declaration) -> Self::Result {
        let id = d.id;
        match &d.kind {
            taroc_hir::DeclarationKind::Interface(node) => {
                self.collect(id, d.identifier, &d.attributes, node)
            }
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, d);
    }

    fn visit_assoc_declaration(
        &mut self,
        _: &taroc_hir::AssociatedDeclaration,
        _: taroc_hir::visitor::AssocContext,
    ) -> Self::Result {
        return;
    }

    fn visit_function_declaration(&mut self, _: &taroc_hir::FunctionDeclaration) -> Self::Result {
        return;
    }

    fn visit_foreign_declaration(&mut self, _: &taroc_hir::ForeignDeclaration) -> Self::Result {
        return;
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect(
        &mut self,
        id: taroc_hir::NodeID,
        _: Identifier,
        _: &taroc_hir::AttributeList,
        node: &taroc_hir::InterfaceDefinition,
    ) {
        let gcx = self.context;
        let def_id = gcx.def_id(id);
        let conformances = &node.generics.conformance;

        // super interfaces
        let mut superfaces = vec![];
        if let Some(conformances) = conformances {
            let icx = ItemCtx::new(gcx);
            for conformance in conformances.interfaces.iter() {
                let reference = icx.lowerer().lower_interface_reference(
                    gcx.store.common_types.self_type_parameter,
                    conformance,
                    &LoweringRequest::default(),
                );

                superfaces.push(Spanned::new(reference, conformance.path.span));
            }
        }
        // assoc items
        let mut assoc_types = HashMap::new();
        for declaration in &node.declarations {
            match &declaration.kind {
                taroc_hir::AssociatedDeclarationKind::Type(_) => {
                    let assoc_id = gcx.def_id(declaration.id);

                    // duplicates caught by resolver
                    assoc_types.insert(declaration.identifier.symbol, assoc_id);
                    let ty = gcx
                        .store
                        .interners
                        .intern_ty(TyKind::AssociatedType(AssocTyKind::Inherent(assoc_id)));
                    gcx.cache_type(assoc_id, ty);
                }
                _ => {}
            }
        }

        let definition = InterfaceDefinition {
            id: def_id,
            superfaces,
            assoc_types,
        };

        let definition = gcx.alloc(definition);
        gcx.with_type_database(def_id.package(), |db| {
            db.interfaces.insert(def_id, definition)
        });
    }
}
