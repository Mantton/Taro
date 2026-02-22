use rustc_hash::FxHashMap;

use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, AssociatedDeclarationKind, DefinitionID, Interface},
    sema::{
        models::{InterfaceDefinition, InterfaceReference},
        tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    },
    span::{Spanned, Symbol},
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    super::hierarchy::run(package, context)?; // Check Hierarchy Validity
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl hir::HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::Interface(definition) = &node.kind {
            self.collect(node.id, definition);
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect(&mut self, id: DefinitionID, definition: &Interface) {
        let superfaces = self.collect_superfaces(id, definition);
        let assoc_types = self.collect_associated_types(definition);

        let definition = InterfaceDefinition {
            id,
            superfaces,
            assoc_types,
        };

        let gcx = self.context;
        let definition = gcx.store.arenas.interface_definitions.alloc(definition);
        gcx.with_session_type_database(|db| db.def_to_iface_def.insert(id, definition));
    }

    fn collect_superfaces(
        &mut self,
        id: DefinitionID,
        definition: &Interface,
    ) -> Vec<Spanned<InterfaceReference<'ctx>>> {
        let gcx = self.context;

        let Some(conformances) = &definition.conformances else {
            return vec![];
        };

        let icx = DefTyLoweringCtx::new(id, gcx);
        let self_ty = gcx.types.self_type_parameter;
        let mut superfaces = vec![];
        for conformance in &conformances.bounds {
            let reference = icx
                .lowerer()
                .lower_interface_reference(self_ty, &conformance);
            superfaces.push(Spanned::new(reference, conformance.span));
        }

        superfaces
    }

    fn collect_associated_types(
        &mut self,
        definition: &Interface,
    ) -> FxHashMap<Symbol, DefinitionID> {
        let mut assoc_types = FxHashMap::default();

        for declaration in &definition.declarations {
            match &declaration.kind {
                AssociatedDeclarationKind::Type(_) => {
                    let assoc_id = declaration.id;
                    assoc_types.insert(declaration.identifier.symbol, assoc_id);

                    // TODO: Record Type for ID
                }
                _ => continue,
            }
        }

        assoc_types
    }
}
