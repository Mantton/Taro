use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{
        self, AssociatedDeclarationKind, DeclarationKind, DefinitionID, DefinitionKind, HirVisitor,
    },
    sema::{
        models::{Constraint, InterfaceReference, TyKind},
        tycheck::{
            lower::{DefTyLoweringCtx, TypeLowerer},
            utils::generics::GenericsBuilder,
        },
    },
    span::Spanned,
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(package: &hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        hir::walk_package(&mut actor, package);
        context.dcx().ok()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, d: &hir::Declaration) -> Self::Result {
        match &d.kind {
            DeclarationKind::Interface(node) => self.collect_definition(d.id, &node.generics),
            DeclarationKind::Struct(node) => self.collect_definition(d.id, &node.generics),
            DeclarationKind::Enum(node) => self.collect_definition(d.id, &node.generics),
            DeclarationKind::Function(node) => self.collect_definition(d.id, &node.generics),
            DeclarationKind::Impl(node) => self.collect_definition(d.id, &node.generics),
            DeclarationKind::TypeAlias(node) => self.collect_definition(d.id, &node.generics),
            _ => {}
        }

        hir::walk_declaration(self, d)
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        match &declaration.kind {
            AssociatedDeclarationKind::Function(node) => {
                self.collect_definition(declaration.id, &node.generics)
            }
            AssociatedDeclarationKind::Type(node) => {
                self.collect_definition(declaration.id, &node.generics)
            }
            _ => {}
        }

        hir::walk_assoc_declaration(self, declaration, context)
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_definition(&mut self, id: DefinitionID, generics: &hir::Generics) {
        let constraints = self.collect_internal(id, generics);
        self.context.update_constraints(id, constraints);
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_internal(
        &mut self,
        def_id: DefinitionID,
        generics: &hir::Generics,
    ) -> Vec<Spanned<Constraint<'ctx>>> {
        let gcx = self.context;
        let icx = DefTyLoweringCtx::new(def_id, gcx);
        let mut constraints = vec![];

        // Helper function (not closure) to avoid borrow issues
        fn add_interface_constraints<'ctx>(
            gcx: GlobalContext<'ctx>,
            constraints: &mut Vec<Spanned<Constraint<'ctx>>>,
            ty: crate::sema::models::Ty<'ctx>,
            interface: InterfaceReference<'ctx>,
            span: crate::span::Span
        ) {
            // 1. Add Bound Constraint
            // Check for duplicates (exact match)
            let exists = constraints.iter().any(|existing| match existing.value {
                Constraint::Bound {
                    ty: existing_ty,
                    interface: existing_iface,
                } => existing_ty == ty && existing_iface == interface,
                _ => false,
            });

            if !exists {
                let constraint = Constraint::Bound { ty, interface };
                constraints.push(Spanned::new(constraint, span));
            }
            
            // 2. Add Type Equality Constraints from Bindings
            if !interface.bindings.is_empty() {
                // Break cycle: Look up associated type ID directly from InterfaceDefinition
                // which is collected early (phase 40), avoiding dependency on full Requirements (phase 49).
                
                let assoc_map = gcx.with_type_database(interface.id.package(), |db| {
                    db.def_to_iface_def
                        .get(&interface.id)
                        .map(|def| def.assoc_types.clone())
                });

                if let Some(assoc_map) = assoc_map {
                     for binding in interface.bindings {
                        if let Some(&assoc_id) = assoc_map.get(&binding.name) {
                             let alias_ty = gcx.store.interners.intern_ty(TyKind::Alias {
                                 kind: crate::sema::models::AliasKind::Projection,
                                 def_id: assoc_id,
                                 args: interface.arguments,
                             });
                             
                             let eq_constraint = Constraint::TypeEquality(alias_ty, binding.ty);
                             constraints.push(Spanned::new(eq_constraint, span));
                        }
                    }
                }
            }
        }

        // PASS 1: Collect Explicit Bounds (Self, Params, Where-Conformances)
        // We must process bounds first and register them in the database so that
        // subsequent projection lowering (e.g., T.Item) can find them.

        if matches!(gcx.definition_kind(def_id), DefinitionKind::Interface) {
            let self_ty = gcx.types.self_type_parameter;
            let arguments = GenericsBuilder::identity_for_item(gcx, def_id);
            let interface_ref = InterfaceReference {
                id: def_id,
                arguments,
                bindings: &[],
            };

            let constraint = Constraint::Bound {
                ty: self_ty,
                interface: interface_ref,
            };
            constraints.push(Spanned::new(constraint, gcx.definition_ident(def_id).span));
        }

        let hir_parameters = generics.type_parameters.as_ref().map(|f| &f.parameters);
        if let Some(hir_parameters) = hir_parameters {
            for param in hir_parameters.iter() {
                let Some(bounds) = &param.bounds else {
                    continue;
                };

                let ty = gcx.get_type(param.id);
                for bound in bounds.iter() {
                    let interface = icx.lowerer().lower_interface_reference(ty, &bound.path);
                    add_interface_constraints(gcx, &mut constraints, ty, interface, bound.path.span);
                }
            }
        }

        if let Some(clause) = &generics.where_clause {
            for requirement in clause.requirements.iter() {
                match &requirement {
                    hir::GenericRequirement::ConformanceRequirement(node) => {
                        let ty = icx.lowerer().lower_type(&node.bounded_type);
                        for bound in node.bounds.iter() {
                            let interface =
                                icx.lowerer().lower_interface_reference(ty, &bound.path);
                            add_interface_constraints(gcx, &mut constraints, ty, interface, node.span);
                        }
                    }
                    _ => {} // Skip equalities in Pass 1
                };
            }
        }

        // Commit bounds to DB immediately to make them visible for lowering in Pass 2
        gcx.update_constraints(def_id, constraints.clone());

        // PASS 2: Collect Type Equalities
        // Now that bounds are visible, we can safely lower projections like `T.Item`.
        if let Some(clause) = &generics.where_clause {
            for requirement in clause.requirements.iter() {
                 match &requirement {
                    hir::GenericRequirement::SameTypeRequirement(node) => {
                        let constraint = Constraint::TypeEquality(
                            icx.lowerer().lower_type(&node.bounded_type),
                            icx.lowerer().lower_type(&node.bound),
                        );
                        constraints.push(Spanned::new(constraint, node.span));
                    }
                    _ => {} // Skip bounds (already handled)
                };
            }
        }

        constraints
    }
}
