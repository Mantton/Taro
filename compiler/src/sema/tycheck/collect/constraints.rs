use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, AssociatedDeclarationKind, DeclarationKind, DefinitionID, DefinitionKind, HirVisitor},
    sema::{
        models::{Constraint, InterfaceReference},
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
            DeclarationKind::Extension(node) => self.collect_definition(d.id, &node.generics),
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
            AssociatedDeclarationKind::Operator(node) => {
                self.collect_definition(declaration.id, &node.function.generics)
            }
            _ => {}
        }

        hir::walk_assoc_declaration(self, declaration, context)
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_definition(&mut self, id: DefinitionID, generics: &hir::Generics) {
        let constraints = self.collect_internal(id, generics);
        self.context.cache_constraints(id, constraints);
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

        if matches!(gcx.definition_kind(def_id), DefinitionKind::Interface) {
            let self_ty = gcx.types.self_type_parameter;
            let arguments = GenericsBuilder::identity_for_item(gcx, def_id);
            let interface_ref = InterfaceReference {
                id: def_id,
                arguments,
            };

            let constraint = Constraint::Bound {
                ty: self_ty,
                interface: interface_ref,
            };
            constraints.push(Spanned::new(
                constraint,
                gcx.definition_ident(def_id).span,
            ));
        }

        let hir_parameters = generics.type_parameters.as_ref().map(|f| &f.parameters);
        if let Some(hir_parameters) = hir_parameters {
            for param in hir_parameters.iter() {
                let Some(bounds) = &param.bounds else {
                    continue;
                };

                let ty = gcx.get_type(param.id);
                for bound in bounds.iter() {
                    let constraint = Constraint::Bound {
                        ty,
                        interface: icx
                            .lowerer()
                            .lower_interface_reference(ty, &bound.path),
                    };
                    constraints.push(Spanned::new(constraint, bound.path.span));
                }
            }
        }

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
                    hir::GenericRequirement::ConformanceRequirement(node) => {
                        let ty = icx.lowerer().lower_type(&node.bounded_type);
                        for bound in node.bounds.iter() {
                            let constraint = Constraint::Bound {
                                ty,
                                interface: icx
                                    .lowerer()
                                    .lower_interface_reference(ty, &bound.path),
                            };
                            constraints.push(Spanned::new(constraint, node.span));
                        }
                    }
                };
            }
        }

        constraints
    }
}
