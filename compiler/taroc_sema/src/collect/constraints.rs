use crate::GlobalContext;
use crate::lower::{ItemCtx, LoweringRequest, TypeLowerer};
use crate::ty::{Constraint, GenericArgument, InterfaceReference};
use taroc_error::CompileResult;
use taroc_hir::{
    DefinitionID, DefinitionKind, NodeID,
    visitor::{self, HirVisitor},
};
use taroc_span::Spanned;

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

/// Collect & Cache Generics Information for a Definition
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
        match &d.kind {
            taroc_hir::DeclarationKind::Interface(node) => {
                self.collect_definition(d.id, &node.generics)
            }
            taroc_hir::DeclarationKind::Struct(node) => {
                self.collect_definition(d.id, &node.generics)
            }
            taroc_hir::DeclarationKind::Enum(node) => self.collect_definition(d.id, &node.generics),
            taroc_hir::DeclarationKind::Function(node) => {
                self.collect_definition(d.id, &node.generics)
            }
            taroc_hir::DeclarationKind::Extend(node) => self.collect_extension(d.id, &node),
            taroc_hir::DeclarationKind::TypeAlias(node) => {
                self.collect_definition(d.id, &node.generics)
            }
            _ => {}
        }

        visitor::walk_declaration(self, d)
    }

    fn visit_function_declaration(&mut self, d: &taroc_hir::FunctionDeclaration) -> Self::Result {
        match &d.kind {
            taroc_hir::FunctionDeclarationKind::Struct(node) => {
                self.collect_definition(d.id, &node.generics)
            }
            taroc_hir::FunctionDeclarationKind::Enum(node) => {
                self.collect_definition(d.id, &node.generics)
            }
            taroc_hir::FunctionDeclarationKind::Function(node) => {
                self.collect_definition(d.id, &node.generics)
            }
            taroc_hir::FunctionDeclarationKind::TypeAlias(node) => {
                self.collect_definition(d.id, &node.generics)
            }
            _ => {}
        }
        visitor::walk_function_declaration(self, d)
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &taroc_hir::AssociatedDeclaration,
        context: taroc_hir::visitor::AssocContext,
    ) -> Self::Result {
        match &declaration.kind {
            taroc_hir::AssociatedDeclarationKind::Function(node) => {
                self.collect_definition(declaration.id, &node.generics)
            }
            taroc_hir::AssociatedDeclarationKind::Type(node) => {
                self.collect_definition(declaration.id, &node.generics)
            }
            taroc_hir::AssociatedDeclarationKind::Operator(_, node) => {
                self.collect_definition(declaration.id, &node.generics)
            }
            _ => {}
        }

        visitor::walk_assoc_declaration(self, declaration, context)
    }

    fn visit_foreign_declaration(&mut self, d: &taroc_hir::ForeignDeclaration) -> Self::Result {
        match &d.kind {
            taroc_hir::ForeignDeclarationKind::Function(node) => {
                self.collect_definition(d.id, &node.generics)
            }
            taroc_hir::ForeignDeclarationKind::Type(node) => {
                self.collect_definition(d.id, &node.generics)
            }
        }

        visitor::walk_foreign_declaration(self, d)
    }
}
impl<'ctx> Actor<'ctx> {
    fn collect_definition(&mut self, id: NodeID, generics: &taroc_hir::Generics) {
        let def_id = self.context.def_id(id);
        let constraints = self.collect_internal(def_id, generics);
        self.context.cache_def_constraints(def_id, constraints);
    }

    fn collect_extension(&mut self, id: NodeID, node: &taroc_hir::Extend) {
        let def_id = self.context.def_id(id);

        let mut constraints = vec![];

        if let Some(implicit) = self.collect_implicit_extension_constraint(&node.ty) {
            constraints.extend(implicit);
        }

        let explicit = self.collect_internal(def_id, &node.generics);
        constraints.extend(explicit);
        self.context.cache_def_constraints(def_id, constraints);
    }
}
impl<'ctx> Actor<'ctx> {
    fn collect_internal(
        &mut self,
        def_id: DefinitionID,
        generics: &taroc_hir::Generics,
    ) -> Vec<Spanned<Constraint<'ctx>>> {
        let icx = ItemCtx::new(self.context);
        let mut constraints = vec![];

        // inteface implict self type param constraint
        if matches!(
            self.context.def_kind(def_id),
            taroc_hir::DefinitionKind::Interface
        ) {
            let gcx = self.context;
            // Build constraint : Self : Interface
            let generics = gcx.generics_of(def_id);

            let self_ty = gcx.store.common_types.self_type_parameter;
            let arguments: Vec<_> = generics
                .parameters
                .iter()
                .enumerate()
                .map(|(index, param)| match param.kind {
                    crate::ty::GenericParameterDefinitionKind::Type { .. } => {
                        let ty = if index == 0 {
                            gcx.store.common_types.self_type_parameter
                        } else {
                            gcx.type_of(param.id)
                        };

                        GenericArgument::Type(ty)
                    }
                    crate::ty::GenericParameterDefinitionKind::Const { .. } => todo!(),
                })
                .collect();
            let arguments = gcx.store.interners.intern_generic_args(&arguments);
            let interface_ref = InterfaceReference {
                id: def_id,
                arguments,
            };

            let constraint = Constraint::Bound {
                ty: self_ty,
                interface: interface_ref,
            };

            constraints.push(Spanned::new(constraint, gcx.ident_for(def_id).span));
        }
        // Type Parameters
        let hir_parameters = generics.type_parameters.as_ref().map(|f| &f.parameters);
        if let Some(hir_parameters) = hir_parameters {
            for param in hir_parameters.iter() {
                let Some(bounds) = &param.bounds else {
                    continue;
                };

                let param_def_id = self.context.def_id(param.id);
                let ty = self.context.type_of(param_def_id);
                for bound in bounds.iter() {
                    let span = bound.path.path.span;
                    let constraint = Constraint::Bound {
                        ty,
                        interface: icx.lowerer().lower_interface_reference(
                            ty,
                            &bound.path,
                            &LoweringRequest::default(),
                        ),
                    };
                    constraints.push(Spanned {
                        span,
                        value: constraint,
                    });
                }
            }
        }

        // Where Clause
        if let Some(clause) = &generics.where_clause {
            for requirement in clause.requirements.iter() {
                match &requirement {
                    taroc_hir::GenericRequirement::SameTypeRequirement(node) => {
                        let constraint = Constraint::TypeEquality(
                            icx.lowerer()
                                .lower_type(&node.bounded_type, &LoweringRequest::default()),
                            icx.lowerer()
                                .lower_type(&node.bound, &LoweringRequest::default()),
                        );

                        let constraint = (constraint, node.bounded_type.span.to(node.bound.span));
                        constraints.push(Spanned {
                            value: constraint.0,
                            span: constraint.1,
                        });
                    }
                    taroc_hir::GenericRequirement::ConformanceRequirement(node) => {
                        for bound in node.bounds.iter() {
                            let ty = icx
                                .lowerer()
                                .lower_type(&node.bounded_type, &LoweringRequest::default());
                            let constraint = Constraint::Bound {
                                ty,
                                interface: icx.lowerer().lower_interface_reference(
                                    ty,
                                    &bound.path,
                                    &LoweringRequest::default(),
                                ),
                            };

                            let span = node.bounded_type.span.to(node
                                .bounds
                                .last()
                                .map(|f| f.path.path.span)
                                .unwrap_or(node.bounded_type.span));
                            constraints.push(Spanned {
                                span,
                                value: constraint,
                            });
                        }
                    }
                };
            }
        }

        if let Some(conformances) = &generics.conformance
            && matches!(
                self.context.def_kind(def_id),
                DefinitionKind::AssociatedType
            )
        {
            let cx = ItemCtx::new(self.context);
            let ty = self.context.type_of(def_id);
            for conformance in conformances.interfaces.iter() {
                let interface_ref = cx.lowerer().lower_interface_reference(
                    ty,
                    conformance,
                    &LoweringRequest::default(),
                );

                let constraint = Constraint::Bound {
                    ty,
                    interface: interface_ref,
                };

                constraints.push(Spanned::new(constraint, conformance.path.span));
            }
        }

        return constraints;
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect_implicit_extension_constraint(
        &mut self,
        ty: &taroc_hir::Type,
    ) -> Option<Vec<Spanned<Constraint<'ctx>>>> {
        // let icx = ItemCtx::new(self.context);
        // get path
        let taroc_hir::TypeKind::Path(path) = &ty.kind else {
            return None;
        };

        // get arguments
        let segment = path.segments.last().unwrap();
        let Some(arguments) = &segment.arguments else {
            return None;
        };

        // get def_id
        let Some(def_id) = self.context.ty_to_def(self.context.type_of_node(ty.id)) else {
            return None;
        };

        let generics = self.context.generics_of(def_id);
        let mut constraints = vec![];

        for (index, parameter) in generics.parameters.iter().enumerate() {
            let argument = &arguments.arguments.get(index);
            let Some(argument) = argument else {
                break;
            };

            match (&parameter.kind, argument) {
                (
                    crate::ty::GenericParameterDefinitionKind::Type { .. },
                    taroc_hir::TypeArgument::Type(ty),
                ) => {
                    let param_ty = self.context.type_of(parameter.id);
                    let arg_ty = self.context.type_of_node(ty.id);

                    if arg_ty == param_ty {
                        continue;
                    }

                    let constraint = Constraint::TypeEquality(arg_ty, param_ty);
                    constraints.push(Spanned {
                        span: ty.span,
                        value: constraint,
                    });
                }
                (
                    crate::ty::GenericParameterDefinitionKind::Const { .. },
                    taroc_hir::TypeArgument::Const(_),
                ) => todo!(),
                _ => {
                    unreachable!("mismatched arguments")
                }
            }
        }

        Some(constraints)
    }
}
