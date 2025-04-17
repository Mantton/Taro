use super::package::Actor;

impl Actor<'_> {
    pub fn lower_generics(&mut self, g: taroc_ast::Generics) -> taroc_hir::Generics {
        taroc_hir::Generics {
            type_parameters: self
                .lower_optional(g.type_parameters, |a, v| a.lower_type_parameters(v)),
            where_clause: self
                .lower_optional(g.where_clause, |a, v| a.lower_generic_where_clause(v)),
            inheritance: self.lower_optional(g.inheritance, |a, v| a.lower_inheritance(v)),
        }
    }

    pub fn lower_type_parameters(
        &mut self,
        tp: taroc_ast::TypeParameters,
    ) -> taroc_hir::TypeParameters {
        taroc_hir::TypeParameters {
            span: tp.span,
            parameters: self.lower_sequence(tp.parameters, |a, v| a.lower_type_parameter(v)),
        }
    }

    pub fn lower_type_parameter(
        &mut self,
        tp: taroc_ast::TypeParameter,
    ) -> taroc_hir::TypeParameter {
        taroc_hir::TypeParameter {
            id: self.next(),
            span: tp.span,
            identifier: tp.identifier.clone(),
            bounds: self.lower_optional(tp.bounds, |a1, bounds| a1.lower_generic_bounds(bounds)),
            kind: self.lower_type_parameter_kind(tp.kind),
        }
    }

    pub fn lower_type_parameter_kind(
        &mut self,
        kind: taroc_ast::TypeParameterKind,
    ) -> taroc_hir::TypeParameterKind {
        match kind {
            taroc_ast::TypeParameterKind::Type { default } => taroc_hir::TypeParameterKind::Type {
                default: self.lower_optional(default, |a, v| a.lower_type(v)),
            },
            taroc_ast::TypeParameterKind::Constant { ty, default } => {
                taroc_hir::TypeParameterKind::Constant {
                    ty: self.lower_type(ty),
                    default: self.lower_optional(default, |a, v| a.lower_anon_const(v)),
                }
            }
        }
    }

    pub fn lower_type_arguments(
        &mut self,
        arg: taroc_ast::TypeArguments,
    ) -> taroc_hir::TypeArguments {
        taroc_hir::TypeArguments {
            span: arg.span,
            arguments: self.lower_sequence(arg.arguments, |a, arg| a.lower_type_argument(arg)),
        }
    }

    pub fn lower_type_argument(&mut self, arg: taroc_ast::TypeArgument) -> taroc_hir::TypeArgument {
        match arg {
            taroc_ast::TypeArgument::Type(ty) => taroc_hir::TypeArgument::Type(self.lower_type(ty)),
            taroc_ast::TypeArgument::Const(anon_const) => {
                taroc_hir::TypeArgument::Const(self.lower_anon_const(anon_const))
            }
        }
    }

    pub fn lower_generic_bounds(
        &mut self,
        bounds: taroc_ast::GenericBounds,
    ) -> taroc_hir::GenericBounds {
        self.lower_sequence(bounds, |a, bound| a.lower_generic_bound(bound))
    }

    fn lower_generic_bound(&mut self, bound: taroc_ast::GenericBound) -> taroc_hir::GenericBound {
        taroc_hir::GenericBound {
            path: self.lower_tagged_path(bound.path),
        }
    }

    pub fn lower_generic_where_clause(
        &mut self,
        bound: taroc_ast::GenericWhereClause,
    ) -> taroc_hir::GenericWhereClause {
        taroc_hir::GenericWhereClause {
            requirements: self.lower_generic_requirements(bound.requirements),
            span: bound.span,
        }
    }

    fn lower_generic_requirements(
        &mut self,
        requirements: taroc_ast::GenericRequirementList,
    ) -> taroc_hir::GenericRequirementList {
        self.lower_sequence(requirements, |a, req| a.lower_generic_requirement(req))
    }

    fn lower_generic_requirement(
        &mut self,
        requirement: taroc_ast::GenericRequirement,
    ) -> taroc_hir::GenericRequirement {
        match requirement {
            taroc_ast::GenericRequirement::SameTypeRequirement(c) => {
                taroc_hir::GenericRequirement::SameTypeRequirement(
                    taroc_hir::RequiredTypeConstraint {
                        bounded_type: self.lower_tagged_path(c.bounded_type),
                        bound: self.lower_type(c.bound),
                        span: c.span,
                    },
                )
            }
            taroc_ast::GenericRequirement::ConformanceRequirement(c) => {
                taroc_hir::GenericRequirement::ConformanceRequirement(
                    taroc_hir::ConformanceConstraint {
                        bounded_type: self.lower_tagged_path(c.bounded_type),
                        bounds: self.lower_generic_bounds(c.bounds),
                        span: c.span,
                    },
                )
            }
        }
    }

    fn lower_inheritance(&mut self, inheritance: taroc_ast::Inheritance) -> taroc_hir::Inheritance {
        taroc_hir::Inheritance {
            interfaces: self.lower_sequence(inheritance.interfaces, |a, v| a.lower_tagged_path(v)),
        }
    }
}
