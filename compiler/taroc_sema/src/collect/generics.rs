use crate::GlobalContext;
use crate::ty::{GenericParameter, TyKind};
use taroc_error::CompileResult;
use taroc_hir::{NodeID, visitor::HirVisitor};
use taroc_span::Symbol;

/// Collect & Cache Generics Information for a Definition
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

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, d: &taroc_hir::Declaration) -> Self::Result {
        let id = d.id;
        match &d.kind {
            taroc_hir::DeclarationKind::Interface(node) => self.collect(id, &node.generics),
            taroc_hir::DeclarationKind::Struct(node) => self.collect(id, &node.generics),
            taroc_hir::DeclarationKind::Enum(node) => self.collect(id, &node.generics),
            taroc_hir::DeclarationKind::Function(node) => self.collect(id, &node.generics),
            taroc_hir::DeclarationKind::TypeAlias(node) => self.collect(id, &node.generics),
            taroc_hir::DeclarationKind::Extend(node) => self.collect(id, &node.generics),
            _ => {}
        }

        taroc_hir::visitor::walk_declaration(self, d);
    }

    fn visit_function_declaration(&mut self, d: &taroc_hir::FunctionDeclaration) -> Self::Result {
        let id = d.id;
        match &d.kind {
            taroc_hir::FunctionDeclarationKind::Struct(node) => self.collect(id, &node.generics),
            taroc_hir::FunctionDeclarationKind::Enum(node) => self.collect(id, &node.generics),
            taroc_hir::FunctionDeclarationKind::Function(node) => self.collect(id, &node.generics),
            taroc_hir::FunctionDeclarationKind::TypeAlias(node) => self.collect(id, &node.generics),
            _ => {}
        }

        taroc_hir::visitor::walk_function_declaration(self, d);
    }

    fn visit_assoc_declaration(
        &mut self,
        declaration: &taroc_hir::AssociatedDeclaration,
        context: taroc_hir::visitor::AssocContext,
    ) -> Self::Result {
        let id = declaration.id;

        match &declaration.kind {
            taroc_hir::AssociatedDeclarationKind::Function(node) => {
                self.collect(id, &node.generics)
            }
            taroc_hir::AssociatedDeclarationKind::Type(node) => self.collect(id, &node.generics),
            taroc_hir::AssociatedDeclarationKind::Operator(_, node) => {
                self.collect(id, &node.generics)
            }
            _ => {}
        };

        taroc_hir::visitor::walk_assoc_declaration(self, declaration, context);
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect(&mut self, id: NodeID, generics: &taroc_hir::Generics) {
        // println!(
        //     "Collect Generics For '{}'",
        //     self.context.ident_for(self.context.def_id(id)).symbol
        // );
        let def_id = self.context.def_id(id);

        // Interfaces have implicit self type parameter
        let interface_self_type = if matches!(
            self.context.def_kind(def_id),
            taroc_hir::DefinitionKind::Interface
        ) {
            let def = crate::ty::GenericParameterDefinition {
                index: 0,
                name: Symbol::with("Self"),
                id: def_id,
                kind: crate::ty::GenericParameterDefinitionKind::Type { default: None },
            };
            Some(def)
        } else {
            None
        };

        let has_self = interface_self_type.is_some();
        let parameters_len = &generics
            .type_parameters
            .as_ref()
            .map(|f| f.parameters.len())
            .unwrap_or_default();
        let mut parameters = Vec::with_capacity(parameters_len + (has_self as usize));

        let start = has_self as usize;
        if let Some(s) = interface_self_type {
            parameters.push(s);
        };

        // Parameters
        let hir_parameters = generics.type_parameters.as_ref().map(|f| &f.parameters);
        if let Some(hir_parameters) = hir_parameters {
            for (index, param) in hir_parameters.iter().enumerate() {
                let id = self.context.def_id(param.id);
                let name = param.identifier.symbol;
                let index = start + index;
                // Definition
                let def = crate::ty::GenericParameterDefinition {
                    name,
                    id,
                    index,
                    kind: match &param.kind {
                        taroc_hir::TypeParameterKind::Type { default } => {
                            crate::ty::GenericParameterDefinitionKind::Type {
                                default: default.clone(),
                            }
                        }
                        taroc_hir::TypeParameterKind::Constant { default, .. } => {
                            crate::ty::GenericParameterDefinitionKind::Const {
                                has_default: default.is_some(),
                            }
                        }
                    },
                };
                parameters.push(def);

                // Type
                let kind = TyKind::Parameter(GenericParameter { index, name });
                let ty = self.context.mk_ty(kind);
                self.context.cache_type(id, ty);
            }
        }

        // Result
        let generics = crate::ty::Generics {
            parameters,
            has_self,
        };
        self.context.cache_generics(def_id, generics);
    }
}
