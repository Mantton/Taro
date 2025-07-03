use crate::GlobalContext;
use crate::ty::{GenericParameter, TyKind};
use taroc_error::CompileResult;
use taroc_hir::DefinitionKind;
use taroc_hir::{NodeID, visitor::HirVisitor};
use taroc_span::Symbol;

/// Collect & Cache Generics Information for a Definition
pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    pass: u8,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context, pass: 0 }
    }

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package); // Collect Top Level
        actor.pass = 1;
        taroc_hir::visitor::walk_package(&mut actor, package); // Collect Extensions
        context.diagnostics.report()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, d: &taroc_hir::Declaration) -> Self::Result {
        let id = d.id;

        // Intial Pass, Collect Top Level
        if self.pass == 0 {
            match &d.kind {
                taroc_hir::DeclarationKind::Interface(node) => self.collect(id, &node.generics),
                taroc_hir::DeclarationKind::Struct(node) => self.collect(id, &node.generics),
                taroc_hir::DeclarationKind::Enum(node) => self.collect(id, &node.generics),
                taroc_hir::DeclarationKind::Function(node) => self.collect(id, &node.generics),
                taroc_hir::DeclarationKind::TypeAlias(node) => self.collect(id, &node.generics),
                taroc_hir::DeclarationKind::Extend(_) => return,
                _ => {}
            }
        } else {
            // Extension Pass
            match &d.kind {
                taroc_hir::DeclarationKind::Extend(node) => self.collect(id, &node.generics),
                _ => return,
            }
        }

        taroc_hir::visitor::walk_declaration(self, d);
    }

    fn visit_function_declaration(&mut self, d: &taroc_hir::FunctionDeclaration) -> Self::Result {
        if self.pass == 1 {
            return;
        }
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
        let gcx = self.context;
        let def_id = gcx.def_id(id);

        // Extensions Share Generics of their Self Types
        if let DefinitionKind::Extension = gcx.def_kind(def_id) {
            let alias = gcx.extension_self_alias(def_id);
            let id = match alias {
                taroc_hir::SelfTypeAlias::Def(definition_id) => Some(definition_id),
                taroc_hir::SelfTypeAlias::Primary(_) => None,
            };

            let Some(id) = id else { return };
            let self_ty_generics = gcx.generics_of(id);

            gcx.cache_generics(def_id, self_ty_generics.clone());
            return;
        }

        // Interfaces have implicit self type parameter
        let interface_self_type =
            if matches!(gcx.def_kind(def_id), taroc_hir::DefinitionKind::Interface) {
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

        let mut own_start = has_self as usize;
        let mut parent_has_self = false;
        let parent_def_id = if let DefinitionKind::AssociatedFunction
        | DefinitionKind::AssociatedOperator = gcx.def_kind(def_id)
        {
            Some(gcx.parent(def_id))
        } else {
            None
        };

        let parent_count = parent_def_id.map_or(0, |id| {
            let parent_generics = gcx.generics_of(id);
            assert!(!(has_self && parent_generics.has_self)); // Parent and Def cannot both have self param
            parent_has_self = parent_generics.has_self;
            own_start = parent_generics.total_count();
            parent_generics.parent_count + parent_generics.total_count()
        });

        let mut parameters = Vec::with_capacity(parameters_len + (has_self as usize));
        if let Some(s) = interface_self_type {
            parameters.push(s);
        };

        let start = own_start - has_self as usize + parameters.len();

        // Parameters
        let hir_parameters = generics.type_parameters.as_ref().map(|f| &f.parameters);
        if let Some(hir_parameters) = hir_parameters {
            for (index, param) in hir_parameters.iter().enumerate() {
                let id = gcx.def_id(param.id);
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
                let ty = gcx.mk_ty(kind);
                gcx.cache_type(id, ty);
            }
        }

        // Result
        let generics = crate::ty::Generics {
            parent: parent_def_id,
            parameters,
            has_self: has_self || parent_has_self,
            parent_count,
        };
        gcx.cache_generics(def_id, generics);
    }
}
