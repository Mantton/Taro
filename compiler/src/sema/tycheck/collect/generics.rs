use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{
        self, AssociatedDeclarationKind, DeclarationKind, DefinitionID, DefinitionKind, HirVisitor,
        TypeParameterKind,
    },
    sema::models::{
        GenericParameter, GenericParameterDefinition, GenericParameterDefinitionKind, Generics, Ty,
        TyKind,
    },
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

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        let id = node.id;

        match &node.kind {
            DeclarationKind::Interface(node) => self.collect(id, &node.generics),
            DeclarationKind::Struct(node) => self.collect(id, &node.generics),
            DeclarationKind::Enum(node) => self.collect(id, &node.generics),
            DeclarationKind::TypeAlias(node) => self.collect(id, &node.generics),
            DeclarationKind::Function(node) => self.collect(id, &node.generics),
            DeclarationKind::Impl(node) => self.collect(id, &node.generics),
            _ => {}
        }

        hir::walk_declaration(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        let id = node.id;

        match &node.kind {
            AssociatedDeclarationKind::Type(node) => self.collect(id, &node.generics),
            AssociatedDeclarationKind::Function(node) => self.collect(id, &node.generics),
            _ => {}
        }

        hir::walk_assoc_declaration(self, node, context)
    }

    fn visit_variant(&mut self, node: &hir::Variant) -> Self::Result {
        let gcx = self.context;
        let ctor_id = node.ctor_def_id;
        let parent = gcx
            .definition_parent(ctor_id)
            .expect("CTOR Parent Definition");

        let parent = if let DefinitionKind::Variant = gcx.definition_kind(parent) {
            gcx.definition_parent(parent)
                .expect("Variant Parent Definition")
        } else {
            parent
        };

        debug_assert!(
            matches!(gcx.definition_kind(parent), DefinitionKind::Enum),
            "parent of variant must be an enum definition"
        );

        let parent_generics = gcx.generics_of(parent);
        gcx.cache_generics(ctor_id, parent_generics.clone());
    }
}

impl<'ctx> Actor<'ctx> {
    fn collect(&mut self, id: DefinitionID, generics: &hir::Generics) {
        let gcx = self.context;

        // Interfaces have implicit self type parameter
        let interface_self_type = if matches!(gcx.definition_kind(id), DefinitionKind::Interface) {
            let def = GenericParameterDefinition {
                id,
                index: 0,
                name: gcx.intern_symbol("Self"),
                kind: GenericParameterDefinitionKind::Type { default: None },
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
        let def_kind = gcx.definition_kind(id);
        let parent_def_id = if let DefinitionKind::AssociatedFunction
        | DefinitionKind::AssociatedOperator
        | DefinitionKind::AssociatedConstant
        | DefinitionKind::VariantConstructor(..) = def_kind
        {
            Some(gcx.definition_parent(id).expect("Parent of Definition"))
        } else {
            None
        };

        let parent_count = parent_def_id.map_or(0, |parent_id| {
            let parent_generics = gcx.generics_of(parent_id);
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
                let id = param.id;
                let name = param.identifier.symbol.clone();
                let index = start + index;
                // Definition
                let def = GenericParameterDefinition {
                    name: name.clone(),
                    id,
                    index,
                    kind: match &param.kind {
                        TypeParameterKind::Type { default } => {
                            GenericParameterDefinitionKind::Type {
                                default: default.clone(),
                            }
                        }
                        TypeParameterKind::Constant { default, ty } => {
                            GenericParameterDefinitionKind::Const {
                                ty: ty.clone(),
                                default: default.clone(),
                            }
                        }
                    },
                };
                parameters.push(def);

                // Type
                let kind = TyKind::Parameter(GenericParameter { index, name });
                let ty = Ty::new(kind, gcx);
                gcx.cache_type(id, ty);
            }
        }

        // Result
        let generics = Generics {
            parent: parent_def_id,
            parameters,
            has_self: has_self || parent_has_self,
            parent_count,
        };
        gcx.cache_generics(id, generics);
    }
}
