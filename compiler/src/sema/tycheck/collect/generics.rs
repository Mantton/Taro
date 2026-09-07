use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{
        self, AssociatedDeclarationKind, DeclarationKind, DefinitionID, DefinitionKind, HirVisitor,
        TypeParameterKind,
    },
    sema::models::{
        Constraint, GenericArgument, GenericParameter, GenericParameterDefinition,
        GenericParameterDefinitionKind, Generics, InterfaceReference, Ty, TyKind,
    },
    sema::tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    tuple_bounds: TupleBounds,
}

impl<'ctx> Actor<'ctx> {
    fn run(package: &hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut tuple_bounds = TupleBounds::default();
        hir::walk_package(&mut tuple_bounds, package);
        let mut actor = Actor {
            context,
            tuple_bounds,
        };
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
    fn cache_lowered_generic_metadata(&self, owner: DefinitionID) {
        let gcx = self.context;
        let params = gcx.generics_of(owner).parameters.clone();
        let lowering_ctx = DefTyLoweringCtx::new(owner, gcx);
        let lowerer: &dyn TypeLowerer<'ctx> = &lowering_ctx;

        for param in &params {
            match &param.kind {
                GenericParameterDefinitionKind::Type { default } => {
                    let Some(default) = default.as_ref() else {
                        continue;
                    };
                    if gcx.try_generic_type_default(param.id).is_none() {
                        let ty = lowerer.lower_type(default);
                        gcx.cache_generic_type_default(param.id, ty);
                    }
                }
                GenericParameterDefinitionKind::Const { ty, default } => {
                    if gcx.try_generic_const_param_ty(param.id).is_none() {
                        let lowered = lowerer.lower_type(ty);
                        gcx.cache_generic_const_param_ty(param.id, lowered);
                    }

                    let Some(default) = default.as_ref() else {
                        continue;
                    };

                    if gcx.try_generic_const_default(param.id).is_none() {
                        let expected_ty = gcx
                            .try_generic_const_param_ty(param.id)
                            .unwrap_or_else(|| lowerer.lower_type(ty));
                        let value = lowerer.lower_const_argument(expected_ty, default);
                        gcx.cache_generic_const_default(param.id, value);
                    }
                }
            }
        }
    }

    /// Argument-pack bounds must be visible before interface superfaces and
    /// generic defaults are lowered. Store them in the ordinary constraint map;
    /// the full constraint collector will retain and deduplicate these bounds.
    fn seed_tuple_bounds(&self, owner: DefinitionID, generics: &hir::Generics) {
        let gcx = self.context;
        let Some(tuple_id) = gcx.std_item_def(hir::StdItem::Tuple) else {
            return;
        };
        let mut constraints = Vec::new();
        let mut add = |ty: Ty<'ctx>, bounds: &hir::GenericBounds| {
            for bound in bounds {
                let Some(id) = TupleBounds::target(&bound.path.path) else {
                    continue;
                };
                if !self
                    .tuple_bounds
                    .implies_tuple(gcx, id, tuple_id, &mut FxHashSet::default())
                {
                    continue;
                }
                constraints.push(crate::span::Spanned::new(
                    Constraint::Bound {
                        ty,
                        interface: InterfaceReference {
                            id: tuple_id,
                            arguments: gcx
                                .store
                                .interners
                                .intern_generic_args(vec![GenericArgument::Type(ty)]),
                            bindings: &[],
                        },
                    },
                    bound.path.span,
                ));
            }
        };
        if let Some(parameters) = &generics.type_parameters {
            for param in &parameters.parameters {
                if let Some(bounds) = &param.bounds {
                    add(gcx.get_type(param.id), bounds);
                }
            }
        }
        if let Some(clause) = &generics.where_clause {
            for requirement in &clause.requirements {
                let hir::GenericRequirement::ConformanceRequirement(requirement) = requirement
                else {
                    continue;
                };
                let hir::TypeKind::Nominal(hir::ResolvedPath::Resolved(path)) =
                    &requirement.bounded_type.kind
                else {
                    continue;
                };
                if let hir::Resolution::Definition(id, DefinitionKind::TypeParameter) =
                    path.resolution
                {
                    add(gcx.get_type(id), &requirement.bounds);
                }
            }
        }
        gcx.update_constraints(owner, constraints);
    }

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
                let name = param.identifier.symbol;
                let index = start + index;
                // Definition
                let def = GenericParameterDefinition {
                    name: name,
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
        let lowered_generics = Generics {
            parent: parent_def_id,
            parameters,
            has_self: has_self || parent_has_self,
            parent_count,
        };
        gcx.cache_generics(id, lowered_generics);
        self.seed_tuple_bounds(id, generics);
        self.cache_lowered_generic_metadata(id);
    }
}

/// Read only the nominal header graph so tuple-pack bounds are independent of
/// declaration order. Generic arguments do not affect marker implication. The
/// normal interface collector remains responsible for lowering and validation.
#[derive(Default)]
struct TupleBounds(FxHashMap<DefinitionID, Vec<DefinitionID>>);

impl TupleBounds {
    fn target(path: &hir::ResolvedPath) -> Option<DefinitionID> {
        let hir::ResolvedPath::Resolved(path) = path else {
            return None;
        };
        match path.resolution {
            hir::Resolution::Definition(
                id,
                DefinitionKind::Interface | DefinitionKind::TypeAlias,
            ) => Some(id),
            _ => None,
        }
    }

    fn implies_tuple(
        &self,
        gcx: GlobalContext<'_>,
        id: DefinitionID,
        tuple_id: DefinitionID,
        visited: &mut FxHashSet<DefinitionID>,
    ) -> bool {
        if id == tuple_id {
            return true;
        }
        if !visited.insert(id) {
            return false;
        }
        if let Some(parents) = self.0.get(&id) {
            return parents
                .iter()
                .any(|&parent| self.implies_tuple(gcx, parent, tuple_id, visited));
        }
        if let Some(alias) = gcx.try_get_interface_alias(id) {
            return alias
                .iter()
                .any(|parent| self.implies_tuple(gcx, parent.id, tuple_id, visited));
        }
        gcx.get_interface_definition(id).is_some_and(|definition| {
            definition
                .superfaces
                .iter()
                .any(|parent| self.implies_tuple(gcx, parent.value.id, tuple_id, visited))
        })
    }
}

impl HirVisitor for TupleBounds {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        let parents = match &node.kind {
            DeclarationKind::Interface(interface) => {
                interface.conformances.as_ref().map(|conformances| {
                    conformances
                        .bounds
                        .iter()
                        .filter_map(|bound| Self::target(&bound.path))
                        .collect()
                })
            }
            DeclarationKind::TypeAlias(alias) => {
                if let Some(bounds) = &alias.interface_set {
                    Some(
                        bounds
                            .iter()
                            .filter_map(|bound| Self::target(&bound.path.path))
                            .collect(),
                    )
                } else if let Some(ty) = &alias.ty
                    && let hir::TypeKind::Nominal(path) = &ty.kind
                {
                    Some(Self::target(path).into_iter().collect())
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(parents) = parents {
            self.0.insert(node.id, parents);
        }
        hir::walk_declaration(self, node)
    }
}
