use crate::{models::SubstitutionMap, utils};
use taroc_context::GlobalContext;
use taroc_hir::{DefinitionID, DefinitionKind, NodeID, Resolution};
use taroc_ty::{GenericArgument, Ty, TyKind};

pub fn lower_type<'ctx>(ty: &taroc_hir::Type, context: GlobalContext<'ctx>) -> taroc_ty::Ty<'ctx> {
    let actor = TypeLowerer {
        context,
        substitutions: SubstitutionMap::new(),
    };
    actor.lower(ty)
}

pub fn lower_type_with_base<'ctx>(
    ty: &taroc_hir::Type,
    context: GlobalContext<'ctx>,
    substitutions: SubstitutionMap<'ctx>,
) -> taroc_ty::Ty<'ctx> {
    let actor = TypeLowerer {
        context,
        substitutions,
    };
    actor.lower(ty)
}

struct TypeLowerer<'ctx> {
    context: GlobalContext<'ctx>,
    substitutions: SubstitutionMap<'ctx>,
}

impl<'ctx> TypeLowerer<'ctx> {
    pub fn mk(&mut self, k: TyKind<'ctx>) -> Ty<'ctx> {
        self.context.store.interners.intern_ty(k)
    }

    fn lower_nested(&self, ty: &taroc_hir::Type) -> Ty<'ctx> {
        lower_type_with_base(ty, self.context, self.substitutions.clone())
    }

    pub fn lower(mut self, ty: &taroc_hir::Type) -> Ty<'ctx> {
        let ty = match &ty.kind {
            taroc_hir::TypeKind::Tuple(items) => {
                let items: Vec<Ty<'ctx>> = items.iter().map(|ty| self.lower_nested(ty)).collect();
                let items = self.context.store.interners.intern_ty_list(&items);
                self.mk(TyKind::Tuple(items))
            }
            taroc_hir::TypeKind::Path(path) => self.lower_unchecked_path(path, ty.id),
            taroc_hir::TypeKind::Function {
                inputs,
                output,
                is_async,
            } => {
                let inputs: Vec<Ty<'ctx>> = inputs.iter().map(|ty| self.lower_nested(ty)).collect();
                let inputs = self.context.store.interners.intern_ty_list(&inputs);

                let kind = TyKind::Function {
                    inputs,
                    output: self.lower_nested(output),
                    is_async: *is_async,
                };
                self.mk(kind)
            }
            taroc_hir::TypeKind::Variadic(ty) => {
                let ty = self.lower_nested(ty);
                let kind = TyKind::Variadic(ty);
                self.mk(kind)
            }

            taroc_hir::TypeKind::Opaque(..) => todo!(),
            taroc_hir::TypeKind::Exisitential(..) => todo!(),
            taroc_hir::TypeKind::Infer => todo!("infer"),
        };
        ty
    }
}

impl<'ctx> TypeLowerer<'ctx> {
    fn lower_unchecked_path(&mut self, path: &taroc_hir::Path, id: NodeID) -> Ty<'ctx> {
        self.lower_path(id, path)
    }

    fn lower_path(&mut self, _id: NodeID, path: &taroc_hir::Path) -> Ty<'ctx> {
        debug_assert!(!path.segments.is_empty(), "empty path");

        for (index, segment) in path.segments.iter().enumerate() {
            // self.context
            //     .diagnostics
            //     .info("Lowering".into(), segment.identifier.span);
            let res = self.context.resolution(segment.id);
            let ty = self.lower_path_segment(segment, res);

            if ty == self.context.store.common_types.error {
                return ty;
            }

            if index == path.segments.len() - 1 {
                return ty;
            }
        }

        return self.context.store.common_types.error;
    }

    fn lower_path_segment(
        &mut self,
        segment: &taroc_hir::PathSegment,
        res: Resolution,
    ) -> Ty<'ctx> {
        match res {
            Resolution::Definition(def_id, DefinitionKind::Enum | DefinitionKind::Struct) => {
                self.lower_path_segment_with_definition(segment, def_id)
            }
            Resolution::Definition(def_id, DefinitionKind::TypeAlias) => {
                self.lower_alias(segment, def_id)
            }
            Resolution::Definition(def_id, DefinitionKind::TypeParameter) => {
                self.lower_type_parameter(segment, def_id)
            }
            Resolution::Definition(_, DefinitionKind::Interface) => {
                // TODO!!
                todo!()
            }
            Resolution::InterfaceSelfTypeAlias(..) => {
                self.context.store.common_types.self_type_parameter
            }
            Resolution::Definition(id, DefinitionKind::AssociatedType) => self
                .context
                .store
                .interners
                .intern_ty(TyKind::AssociatedType(id)),
            Resolution::Definition(
                _,
                DefinitionKind::Namespace | DefinitionKind::Module | DefinitionKind::Bridged,
            ) => self.context.store.common_types.ignore,

            Resolution::SelfTypeAlias(definition_id) => self.context.type_of(definition_id),
            Resolution::FunctionSet(..) => {
                unreachable!("cannot resolve type to set of functions")
            }
            Resolution::Local(..) => unreachable!("cannot resolve type to local variable"),
            Resolution::Error => {
                unreachable!("prereported resolution error, this compiler pass should not happen")
            }
            _ => {
                println!("{:?}", res);
                todo!("implement!")
            }
        }
    }

    fn lower_path_segment_with_definition(
        &mut self,
        segment: &taroc_hir::PathSegment,
        def_id: DefinitionID,
    ) -> Ty<'ctx> {
        let context = self.context;
        let generics = self.context.generics_of(def_id);
        let arguments = self.lower_type_arguments(def_id, &generics, segment);
        let Some(arguments) = arguments else {
            return self.context.store.common_types.error;
        };

        let ty = context.type_of(def_id);
        let substitutions = utils::create_substitution_map(def_id, arguments, context);
        self.substitutions.extend(substitutions);

        // Instantiated Ty
        let ty = utils::substitute(ty, &self.substitutions, None, context);
        ty
    }

    fn lower_alias(&mut self, segment: &taroc_hir::PathSegment, def_id: DefinitionID) -> Ty<'ctx> {
        // Resolve Alias Generics
        let generics = self.context.generics_of(def_id);
        let arguments = self.lower_type_arguments(def_id, &generics, segment);
        let Some(arguments) = arguments else {
            return self.context.store.common_types.error;
        };
        let substitutions = utils::create_substitution_map(def_id, arguments, self.context);
        self.substitutions.extend(substitutions);
        // Get RHS
        let normalized = self.context.alias_resolution(def_id);
        let ty = self.lower_nested(&normalized.ty);
        let ty = utils::substitute(ty, &self.substitutions, None, self.context);
        // self.context
        //     .diagnostics
        //     .warn("Here".into(), segment.identifier.span);
        // println!("{:?}", ty);
        return ty;
    }
    fn lower_type_parameter(
        &mut self,
        segment: &taroc_hir::PathSegment,
        def_id: DefinitionID,
    ) -> Ty<'ctx> {
        let generics = self.context.generics_of(def_id);
        let arguments = self.lower_type_arguments(def_id, &generics, segment);
        if arguments.is_none() {
            return self.context.store.common_types.error;
        };

        self.context.type_of(def_id)
    }

    fn lower_type_arguments(
        &mut self,
        def_id: DefinitionID,
        generics: &taroc_ty::Generics,
        segment: &taroc_hir::PathSegment,
    ) -> Option<taroc_ty::GenericArguments<'ctx>> {
        let arguments = if let Some(arguments) = &segment.arguments {
            arguments
        } else {
            &taroc_hir::TypeArguments {
                span: segment.identifier.span,
                arguments: Default::default(),
            }
        };
        let mut ok = check_generics_prohibited(def_id, &generics, &arguments, self.context);
        if !ok {
            return None;
        }

        ok = check_generic_arg_count(&generics, segment, self.context);
        if !ok {
            return None;
        }

        let arguments = self.lower_generic_args(arguments);
        let arguments = self.context.store.interners.intern_generic_args(&arguments);
        return Some(arguments);
    }

    fn lower_generic_args(
        &mut self,
        arguments: &taroc_hir::TypeArguments,
    ) -> Vec<GenericArgument<'ctx>> {
        let mut output = vec![];

        for argument in &arguments.arguments {
            match argument {
                taroc_hir::TypeArgument::Type(ty) => {
                    let ty = self.lower_nested(ty);
                    output.push(GenericArgument::Type(ty));
                }
                taroc_hir::TypeArgument::Const(_) => todo!(),
            }
        }
        return output;
    }
}

fn check_generics_prohibited(
    def_id: DefinitionID,
    _: &taroc_ty::Generics,
    arguments: &taroc_hir::TypeArguments,
    context: GlobalContext<'_>,
) -> bool {
    let kind = context.def_kind(def_id);

    // No type arguments => always OK
    if arguments.arguments.is_empty() {
        return true;
    }

    // Only these kinds allow generics
    let allowed = matches!(
        kind,
        DefinitionKind::Struct
            | DefinitionKind::Enum
            | DefinitionKind::Interface
            | DefinitionKind::TypeAlias
    );

    if !allowed {
        context.diagnostics.error(
            format!("Generics not permitted on {:?}", kind),
            arguments.span,
        );
        return false;
    }

    true
}

pub fn check_generic_arg_count(
    generics: &taroc_ty::Generics,
    segment: &taroc_hir::PathSegment,
    context: GlobalContext<'_>,
) -> bool {
    let defaults_count = generics.default_count();
    let total_count = generics.total_count();

    let min = total_count - defaults_count - generics.has_self as usize;
    let provided = segment
        .arguments
        .as_ref()
        .map(|v| v.arguments.len())
        .unwrap_or(0);

    if (min..=total_count).contains(&provided) {
        return true;
    }

    if provided > total_count {
        let message = format!(
            "excess generic arguments, '{}' requires {} type argument(s), provided {}",
            segment.identifier.symbol, min, provided
        );
        context
            .diagnostics
            .error(message, segment.arguments.as_ref().map(|v| v.span).unwrap());
    } else {
        context
            .diagnostics
            .error("Missing Generic Arguments".into(), segment.identifier.span);
    }

    return false;
}
