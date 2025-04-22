use crate::{
    models::{InferenceContext, SubstitutionMap},
    utils,
};
use taroc_context::GlobalContext;
use taroc_hir::{DefinitionID, DefinitionKind, NodeID, Resolution, TaggedPath};
use taroc_ty::{GenericArgument, InterfaceReference, Ty, TyKind};

pub fn lower_type<'ctx>(
    ty: &taroc_hir::Type,
    context: &mut InferenceContext<'ctx>,
) -> taroc_ty::Ty<'ctx> {
    let actor = TypeLowerer {
        context,
        substitutions: SubstitutionMap::new(),
    };
    actor.lower(ty)
}

pub fn lower_type_with_base<'ctx>(
    ty: &taroc_hir::Type,
    substitutions: SubstitutionMap<'ctx>,
    context: &mut InferenceContext<'ctx>,
) -> taroc_ty::Ty<'ctx> {
    let actor = TypeLowerer {
        context,
        substitutions,
    };
    actor.lower(ty)
}

struct TypeLowerer<'ctx, 'icx> {
    context: &'icx mut InferenceContext<'ctx>,
    substitutions: SubstitutionMap<'ctx>,
}

impl<'ctx, 'icx> TypeLowerer<'ctx, 'icx> {
    pub fn mk(&mut self, k: TyKind<'ctx>) -> Ty<'ctx> {
        self.context.context.store.interners.intern_ty(k)
    }

    fn lower_nested(&mut self, ty: &taroc_hir::Type) -> Ty<'ctx> {
        lower_type_with_base(ty, self.substitutions.clone(), self.context)
    }

    pub fn lower(mut self, ty: &taroc_hir::Type) -> Ty<'ctx> {
        let ty = match &ty.kind {
            taroc_hir::TypeKind::Tuple(items) => {
                let items: Vec<Ty<'ctx>> = items.iter().map(|ty| self.lower_nested(ty)).collect();
                let items = self.context.context.store.interners.intern_ty_list(&items);
                self.mk(TyKind::Tuple(items))
            }
            taroc_hir::TypeKind::Path(path) => self.lower_unchecked_path(path, ty.id),
            taroc_hir::TypeKind::Function {
                inputs,
                output,
                is_async,
            } => {
                let inputs: Vec<Ty<'ctx>> = inputs.iter().map(|ty| self.lower_nested(ty)).collect();
                let inputs = self.context.context.store.interners.intern_ty_list(&inputs);

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

impl<'ctx, 'icx> TypeLowerer<'ctx, 'icx> {
    fn lower_unchecked_path(&mut self, path: &taroc_hir::Path, id: NodeID) -> Ty<'ctx> {
        self.lower_path(id, path)
    }

    fn lower_path(&mut self, _id: NodeID, path: &taroc_hir::Path) -> Ty<'ctx> {
        debug_assert!(!path.segments.is_empty(), "empty path");

        for (index, segment) in path.segments.iter().enumerate() {
            // self.context
            //     .diagnostics
            //     .info("Lowering".into(), segment.identifier.span);
            let res = self.context.context.resolution(segment.id);
            let ty = self.lower_path_segment(segment, res);

            if ty == self.context.context.store.common_types.error {
                return ty;
            }

            if index == path.segments.len() - 1 {
                return ty;
            }
        }

        return self.context.context.store.common_types.error;
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
                self.context.context.store.common_types.self_type_parameter
            }
            Resolution::Definition(id, DefinitionKind::AssociatedType) => self
                .context
                .context
                .store
                .interners
                .intern_ty(TyKind::AssociatedType(id)),
            Resolution::Definition(
                _,
                DefinitionKind::Namespace | DefinitionKind::Module | DefinitionKind::Bridged,
            ) => self.context.context.store.common_types.ignore,

            Resolution::SelfTypeAlias(definition_id) => self.context.context.type_of(definition_id),
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
        // Lower Type Arguments
        let generics = self.context.context.generics_of(def_id);
        let arguments = self.lower_type_arguments(def_id, &generics, segment);
        let Some(arguments) = arguments else {
            return self.context.context.store.common_types.error;
        };

        // Duplicate Constraints
        self.context
            .instantiate_definition_constraints(def_id, arguments);

        // Build / Extend Subst Map
        let substitutions = utils::create_substitution_map(def_id, arguments, self.context.context);
        self.substitutions.extend(substitutions);

        // Instantiated Ty
        let ty = self.context.context.type_of(def_id);
        let ty = utils::substitute(ty, &self.substitutions, None, self.context.context);
        ty
    }

    fn lower_alias(&mut self, segment: &taroc_hir::PathSegment, def_id: DefinitionID) -> Ty<'ctx> {
        // Resolve Alias Generics
        let generics = self.context.context.generics_of(def_id);
        let arguments = self.lower_type_arguments(def_id, &generics, segment);
        let Some(arguments) = arguments else {
            return self.context.context.store.common_types.error;
        };

        // Constraints
        self.context
            .instantiate_definition_constraints(def_id, arguments);

        let substitutions = utils::create_substitution_map(def_id, arguments, self.context.context);
        self.substitutions.extend(substitutions);
        // Get RHS
        let normalized = self.context.context.alias_resolution(def_id);
        let ty = self.lower_nested(&normalized.ty);
        let ty = utils::substitute(ty, &self.substitutions, None, self.context.context);
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
        let generics = self.context.context.generics_of(def_id);
        let arguments = self.lower_type_arguments(def_id, &generics, segment);
        if arguments.is_none() {
            return self.context.context.store.common_types.error;
        };

        self.context.context.type_of(def_id)
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
        let mut ok = check_generics_prohibited(def_id, &generics, &arguments, self.context.context);
        if !ok {
            return None;
        }

        ok = check_generic_arg_count(&generics, segment, self.context.context);
        if !ok {
            return None;
        }

        let arguments = self.lower_generic_args(arguments, generics);
        let arguments = self
            .context
            .context
            .store
            .interners
            .intern_generic_args(&arguments);
        return Some(arguments);
    }

    fn lower_generic_args(
        &mut self,
        arguments: &taroc_hir::TypeArguments,
        generics: &taroc_ty::Generics,
    ) -> Vec<GenericArgument<'ctx>> {
        let mut output = vec![];
        for (index, parameter) in generics.parameters.iter().enumerate() {
            let argument = arguments.arguments.get(index);
            let argument = match argument {
                Some(argument) => match argument {
                    taroc_hir::TypeArgument::Type(ty) => {
                        let ty = self.lower_nested(ty);
                        GenericArgument::Type(ty)
                    }
                    taroc_hir::TypeArgument::Const(_) => todo!(),
                },
                None => match &parameter.kind {
                    taroc_ty::GenericParameterDefinitionKind::Type { default } => {
                        let Some(default) = default else {
                            unreachable!(
                                "ICE: default type validation is linked to the generic argument count, this must be checked prior"
                            )
                        };

                        let ty = self.lower_nested(default);
                        GenericArgument::Type(ty)
                    }
                    taroc_ty::GenericParameterDefinitionKind::Const { .. } => todo!(),
                },
            };
            output.push(argument);
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

pub fn lower_interface_reference<'ctx>(
    def_id: DefinitionID,
    node: &TaggedPath,
    context: GlobalContext<'ctx>,
) -> InterfaceReference<'ctx> {
    let resolution = context.resolution(node.id);
    let interface_id = match resolution {
        taroc_hir::Resolution::Definition(id, taroc_hir::DefinitionKind::Interface) => id,
        _ => unreachable!("resolver must validate provided paths are interfaces"),
    };

    let arguments = node
        .path
        .segments
        .last()
        .map(|f| f.arguments.as_ref())
        .flatten();

    let generics = context.generics_of(interface_id);
    check_generic_arg_count(&generics, node.path.segments.last().unwrap(), context);

    let mut result = vec![];
    let mut icx = InferenceContext::new(context);

    for (index, parameter) in generics.parameters.iter().enumerate() {
        if index == 0 && generics.has_self {
            let self_ty = context.type_of(def_id);
            result.push(GenericArgument::Type(self_ty));
            continue;
        }

        if let Some(arguments) = arguments
            && let Some(argument) = arguments
                .arguments
                .get(parameter.index - generics.has_self as usize)
        {
            match argument {
                taroc_hir::TypeArgument::Type(ty) => {
                    let ty = lower_type(ty, &mut icx);
                    result.push(GenericArgument::Type(ty));
                    continue;
                }
                taroc_hir::TypeArgument::Const(_) => todo!(),
            }
        } else {
            // Get Default Argument
            match &parameter.kind {
                taroc_ty::GenericParameterDefinitionKind::Type { default } => {
                    let ty = if let Some(default) = default {
                        lower_type(default, &mut icx)
                    } else {
                        context
                            .diagnostics
                            .warn("Defaulting To Err".into(), node.path.span);
                        context.store.common_types.error
                    };

                    result.push(GenericArgument::Type(ty));
                    continue;
                }
                taroc_ty::GenericParameterDefinitionKind::Const { .. } => {
                    todo!()
                }
            }
        };
    }

    let reference = InterfaceReference {
        id: interface_id,
        arguments: context.store.interners.mk_args(result),
    };

    return reference;
}
