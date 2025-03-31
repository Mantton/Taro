use rustc_hash::FxHashMap;
use taroc_context::GlobalContext;
use taroc_hir::{DefinitionID, DefinitionKind, NodeID, Resolution};
use taroc_ty::{GenericArgument, Ty, TyKind};

pub type SubstitutionMap<'ctx> = FxHashMap<Ty<'ctx>, GenericArgument<'ctx>>;

pub fn lower_type<'ctx>(
    ty: &taroc_hir::Type,
    context: GlobalContext<'ctx>,
    initial_subst: SubstitutionMap<'ctx>, // Pass initial substitutions from caller
) -> taroc_ty::Ty<'ctx> {
    let actor = TypeLowerer {
        context,
        active_subst: initial_subst,
    };
    actor.lower(ty)
}

struct TypeLowerer<'ctx> {
    context: GlobalContext<'ctx>,
    // The currently active substitution map, accumulates as we lower paths
    active_subst: SubstitutionMap<'ctx>,
}

impl<'ctx> TypeLowerer<'ctx> {
    pub fn lower(mut self, ty: &taroc_hir::Type) -> Ty<'ctx> {
        let mk = |k| self.context.store.interners.intern_ty(k);
        let ty = match &ty.kind {
            taroc_hir::TypeKind::Pointer(ty, mutability) => mk(TyKind::Pointer(
                lower_type(ty, self.context, self.active_subst.clone()),
                *mutability,
            )),
            taroc_hir::TypeKind::Reference(ty, mutability) => mk(TyKind::Reference(
                lower_type(ty, self.context, self.active_subst.clone()),
                *mutability,
            )),
            taroc_hir::TypeKind::Tuple(items) => {
                let items: Vec<Ty<'ctx>> = items
                    .iter()
                    .map(|ty| lower_type(ty, self.context, self.active_subst.clone()))
                    .collect();
                let items = self.context.store.interners.intern_ty_list(&items);
                mk(TyKind::Tuple(items))
            }
            taroc_hir::TypeKind::Path(path) => self.lower_unchecked_path(path, ty.id),
            taroc_hir::TypeKind::Array { element, .. } => {
                let _element = self.lower(element);
                todo!()
            }
            taroc_hir::TypeKind::Function {
                inputs,
                output,
                is_async,
            } => {
                let inputs: Vec<Ty<'ctx>> = inputs
                    .iter()
                    .map(|ty| lower_type(ty, self.context, self.active_subst.clone()))
                    .collect();
                let inputs = self.context.store.interners.intern_ty_list(&inputs);

                let kind = TyKind::Function {
                    inputs,
                    output: lower_type(output, self.context, self.active_subst.clone()),
                    is_async: *is_async,
                };
                mk(kind)
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
            self.context
                .diagnostics
                .info("Lowering".into(), segment.identifier.span);
            let res = self.context.resolution(segment.id);
            let ty = self.lower_path_segment(segment, res);

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
            Resolution::Definition(
                def_id,
                DefinitionKind::Enum | DefinitionKind::Struct | DefinitionKind::TypeAlias,
            ) => self.lower_path_segment_with_definition(segment, def_id),
            Resolution::Definition(def_id, DefinitionKind::TypeParameter) => {
                let arguments = if let Some(arguments) = &segment.arguments {
                    arguments
                } else {
                    &taroc_hir::TypeArguments {
                        span: segment.identifier.span,
                        arguments: Default::default(),
                    }
                };
                check_generics_prohibited(
                    def_id,
                    &self.context.generics_of(def_id),
                    arguments,
                    self.context,
                );

                self.context.type_of(def_id)
            }
            Resolution::Definition(_, DefinitionKind::Interface) => {
                // TODO!!
                self.context.store.common_types.error
            }
            Resolution::Definition(_, DefinitionKind::AssociatedType) => {
                // TODO!!
                self.context.store.common_types.error
            }
            Resolution::Definition(
                _,
                DefinitionKind::Namespace | DefinitionKind::Module | DefinitionKind::Bridged,
            ) => self.context.store.common_types.ignore,
            Resolution::InterfaceSelfTypeAlias(..) => {
                // TODO!
                self.context.store.common_types.error
            }
            Resolution::SelfTypeAlias(definition_id) => {
                println!("{:?}", self.context.def_kind(definition_id));
                self.context.type_of(definition_id)
            }
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
        let generics = self.context.generics_of(def_id);

        let arguments = self.lower_type_arguments(def_id, &generics, segment);
        let local_subst = self.create_local_substitutions(&generics, &arguments);
        // let base = self.context.type_of(def_id);

        // Here we have our base, our substituitions and our arguments, we want to instantiate an instance of the type
        let ty = self.instantiate(def_id, arguments);

        self.active_subst.extend(local_subst);

        ty
    }

    fn lower_type_arguments(
        &mut self,
        def_id: DefinitionID,
        generics: &taroc_ty::Generics,
        segment: &taroc_hir::PathSegment,
    ) -> Vec<GenericArgument<'ctx>> {
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
            return vec![];
        }
        ok = check_generic_arg_count(&generics, segment, self.context);
        if !ok {
            return vec![];
        }

        let arguments = self.lower_generic_args(arguments);
        arguments
    }

    fn lower_generic_args(
        &mut self,
        arguments: &taroc_hir::TypeArguments,
    ) -> Vec<GenericArgument<'ctx>> {
        let mut output = vec![];
        for argument in &arguments.arguments {
            match argument {
                taroc_hir::TypeArgument::Type(ty) => {
                    let ty = lower_type(ty, self.context, self.active_subst.clone());
                    output.push(GenericArgument::Type(ty));
                }
                taroc_hir::TypeArgument::Const(_) => todo!(),
            }
        }

        return output;
    }
}

impl<'ctx> TypeLowerer<'ctx> {
    fn create_local_substitutions(
        &mut self,
        generics: &taroc_ty::Generics,
        args: &[GenericArgument<'ctx>],
    ) -> SubstitutionMap<'ctx> {
        let mut local_subst = SubstitutionMap::default();

        for (i, node) in generics.parameters.iter().enumerate() {
            match &node.kind {
                taroc_ty::GenericParameterDefinitionKind::Type { default } => {
                    let k = self.context.type_of(node.id);
                    let v = if let Some(v) = args.get(i) {
                        *v
                    } else if let Some(default) = default {
                        let ty = lower_type(default, self.context, self.active_subst.clone());
                        GenericArgument::Type(ty)
                    } else {
                        // TODO: pass Segment Here for error reporting
                        GenericArgument::Type(self.context.store.common_types.error)
                    };

                    local_subst.insert(k, v);
                }
                taroc_ty::GenericParameterDefinitionKind::Const { .. } => todo!(),
            }
        }

        local_subst
    }

    fn instantiate(&self, def_id: DefinitionID, arguments: Vec<GenericArgument<'ctx>>) -> Ty<'ctx> {
        let args = self.context.store.interners.intern_generic_args(&arguments);
        let kind = self.context.def_kind(def_id);

        let kind = match kind {
            DefinitionKind::Struct | DefinitionKind::Enum => TyKind::Adt(def_id, args),
            _ => {
                return self.context.store.common_types.error;
            }
        };

        let ty = self.context.store.interners.intern_ty(kind);
        return ty;
    }
}

fn check_generics_prohibited(
    def_id: DefinitionID,
    _generics: &taroc_ty::Generics,
    arguments: &taroc_hir::TypeArguments,
    context: GlobalContext<'_>,
) -> bool {
    let kind = context.def_kind(def_id);
    let ok = match kind {
        DefinitionKind::Struct
        | DefinitionKind::Enum
        | DefinitionKind::Interface
        | DefinitionKind::TypeAlias => true,
        DefinitionKind::TypeParameter | DefinitionKind::AssociatedType => false,
        _ => false,
    };

    if !ok && arguments.arguments.len() >= 1 {
        let msg = format!("Generics not permited on {:?}", kind);
        context.diagnostics.error(msg, arguments.span);
    }
    ok
}

pub fn check_generic_arg_count(
    generics: &taroc_ty::Generics,
    segment: &taroc_hir::PathSegment,
    context: GlobalContext<'_>,
) -> bool {
    let defaults_count = generics.default_count();
    let total_count = generics.total_count();

    let min = total_count - defaults_count;
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
