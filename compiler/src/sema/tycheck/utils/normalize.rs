use crate::sema::tycheck::{
    infer::InferCtx,
    resolve_conformance_witness,
    utils::{instantiate::instantiate_ty_with_args, param_env::ParamEnv, type_head_from_value_ty},
};
use crate::{
    compile::context::GlobalContext,
    hir::DefinitionID,
    sema::{
        models::{AliasKind, GenericArgument, GenericArguments, InterfaceReference, Ty, TyKind},
        tycheck::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    },
};
use std::rc::Rc;

/// Normalize a type using the given inference context and parameter environment.
/// The inference context is used to resolve inference variables before normalizing.
pub fn normalize_ty<'ctx>(icx: Rc<InferCtx<'ctx>>, ty: Ty<'ctx>, env: &ParamEnv<'ctx>) -> Ty<'ctx> {
    let mut folder = NormalizeFolder { icx, env };
    ty.fold_with(&mut folder)
}

/// Shallow normalization that only resolves type aliases (weak/inherent).
/// Does NOT resolve projections or inference variables.
/// Used for contexts without InferCtx like codegen or canonical constraint building.
pub fn normalize_aliases<'ctx>(gcx: GlobalContext<'ctx>, ty: Ty<'ctx>) -> Ty<'ctx> {
    let mut folder = ShallowNormalizeFolder { gcx };
    ty.fold_with(&mut folder)
}

struct ShallowNormalizeFolder<'ctx> {
    gcx: GlobalContext<'ctx>,
}

impl<'ctx> TypeFolder<'ctx> for ShallowNormalizeFolder<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        match ty.kind() {
            TyKind::Alias { kind, def_id, args } if kind != AliasKind::Projection => {
                let base = self.gcx.get_alias_type(def_id);
                let instantiated = instantiate_ty_with_args(self.gcx, base, args);
                return instantiated.fold_with(self);
            }
            _ => ty.super_fold_with(self),
        }
    }
}

struct NormalizeFolder<'a, 'ctx> {
    icx: Rc<InferCtx<'ctx>>,
    env: &'a ParamEnv<'ctx>,
}

impl<'a, 'ctx> NormalizeFolder<'a, 'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.icx.gcx
    }
}

impl<'a, 'ctx> TypeFolder<'ctx> for NormalizeFolder<'a, 'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.icx.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        // First resolve any inference variables
        let ty = self.icx.resolve_vars_if_possible(ty);

        match ty.kind() {
            TyKind::Alias {
                kind: AliasKind::Projection,
                def_id,
                args,
            } => {
                // Priority 1: Check ParamEnv for explicit type equalities.
                // This handles parametric normalization like `T: Container[Item=int]`
                // where we want `T.Item` to normalize to `int`.

                let equiv_types = self.env.equivalent_types(ty);

                // Prefer concrete types (non-aliased, non-parameter)
                if let Some(&resolved) = equiv_types
                    .iter()
                    .find(|&&t| t != ty && !matches!(t.kind(), TyKind::Alias { .. }))
                {
                    return resolved.fold_with(self);
                }

                if let Some(resolved) = self.resolve_projection(def_id, args) {
                    return resolved.fold_with(self);
                }

                ty.super_fold_with(self)
            }
            TyKind::Alias { def_id, args, .. } => {
                let base = self.gcx().get_alias_type(def_id);
                let instantiated = instantiate_ty_with_args(self.gcx(), base, args);
                instantiated.fold_with(self)
            }
            // Handle type parameters with equality constraints
            // e.g., for `where T == string`, normalize T to string
            TyKind::Parameter(_) => {
                let equiv_types = self.env.equivalent_types(ty);
                // Find a concrete type equivalent to this parameter
                // Prefer non-parameter, non-alias types
                if let Some(&resolved) = equiv_types.iter().find(|&&t| {
                    !matches!(
                        t.kind(),
                        TyKind::Parameter(_) | TyKind::Alias { .. } | TyKind::Infer(_)
                    )
                }) {
                    return resolved.fold_with(self);
                }
                // If no concrete type found, try any alias (which will be normalized recursively)
                if let Some(&resolved) = equiv_types
                    .iter()
                    .find(|&&t| t != ty && !matches!(t.kind(), TyKind::Parameter(_)))
                {
                    return resolved.fold_with(self);
                }
                ty
            }
            _ => ty.super_fold_with(self),
        }
    }
}

impl<'a, 'ctx> NormalizeFolder<'a, 'ctx> {
    fn resolve_projection(
        &self,
        assoc_id: DefinitionID,
        args: GenericArguments<'ctx>,
    ) -> Option<Ty<'ctx>> {
        let gcx = self.gcx();
        let interface_id = gcx.definition_parent(assoc_id)?;
        let self_arg = args.get(0)?;
        let GenericArgument::Type(self_ty) = self_arg else {
            return None;
        };

        // Recursively normalize substituted Self type
        let self_ty = self.icx.resolve_vars_if_possible(*self_ty);

        // If Self is still an inference variable, cannot resolve yet
        if self_ty.is_infer() {
            return None;
        }

        // Existential types with associated type bindings: resolve projections directly.
        // For `any Producer[Output = int].Output`, extract `int` from the binding.
        // This is the most direct resolution path since bindings are explicit.
        if let TyKind::BoxedExistential { interfaces } = self_ty.kind() {
            let assoc_name = gcx.definition_ident(assoc_id).symbol;

            for iface in interfaces.iter() {
                // Match interface by ID (direct match or parent of associated type)
                if iface.id == interface_id || gcx.definition_parent(assoc_id) == Some(iface.id) {
                    for binding in iface.bindings {
                        if binding.name == assoc_name {
                            return Some(binding.ty);
                        }
                    }
                }
            }
        }

        let instantiate_witness = |witness: crate::sema::models::ConformanceWitness<'ctx>| {
            let witness_ty = witness.type_witnesses.get(&assoc_id)?;

            if let Some(impl_id) = witness.extension_id {
                // If the witness comes from a concrete implementation, we need to solve for the
                // implementation's generic parameters by unifying the actual Self type with
                // the implementation's target type.
                // e.g. Self = &List[int32] vs ImplTarget = &List[Element]
                let impl_generics = gcx.generics_of(impl_id);
                if !impl_generics.is_empty() {
                    let span = gcx.definition_ident(assoc_id).span;
                    let impl_args = self.icx.fresh_args_for_def(impl_id, span);

                    let target_ty = gcx
                        .get_impl_target_ty(impl_id)
                        .unwrap_or_else(|| gcx.get_type(impl_id));
                    let instantiated_target = instantiate_ty_with_args(gcx, target_ty, impl_args);

                    let unifier =
                        crate::sema::tycheck::utils::unify::TypeUnifier::new(self.icx.clone());
                    if unifier.unify(self_ty, instantiated_target).is_ok() {
                        return Some(instantiate_ty_with_args(gcx, *witness_ty, impl_args));
                    }
                }
            }

            Some(instantiate_ty_with_args(gcx, *witness_ty, args))
        };

        // Strategy 1: Check ParamEnv bounds for the matching interface
        let bounds = self.env.bounds_for(self_ty);
        for bound_iface in &bounds {
            if bound_iface.id == interface_id {
                // Found matching bound - look up type witness from conformance
                let head = type_head_from_value_ty(self_ty)?;
                let witness = resolve_conformance_witness(gcx, head, *bound_iface)?;
                return instantiate_witness(witness);
            }
        }

        // Strategy 2: For concrete types without explicit bounds, try direct lookup
        let head = type_head_from_value_ty(self_ty)?;
        let interface = InterfaceReference {
            id: interface_id,
            arguments: args,
            bindings: &[],
        };
        let witness = resolve_conformance_witness(gcx, head, interface)?;
        instantiate_witness(witness)
    }
}
