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
                if let Some(resolved) = self.resolve_projection(def_id, args) {
                    return resolved.fold_with(self);
                }

                // Fallback: Check ParamEnv for type equalities.
                // If we have a constraint like `T.Item == string`, we can use that here.
                let equiv_types = self.env.equivalent_types(ty);
                // Prefer concrete types over other aliases
                if let Some(&resolved) = equiv_types
                    .iter()
                    .find(|&&t| t != ty && !matches!(t.kind(), TyKind::Alias { .. }))
                {
                    return resolved.fold_with(self);
                }

                ty.super_fold_with(self)
            }
            TyKind::Alias { def_id, args, .. } => {
                let base = self.gcx().get_alias_type(def_id);
                let instantiated = instantiate_ty_with_args(self.gcx(), base, args);
                instantiated.fold_with(self)
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

        // Recursively normalize Self type using same context
        let self_ty = self.icx.resolve_vars_if_possible(*self_ty);

        // If Self is still an inference variable, cannot resolve yet
        if self_ty.is_infer() {
            // DEBUG: Infered Here
            return None;
        }

        // Strategy 1: Check ParamEnv bounds for the matching interface
        let bounds = self.env.bounds_for(self_ty);
        for bound_iface in &bounds {
            if bound_iface.id == interface_id {
                // Found matching bound - look up type witness from conformance
                let head = type_head_from_value_ty(self_ty)?;
                let witness = resolve_conformance_witness(gcx, head, *bound_iface)?;
                let witness_ty = witness.type_witnesses.get(&assoc_id)?;
                return Some(instantiate_ty_with_args(gcx, *witness_ty, args));
            }
        }

        // Strategy 2: For concrete types without explicit bounds, try direct lookup
        let head = type_head_from_value_ty(self_ty)?;
        let interface = InterfaceReference {
            id: interface_id,
            arguments: args,
        };
        let witness = resolve_conformance_witness(gcx, head, interface)?;
        let witness_ty = witness.type_witnesses.get(&assoc_id)?;
        Some(instantiate_ty_with_args(gcx, *witness_ty, args))
    }
}
