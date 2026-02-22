use crate::sema::tycheck::{
    infer::InferCtx,
    resolve_conformance_witness,
    utils::{
        instantiate::{instantiate_constraint_with_args, instantiate_ty_with_args},
        param_env::ParamEnv,
        type_head_from_value_ty,
    },
};
use crate::{
    compile::context::GlobalContext,
    hir::DefinitionID,
    sema::{
        models::{
            AliasKind, Const, ConstKind, ConstVarID, GenericArgument, GenericArguments, InferTy,
            InterfaceReference, Ty, TyKind, TyVarID,
        },
        tycheck::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    },
};
use rustc_hash::FxHashSet;
use std::rc::Rc;

/// Normalize a type using the given inference context and parameter environment.
/// The inference context is used to resolve inference variables before normalizing.
pub fn normalize_ty<'ctx>(icx: Rc<InferCtx<'ctx>>, ty: Ty<'ctx>, env: &ParamEnv<'ctx>) -> Ty<'ctx> {
    let mut in_progress = FxHashSet::default();
    in_progress.reserve(env.normalization_set_capacity_hint());
    let mut folder = NormalizeFolder {
        icx,
        env,
        in_progress,
    };
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
    in_progress: FxHashSet<Ty<'ctx>>,
}

fn collect_fresh_impl_var_ids<'ctx>(
    args: GenericArguments<'ctx>,
) -> (Vec<TyVarID>, Vec<ConstVarID>) {
    let mut ty_vars = Vec::new();
    let mut const_vars = Vec::new();
    for arg in args {
        match arg {
            GenericArgument::Type(ty) => {
                if let TyKind::Infer(InferTy::TyVar(id)) = ty.kind() {
                    ty_vars.push(id);
                }
            }
            GenericArgument::Const(c) => {
                if let ConstKind::Infer(id) = c.kind {
                    const_vars.push(id);
                }
            }
        }
    }
    (ty_vars, const_vars)
}

fn arg_contains_any_fresh_var<'ctx>(
    arg: &GenericArgument<'ctx>,
    fresh_ty_vars: &[TyVarID],
    fresh_const_vars: &[ConstVarID],
) -> bool {
    match arg {
        GenericArgument::Type(ty) => {
            ty_contains_any_fresh_var(*ty, fresh_ty_vars, fresh_const_vars)
        }
        GenericArgument::Const(c) => {
            const_contains_any_fresh_var(*c, fresh_ty_vars, fresh_const_vars)
        }
    }
}

fn const_contains_any_fresh_var<'ctx>(
    c: Const<'ctx>,
    fresh_ty_vars: &[TyVarID],
    fresh_const_vars: &[ConstVarID],
) -> bool {
    if ty_contains_any_fresh_var(c.ty, fresh_ty_vars, fresh_const_vars) {
        return true;
    }
    match c.kind {
        ConstKind::Infer(id) => fresh_const_vars.contains(&id),
        _ => false,
    }
}

fn ty_contains_any_fresh_var<'ctx>(
    ty: Ty<'ctx>,
    fresh_ty_vars: &[TyVarID],
    fresh_const_vars: &[ConstVarID],
) -> bool {
    match ty.kind() {
        TyKind::Array { element, len } => {
            ty_contains_any_fresh_var(element, fresh_ty_vars, fresh_const_vars)
                || const_contains_any_fresh_var(len, fresh_ty_vars, fresh_const_vars)
        }
        TyKind::Adt(_, args) | TyKind::Alias { args, .. } => args
            .iter()
            .any(|arg| arg_contains_any_fresh_var(arg, fresh_ty_vars, fresh_const_vars)),
        TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
            ty_contains_any_fresh_var(inner, fresh_ty_vars, fresh_const_vars)
        }
        TyKind::Tuple(items) => items
            .iter()
            .any(|t| ty_contains_any_fresh_var(*t, fresh_ty_vars, fresh_const_vars)),
        TyKind::FnPointer { inputs, output } => {
            inputs
                .iter()
                .any(|t| ty_contains_any_fresh_var(*t, fresh_ty_vars, fresh_const_vars))
                || ty_contains_any_fresh_var(output, fresh_ty_vars, fresh_const_vars)
        }
        TyKind::BoxedExistential { interfaces } => interfaces.iter().any(|iface| {
            iface
                .arguments
                .iter()
                .any(|arg| arg_contains_any_fresh_var(arg, fresh_ty_vars, fresh_const_vars))
                || iface.bindings.iter().any(|binding| {
                    ty_contains_any_fresh_var(binding.ty, fresh_ty_vars, fresh_const_vars)
                })
        }),
        TyKind::Closure {
            captured_generics,
            inputs,
            output,
            ..
        } => {
            captured_generics
                .iter()
                .any(|arg| arg_contains_any_fresh_var(arg, fresh_ty_vars, fresh_const_vars))
                || inputs
                    .iter()
                    .any(|t| ty_contains_any_fresh_var(*t, fresh_ty_vars, fresh_const_vars))
                || ty_contains_any_fresh_var(output, fresh_ty_vars, fresh_const_vars)
        }
        TyKind::Infer(InferTy::TyVar(id)) => fresh_ty_vars.contains(&id),
        TyKind::Bool
        | TyKind::Rune
        | TyKind::String
        | TyKind::Int(_)
        | TyKind::UInt(_)
        | TyKind::Float(_)
        | TyKind::Infer(_)
        | TyKind::Parameter(_)
        | TyKind::Opaque(_)
        | TyKind::Error
        | TyKind::Never => false,
    }
}

impl<'a, 'ctx> NormalizeFolder<'a, 'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.icx.gcx
    }

    fn refine_impl_args_from_constraints(
        &self,
        icx: Rc<InferCtx<'ctx>>,
        impl_id: DefinitionID,
        impl_args: GenericArguments<'ctx>,
    ) {
        let gcx = self.gcx();
        let constraints = crate::sema::tycheck::constraints::canonical_constraints_of(gcx, impl_id);
        if constraints.is_empty() {
            return;
        }

        let instantiated: Vec<_> = constraints
            .into_iter()
            .map(|constraint| instantiate_constraint_with_args(gcx, constraint.value, impl_args))
            .collect();
        let env = ParamEnv::new(instantiated.clone());
        let unifier = crate::sema::tycheck::utils::unify::TypeUnifier::new(icx.clone());

        // Equalities can unlock each other (e.g. `A == B.C`, `B == Concrete`),
        // so iterate to a small fixed point.
        let passes = instantiated.len().max(1) * 2;
        for _ in 0..passes {
            for constraint in &instantiated {
                let crate::sema::models::Constraint::TypeEquality(lhs, rhs) = *constraint else {
                    continue;
                };

                let lhs = normalize_ty(icx.clone(), lhs, &env);
                let rhs = normalize_ty(icx.clone(), rhs, &env);
                let _ = unifier.unify(lhs, rhs);
            }
        }
    }
}

impl<'a, 'ctx> TypeFolder<'ctx> for NormalizeFolder<'a, 'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.icx.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        // Resolve one level of inference first; recursive folding handles nested structure.
        let ty = self.icx.shallow_resolve(ty);

        // Break normalization cycles such as `T.Item == U` and `U == T.Item`.
        if !self.in_progress.insert(ty) {
            return ty;
        }

        let normalized = match ty.kind() {
            TyKind::Alias {
                kind: AliasKind::Projection,
                def_id,
                args,
            } => {
                // Priority 1: Check ParamEnv for explicit type equalities.
                // This handles parametric normalization like `T: Container[Item=int]`
                // where we want `T.Item` to normalize to `int`.

                if self.env.has_type_equalities() {
                    let equiv_types = self.env.equivalent_types(ty);

                    // Prefer non-alias equalities first (including parameters).
                    // Cycle prevention is handled by `in_progress`.
                    if let Some(&resolved) = equiv_types.iter().find(|&&t| {
                        t != ty && !matches!(t.kind(), TyKind::Alias { .. } | TyKind::Infer(_))
                    }) {
                        resolved.fold_with(self)
                    } else if let Some(resolved) = self.resolve_projection(def_id, args) {
                        resolved.fold_with(self)
                    } else {
                        ty.super_fold_with(self)
                    }
                } else if let Some(resolved) = self.resolve_projection(def_id, args) {
                    resolved.fold_with(self)
                } else {
                    ty.super_fold_with(self)
                }
            }
            TyKind::Alias { def_id, args, .. } => {
                let base = self.gcx().get_alias_type(def_id);
                let instantiated = instantiate_ty_with_args(self.gcx(), base, args);
                instantiated.fold_with(self)
            }
            // Handle type parameters with equality constraints
            // e.g., for `where T == string`, normalize T to string
            TyKind::Parameter(_) => {
                if !self.env.has_type_equalities() {
                    ty
                } else {
                    let equiv_types = self.env.equivalent_types(ty);
                    // Find a concrete type equivalent to this parameter
                    // Prefer non-parameter, non-alias types
                    if let Some(&resolved) = equiv_types.iter().find(|&&t| {
                        !matches!(
                            t.kind(),
                            TyKind::Parameter(_) | TyKind::Alias { .. } | TyKind::Infer(_)
                        )
                    }) {
                        resolved.fold_with(self)
                    } else if let Some(&resolved) = equiv_types.iter().find(|&&t| {
                        if t == ty || matches!(t.kind(), TyKind::Parameter(_) | TyKind::Infer(_)) {
                            return false;
                        }
                        // Avoid selecting a projection currently being normalized.
                        if matches!(
                            t.kind(),
                            TyKind::Alias {
                                kind: AliasKind::Projection,
                                ..
                            }
                        ) && self.in_progress.contains(&t)
                        {
                            return false;
                        }
                        true
                    }) {
                        resolved.fold_with(self)
                    } else {
                        ty
                    }
                }
            }
            _ => ty.super_fold_with(self),
        };

        self.in_progress.remove(&ty);
        normalized
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
                    let target_ty = gcx
                        .get_impl_target_ty(impl_id)
                        .unwrap_or_else(|| gcx.get_type(impl_id));
                    if self_ty.contains_inference() {
                        // Self may include inference vars owned by the caller context.
                        // Solve in a probe on the caller InferCtx so those vars can participate,
                        // while avoiding leakage of fresh impl vars when this path is speculative.
                        let solved = self.icx.probe(|_| {
                            let impl_args = self.icx.fresh_args_for_def(impl_id, span);
                            let (fresh_ty_vars, fresh_const_vars) =
                                collect_fresh_impl_var_ids(impl_args);
                            let instantiated_target =
                                instantiate_ty_with_args(gcx, target_ty, impl_args);

                            let unifier = crate::sema::tycheck::utils::unify::TypeUnifier::new(
                                self.icx.clone(),
                            );
                            if unifier.unify(self_ty, instantiated_target).is_ok() {
                                self.refine_impl_args_from_constraints(
                                    self.icx.clone(),
                                    impl_id,
                                    impl_args,
                                );
                                let resolved_args: Vec<_> = impl_args
                                    .iter()
                                    .map(|arg| match arg {
                                        GenericArgument::Type(ty) => GenericArgument::Type(
                                            self.icx.resolve_vars_if_possible(*ty),
                                        ),
                                        GenericArgument::Const(c) => GenericArgument::Const(
                                            self.icx.resolve_const_if_possible(*c),
                                        ),
                                    })
                                    .collect();

                                let unresolved_fresh = resolved_args.iter().any(|arg| {
                                    arg_contains_any_fresh_var(
                                        arg,
                                        &fresh_ty_vars,
                                        &fresh_const_vars,
                                    )
                                });
                                if !unresolved_fresh {
                                    let resolved_args =
                                        gcx.store.interners.intern_generic_args(resolved_args);
                                    return Some(instantiate_ty_with_args(
                                        gcx,
                                        *witness_ty,
                                        resolved_args,
                                    ));
                                }
                            }
                            None
                        });
                        if solved.is_some() {
                            return solved;
                        }
                    } else {
                        // Use a local inference context so speculative impl-arg solving
                        // cannot leak fresh vars into the caller's inference state.
                        let local_icx = Rc::new(InferCtx::new(gcx));
                        let impl_args = local_icx.fresh_args_for_def(impl_id, span);
                        let (fresh_ty_vars, fresh_const_vars) =
                            collect_fresh_impl_var_ids(impl_args);
                        let instantiated_target =
                            instantiate_ty_with_args(gcx, target_ty, impl_args);

                        let unifier =
                            crate::sema::tycheck::utils::unify::TypeUnifier::new(local_icx.clone());
                        if unifier.unify(self_ty, instantiated_target).is_ok() {
                            self.refine_impl_args_from_constraints(
                                local_icx.clone(),
                                impl_id,
                                impl_args,
                            );
                            let resolved_args: Vec<_> = impl_args
                                .iter()
                                .map(|arg| match arg {
                                    GenericArgument::Type(ty) => GenericArgument::Type(
                                        local_icx.resolve_vars_if_possible(*ty),
                                    ),
                                    GenericArgument::Const(c) => GenericArgument::Const(
                                        local_icx.resolve_const_if_possible(*c),
                                    ),
                                })
                                .collect();
                            let resolved_args =
                                gcx.store.interners.intern_generic_args(resolved_args);

                            // If impl args still mention fresh local vars, do not materialize
                            // those locals into the outer type context.
                            let unresolved = resolved_args.iter().any(|arg| {
                                arg_contains_any_fresh_var(arg, &fresh_ty_vars, &fresh_const_vars)
                            });
                            if !unresolved {
                                return Some(instantiate_ty_with_args(
                                    gcx,
                                    *witness_ty,
                                    resolved_args,
                                ));
                            }
                        }
                    }

                    // Generic impl witness exists, but impl args could not yet be solved.
                    // Returning `None` avoids incorrectly instantiating witness types with
                    // projection args (which are interface args, not impl args).
                    return None;
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
