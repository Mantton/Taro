use crate::sema::{
    error::TypeError,
    models::Ty,
    tycheck::{
        solve::ConstraintSolver,
        utils::{normalize_ty, unify::TypeUnifier},
    },
};

type UnificationResult<'ctx> = Result<(), TypeError<'ctx>>;

impl<'ctx> ConstraintSolver<'ctx> {
    #[inline(always)]
    pub fn unify(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> UnificationResult<'ctx> {
        if a == b {
            return Ok(());
        }
        let a = self.structurally_resolve(a);
        let b = self.structurally_resolve(b);
        if a == b {
            return Ok(());
        }

        let unifier = TypeUnifier::with_env(self.icx.clone(), &self.param_env);
        unifier.unify(a, b)?;
        Ok(())
    }

    pub fn unify_const(
        &self,
        a: crate::sema::models::Const<'ctx>,
        b: crate::sema::models::Const<'ctx>,
    ) -> Result<(), ()> {
        TypeUnifier::with_env(self.icx.clone(), &self.param_env).unify_const(a, b)
    }

    /// Resolve inference variables AND normalize using param env.
    pub fn structurally_resolve(&self, ty: Ty<'ctx>) -> Ty<'ctx> {
        // Projection equality lookup uses structural keys before normalizing
        // their arguments, so resolve those arguments before entering it.
        let ty = self.icx.resolve_vars_if_possible(ty);
        normalize_ty(self.icx.clone(), ty, &self.param_env)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        sema::{
            models::{AliasKind, Constraint, GenericArgument, GenericParameter, TyKind},
            tycheck::{infer::InferCtx, utils::ParamEnv},
        },
        span::{FileID, Span},
        test_support::analyze_script,
    };
    use std::rc::Rc;

    #[test]
    fn projection_equality_uses_the_resolved_inference_arguments() {
        analyze_script(
            "interface Container { type Item; }\nfunc main() {}\n",
            |_, gcx| {
                let assoc_id = gcx.with_type_database(gcx.package_index(), |db| {
                    *db.def_to_iface_def
                        .values()
                        .next()
                        .unwrap()
                        .assoc_types
                        .values()
                        .next()
                        .unwrap()
                });

                let icx = Rc::new(InferCtx::new(gcx));
                let parameter = Ty::new(
                    TyKind::Parameter(GenericParameter {
                        index: 0,
                        name: gcx.intern_symbol("T"),
                    }),
                    gcx,
                );
                let inferred = icx.next_ty_var(Span::empty(FileID::from_raw(0)));
                TypeUnifier::new(icx.clone())
                    .unify(inferred, parameter)
                    .unwrap();
                let projection = |self_ty| {
                    Ty::new(
                        TyKind::Alias {
                            kind: AliasKind::Projection,
                            def_id: assoc_id,
                            args: gcx
                                .store
                                .interners
                                .intern_generic_args(vec![GenericArgument::Type(self_ty)]),
                        },
                        gcx,
                    )
                };
                // The environment knows T.Item == int32, while the caller's type still
                // spells its receiver as an inference variable already bound to T.
                let solver = ConstraintSolver {
                    icx,
                    obligations: Default::default(),
                    adjustments: Default::default(),
                    interface_calls: Default::default(),
                    integer_literals: Default::default(),
                    field_indices: Default::default(),
                    property_reads: Default::default(),
                    property_writes: Default::default(),
                    overload_sources: Default::default(),
                    value_resolutions: Default::default(),
                    instantiation_args: Default::default(),
                    compiler_call_contexts: Default::default(),
                    current_def: assoc_id,
                    assumption_constraints: &[],
                    param_env: ParamEnv::new(vec![Constraint::TypeEquality(
                        projection(parameter),
                        gcx.types.int32,
                    )]),
                    visible_traits: Default::default(),
                };
                assert_eq!(
                    solver.structurally_resolve(projection(inferred)),
                    gcx.types.int32
                );
            },
        );
    }
}
