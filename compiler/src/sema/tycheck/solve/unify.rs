use crate::sema::{
    error::TypeError,
    models::{Ty, TyKind},
    tycheck::{
        solve::ConstraintSolver,
        utils::{normalize_ty, unify::TypeUnifier},
    },
};

type UnificationResult<'ctx> = Result<(), TypeError<'ctx>>;

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn unify(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> UnificationResult<'ctx> {
        if a == b {
            return Ok(());
        }
        let a = self.structurally_resolve(a);
        let b = self.structurally_resolve(b);
        TypeUnifier::new(self.icx.clone()).unify(a, b)
    }

    pub fn unify_const(
        &self,
        a: crate::sema::models::Const<'ctx>,
        b: crate::sema::models::Const<'ctx>,
    ) -> Result<(), ()> {
        TypeUnifier::new(self.icx.clone()).unify_const(a, b)
    }

    /// Resolve inference variables AND normalize using param env.
    pub fn structurally_resolve(&self, ty: Ty<'ctx>) -> Ty<'ctx> {
        let ty = self.icx.resolve_vars_if_possible(ty);

        if matches!(ty.kind(), TyKind::Alias { .. } | TyKind::Parameter(..)) {
            return normalize_ty(self.icx.clone(), ty, &self.param_env);
        }

        return ty;
    }
}
