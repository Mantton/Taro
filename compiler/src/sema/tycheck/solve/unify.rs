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

        let mut unifier = TypeUnifier::with_env(self.icx.clone(), &self.param_env);
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
        let ty = self.icx.resolve_vars_if_possible(ty);
        normalize_ty(self.icx.clone(), ty, &self.param_env)
    }
}
