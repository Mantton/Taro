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
    pub fn unify(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> UnificationResult<'ctx> {
        if a == b {
            return Ok(());
        }
        // println!("Pre– {} & {}", a.format(self.gcx()), b.format(self.gcx()));
        let a = self.structurally_resolve(a);
        let b = self.structurally_resolve(b);
        // println!("Post– {} & {}\n", a.format(self.gcx()), b.format(self.gcx()));
        TypeUnifier::new(self.icx.clone()).unify(a, b)
    }

    /// Resolve inference variables AND normalize using param env.
    pub fn structurally_resolve(&self, ty: Ty<'ctx>) -> Ty<'ctx> {
        let ty = self.icx.resolve_vars_if_possible(ty);
        normalize_ty(self.icx.clone(), ty, &self.param_env)
    }
}
