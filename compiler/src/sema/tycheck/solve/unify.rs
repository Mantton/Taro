use crate::sema::{
    error::TypeError,
    models::Ty,
    tycheck::{solve::ConstraintSolver, utils::unify::TypeUnifier},
};

type UnificationResult<'ctx> = Result<(), TypeError<'ctx>>;

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn unify(&self, a: Ty<'ctx>, b: Ty<'ctx>) -> UnificationResult<'ctx> {
        TypeUnifier::new(self.icx.clone()).unify(a, b)
    }

    pub fn structurally_resolve(&self, ty: Ty<'ctx>) -> Ty<'ctx> {
        TypeUnifier::new(self.icx.clone()).structurally_resolve(ty)
    }
}
