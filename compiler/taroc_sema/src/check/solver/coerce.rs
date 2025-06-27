use crate::{
    check::solver::{SolverDelegate, SolverResult},
    error::TypeError,
    ty::Ty,
};

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    pub fn solve_coerce(&self, from: Ty<'ctx>, to: Ty<'ctx>) -> SolverResult<'ctx> {
        let result = self.coerce(from, to);
        match result {
            Ok(defer) => {
                if defer.requeue() {
                    SolverResult::Deferred
                } else {
                    SolverResult::Solved(vec![])
                }
            }
            Err(err) => SolverResult::Error(err),
        }
    }

    pub fn coerce(&self, from: Ty<'ctx>, to: Ty<'ctx>) -> CoercionResult<'ctx> {
        let from = self.icx().shallow_resolve(from);
        let to = self.icx().shallow_resolve(to);

        if from.is_ty_var() {
            return self.coerce_from_inference_var(from, to);
        }

        self.unify(from, to)?;

        return Ok(CoercionOutput::Resolved(to));
    }
}

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    fn coerce_from_inference_var(&self, from: Ty<'ctx>, to: Ty<'ctx>) -> CoercionResult<'ctx> {
        assert!(from.is_ty_var() && self.icx().shallow_resolve(from) == from);
        assert!(self.icx().shallow_resolve(to) == to);

        // defer this coercion till we have more information regarding the inference vars
        if to.is_ty_var() {
            return Ok(CoercionOutput::Defer);
        }

        self.unify(from, to)?;
        return Ok(CoercionOutput::Resolved(to));
    }
}

pub enum CoercionOutput<'ctx> {
    Defer,
    Resolved(Ty<'ctx>),
}

pub type CoercionResult<'ctx> = Result<CoercionOutput<'ctx>, TypeError<'ctx>>;

impl<'ctx> CoercionOutput<'ctx> {
    pub fn requeue(self) -> bool {
        return matches!(self, CoercionOutput::Defer);
    }
}
