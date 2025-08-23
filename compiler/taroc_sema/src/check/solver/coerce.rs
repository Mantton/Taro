use crate::ty::Adjustment;
use crate::{
    check::solver::{SolverDelegate, SolverResult},
    error::{ExpectedFound, TypeError},
    ty::{Ty, TyKind},
};
use taroc_hir::Mutability;
use taroc_span::Span;

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
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
        let from = self.structurally_resolve(from);
        let to = self.structurally_resolve(to);

        if from.is_ty_var() {
            return self.coerce_from_inference_var(from, to);
        }

        match to.kind() {
            TyKind::Reference(_, to_mutability) => {
                return self.coerce_reference(from, to, to_mutability);
            }
            _ => {}
        }

        self.unify(to, from)?;
        return Ok(CoercionOutput::Resolved);
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    fn coerce_reference(
        &self,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
        to_mut: Mutability,
    ) -> CoercionResult<'ctx> {
        let from_ty = match from.kind() {
            TyKind::Reference(from_ty, from_mut) => {
                coerce_mutbl(from_mut, to_mut)?;
                from_ty
            }
            _ => {
                self.unify(from, to)?;
                return Ok(CoercionOutput::Resolved);
            }
        };

        let to_ty = match to.kind() {
            TyKind::Reference(to_ty, _) => to_ty,
            _ => unreachable!(),
        };

        self.unify(from_ty, to_ty)?;
        return Ok(CoercionOutput::Resolved);
    }
}

fn coerce_mutbl<'ctx>(from: Mutability, to: Mutability) -> Result<(), TypeError<'ctx>> {
    match (from, to) {
        (Mutability::Mutable, Mutability::Mutable) => Ok(()),
        (Mutability::Mutable, Mutability::Immutable) => Ok(()),
        (Mutability::Immutable, Mutability::Mutable) => Err(TypeError::Mutability),
        (Mutability::Immutable, Mutability::Immutable) => Ok(()),
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    fn coerce_from_inference_var(&self, from: Ty<'ctx>, to: Ty<'ctx>) -> CoercionResult<'ctx> {
        assert!(from.is_ty_var() && self.structurally_resolve(from) == from);
        assert!(self.structurally_resolve(to) == to);

        // defer this coercion till we have more information regarding the inference vars
        if to.is_ty_var() {
            return Ok(CoercionOutput::Defer);
        }

        self.unify(from, to)?;
        return Ok(CoercionOutput::Resolved);
    }
}

pub enum CoercionOutput {
    Defer,
    Resolved,
}

pub type CoercionResult<'ctx> = Result<CoercionOutput, TypeError<'ctx>>;

impl<'ctx> CoercionOutput {
    pub fn requeue(self) -> bool {
        return matches!(self, CoercionOutput::Defer);
    }
}

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_reciever_coerce(
        &self,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
        location: Span,
    ) -> SolverResult<'ctx> {
        let from = self.structurally_resolve(from);
        let to = self.structurally_resolve(to);
        if from.is_ty_var() {
            return SolverResult::Deferred;
        }

        // Break Early
        if from == to {
            return SolverResult::Solved(vec![]);
        }

        // By Value
        {
            let can_pass_by_value = self.icx().probe(|_| {
                let result = self.coerce(from, to);
                return result.is_ok();
            });

            if can_pass_by_value {
                return self.solve_coerce(from, to);
            }
        }

        // By Const Reference
        {
            let potential_ty = self
                .gcx()
                .mk_ty(TyKind::Reference(from, Mutability::Immutable));

            let ok = self.icx().probe(|_| {
                let result = self.unify(potential_ty, to);
                result.is_ok()
            });

            if ok {
                // record auto-ref adjustment
                self.icx()
                    .record_adjustments(location, vec![Adjustment::AutoRef]);
                return SolverResult::Solved(vec![]);
            }
        }

        // By Mut Reference
        {
            let potential_ty = self
                .gcx()
                .mk_ty(TyKind::Reference(from, Mutability::Mutable));

            let ok = self.icx().probe(|_| {
                let result = self.unify(potential_ty, to);
                result.is_ok()
            });

            if ok {
                // record auto-mut-ref adjustment
                self.icx()
                    .record_adjustments(location, vec![Adjustment::AutoMutRef]);
                return SolverResult::Solved(vec![]);
            }
        }

        // By Dereferencing
        {
            let mut autoderef = self.autoderef(location, from);
            let mut success = false;
            let mut steps = 0usize;
            while let Some(potential_ty) = autoderef.next() {
                success |= self.icx().probe(|_| {
                    let result = self.unify(potential_ty, to);
                    result.is_ok()
                });

                if success {
                    break;
                }
                steps += 1;
            }

            if success {
                // record auto-deref adjustments (one per deref step performed)
                if steps > 0 {
                    let mut v = Vec::with_capacity(steps);
                    for _ in 0..steps {
                        v.push(Adjustment::AutoDeref);
                    }
                    self.icx().record_adjustments(location, v);
                }
                // TODO: NoCopy Check
                return SolverResult::Solved(vec![]);
            }
        }

        SolverResult::Error(TypeError::InvalidReciever(ExpectedFound::new(to, from)))
    }
}
