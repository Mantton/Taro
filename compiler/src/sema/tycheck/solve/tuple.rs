use super::ConstraintSolver;
use crate::sema::error::ExpectedFound;
use crate::{
    sema::{
        error::TypeError,
        models::{Ty, TyKind},
        tycheck::solve::{Adjustment, SolverResult, TupleAccessGoalData},
    },
    span::Spanned,
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_tuple_access(&mut self, data: TupleAccessGoalData<'ctx>) -> SolverResult<'ctx> {
        let TupleAccessGoalData {
            node_id,
            receiver,
            index,
            result,
            span,
        } = data;

        let mut adjustment = Vec::new();
        let mut prev: Option<Ty<'ctx>> = None;

        for ty in self.autoderef(receiver) {
            let ty = self.structurally_resolve(ty);
            if let Some(_) = prev {
                adjustment.push(Adjustment::Dereference);
            }
            prev = Some(ty);

            match ty.kind() {
                TyKind::Tuple(elements) => {
                    if index < elements.len() {
                        self.record_adjustments(node_id, adjustment);
                        return self.solve_equality(span, result, elements[index]);
                    } else {
                        // Index out of bounds for this tuple
                        let error = Spanned::new(
                            TypeError::TupleIndexOutOfBounds(ExpectedFound::new(
                                index + 1,
                                elements.len(),
                            )),
                            span,
                        );
                        return SolverResult::Error(vec![error]);
                    }
                }
                TyKind::Infer(_) => {
                    // Start ambiguous if we hit an inference variable
                    // because it *could* be a tuple eventually.
                    return SolverResult::Deferred;
                }
                _ => {
                    // Not a tuple, continue autoderefing.
                    continue;
                }
            }
        }

        let final_ty = prev.unwrap_or_else(|| self.structurally_resolve(receiver));
        let error = Spanned::new(TypeError::NotATuple { ty: final_ty }, span);
        SolverResult::Error(vec![error])
    }
}
