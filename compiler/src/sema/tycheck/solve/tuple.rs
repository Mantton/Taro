use super::ConstraintSolver;
use crate::sema::error::ExpectedFound;
use crate::{
    sema::{
        error::TypeError,
        models::{Ty, TyKind},
        tycheck::solve::{Adjustment, Goal, Obligation, SolverResult, TupleAccessGoalData},
    },
    span::Spanned,
};

impl<'ctx> ConstraintSolver<'ctx> {
    pub fn solve_tuple_access(&mut self, data: TupleAccessGoalData<'ctx>) -> SolverResult<'ctx> {
        self.solve_tuple_access_at(data, Vec::new(), Vec::new())
    }

    fn solve_tuple_access_at(
        &mut self,
        data: TupleAccessGoalData<'ctx>,
        prefix: Vec<Adjustment<'ctx>>,
        mut visited: Vec<Ty<'ctx>>,
    ) -> SolverResult<'ctx> {
        let original = data.clone();
        let TupleAccessGoalData {
            receiver_addressable,
            node_id,
            receiver_node_id,
            receiver,
            index,
            result,
            span,
        } = data;

        let final_receiver = self.structurally_resolve(receiver);
        if final_receiver.is_error() {
            let obligation = Obligation {
                location: span,
                goal: Goal::Equal(result, Ty::error(self.gcx())),
            };
            return SolverResult::Solved(vec![obligation]);
        }

        let mut adjustment = prefix.clone();
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
                        // Autoderef transforms the receiver before field
                        // projection. Recording it on the `.N` result instead
                        // asks THIR to dereference an already-projected element
                        // and leaves codegen projecting from `&(A, B)`.
                        self.record_adjustments(receiver_node_id, adjustment);
                        self.record_field_index(node_id, index);
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

        match self.custom_deref_fallback(
            receiver,
            receiver_addressable,
            span,
            &prefix,
            &mut visited,
        ) {
            Ok(Some((target, prefix, proof))) => {
                let mut data = original;
                data.receiver = target;
                data.receiver_addressable = true;
                let mut result = self.solve_tuple_access_at(data, prefix, visited);
                if let SolverResult::Solved(obligations) = &mut result {
                    obligations.extend(proof);
                }
                return result;
            }
            Err(result) => return result,
            Ok(None) => {}
        }

        let final_ty = prev.unwrap_or_else(|| self.structurally_resolve(receiver));
        let error = Spanned::new(TypeError::NotATuple { ty: final_ty }, span);
        SolverResult::Error(vec![error])
    }
}
