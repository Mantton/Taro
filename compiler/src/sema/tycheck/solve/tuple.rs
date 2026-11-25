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

            let (field_ty, arity) = match ty.kind() {
                TyKind::Tuple(elements) => (elements.get(index).copied(), elements.len()),
                TyKind::Adt(def, args) if def.kind == crate::sema::models::AdtKind::Struct => {
                    let definition = self.gcx().get_struct_definition(def.id);
                    if !definition.positional { continue; }
                    if let Some(field) = definition.fields.get(index)
                        && !self.gcx().is_visibility_allowed(field.visibility, self.current_def)
                    {
                        return SolverResult::Error(vec![Spanned::new(
                            TypeError::FieldNotVisible { name: field.name, struct_ty: ty }, span,
                        )]);
                    }
                    let ty = definition.fields.get(index).map(|field| {
                        super::instantiate_ty_with_args(self.gcx(), field.ty, args)
                    });
                    (ty, definition.fields.len())
                }
                TyKind::Infer(_) => return SolverResult::Deferred,
                _ => continue,
            };
            let Some(field_ty) = field_ty else {
                let error = if matches!(ty.kind(), TyKind::Tuple(_)) {
                    TypeError::TupleIndexOutOfBounds(ExpectedFound::new(index.saturating_add(1), arity))
                } else {
                    TypeError::PositionalFieldOutOfBounds { owner: ty, index, arity }
                };
                return SolverResult::Error(vec![Spanned::new(error, span)]);
            };
            // Dereference the receiver before projecting its positional field.
            self.record_adjustments(receiver_node_id, adjustment);
            self.record_field_index(node_id, index);
            return self.solve_equality(span, result, field_ty);
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
