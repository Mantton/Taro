use crate::{
    check::solver::{
        FieldAccessGoal, Goal, Obligation, SolverDelegate, SolverResult, TupleAccessGoal,
    },
    error::TypeError,
    ty::{AdtKind, Constraint, TyKind},
    utils::instantiate_ty_with_args,
};

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    pub fn solve_field_access(&mut self, goal: FieldAccessGoal<'ctx>) -> SolverResult<'ctx> {
        let base_ty = self.icx().shallow_resolve(goal.base_ty);

        if base_ty.is_infer() {
            return SolverResult::Deferred;
        }

        let mut autoderef = self.fcx.autoderef(goal.field_span, base_ty);

        while let Some(dereferenced_ty) = autoderef.next() {
            match dereferenced_ty.kind() {
                TyKind::Adt(def, args) if def.kind == AdtKind::Struct => {
                    let def = self
                        .gcx()
                        .with_session_type_database(|db| db.structs[&def.id]);
                    let result = if let Some(field) = def
                        .variant
                        .fields
                        .iter()
                        .find(|f| f.name == goal.field.symbol)
                    {
                        let field_ty = instantiate_ty_with_args(self.gcx(), field.ty, args);
                        let obligation = Obligation {
                            location: goal.field.span,
                            goal: Goal::Constraint(Constraint::TypeEquality(
                                field_ty,
                                goal.result_var,
                            )),
                        };

                        // TODO: Adjustments, Field Index
                        SolverResult::Solved(vec![obligation])
                    } else {
                        SolverResult::Error(TypeError::UnknownField(
                            goal.field.symbol,
                            dereferenced_ty,
                        ))
                    };

                    return result;
                }
                _ => {}
            }
        }

        return SolverResult::Error(TypeError::UnknownField(
            goal.field.symbol,
            autoderef.final_ty(),
        ));
    }
}

impl<'icx, 'ctx, 'rcx> SolverDelegate<'icx, 'ctx, 'rcx> {
    pub fn solve_tuple_access(&mut self, goal: TupleAccessGoal<'ctx>) -> SolverResult<'ctx> {
        let base_ty = self.icx().shallow_resolve(goal.base_ty);
        match base_ty.kind() {
            TyKind::Tuple(items) => {
                if goal.index < items.len() {
                    let item_ty = items[goal.index];
                    let obligation = Obligation {
                        location: goal.index_span,
                        goal: Goal::Constraint(Constraint::TypeEquality(item_ty, goal.result_var)),
                    };
                    SolverResult::Solved(vec![obligation])
                } else {
                    SolverResult::Error(TypeError::TupleIndexOutOfBounds(
                        crate::error::ExpectedFound::new(items.len(), goal.index),
                    ))
                }
            }
            TyKind::Infer(_) => SolverResult::Deferred,
            _ => SolverResult::Error(TypeError::NotATuple),
        }
    }
}
