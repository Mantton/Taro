use crate::{
    check::solver::{FieldAccessGoal, Goal, Obligation, SolverDelegate, SolverResult},
    error::TypeError,
    ty::{Constraint, TyKind},
    utils::instantiate_ty_with_args,
};

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_field_access(&mut self, goal: FieldAccessGoal<'ctx>) -> SolverResult<'ctx> {
        let base_ty = self.icx.shallow_resolve(goal.base_ty);
        match base_ty.kind() {
            TyKind::Adt(def, args) => {
                let def = self
                    .gcx()
                    .with_session_type_database(|db| db.structs[&def.id]);
                if let Some(field) = def.fields.iter().find(|f| f.name == goal.field.symbol) {
                    let field_ty = instantiate_ty_with_args(self.gcx(), field.ty, args);
                    let obligation = Obligation {
                        location: goal.field.span,
                        goal: Goal::Constraint(Constraint::TypeEquality(goal.result_var, field_ty)),
                    };
                    SolverResult::Solved(vec![obligation])
                } else {
                    SolverResult::Error(TypeError::UnknownField)
                }
            }
            TyKind::Infer(_) => SolverResult::Deferred,
            _ => SolverResult::Error(TypeError::NotAStruct),
        }
    }
}
