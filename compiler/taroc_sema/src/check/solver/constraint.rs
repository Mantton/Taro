use crate::{
    check::solver::SolverDelegate, error::TypeError, ty::Constraint, utils::constraint2str,
};

impl<'icx, 'ctx> SolverDelegate<'icx, 'ctx> {
    pub fn solve_constraint(&self, constraint: Constraint<'ctx>) -> Result<(), TypeError<'ctx>> {
        match constraint {
            Constraint::Bound { ty, interface } => {
                // TODO: Bound Checks
            }
            Constraint::TypeEquality(a, b) => self.unify(a, b)?,
        }
        return Ok(());
    }
}
