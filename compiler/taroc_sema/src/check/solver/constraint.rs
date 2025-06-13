use crate::{
    check::solver::ObligationSolver, error::TypeError, ty::Constraint, utils::constraint2str,
};

impl<'icx, 'ctx> ObligationSolver<'icx, 'ctx> {
    pub fn solve_constraint(&self, constraint: Constraint<'ctx>) -> Result<(), TypeError<'ctx>> {
        println!("Solve: {}", constraint2str(constraint, self.icx.gcx));

        match constraint {
            Constraint::Bound { ty, interface } => {
                // TODO: Bound Checks
            }
            Constraint::TypeEquality(a, b) => self.unify(a, b)?,
        }
        return Ok(());
    }
}
