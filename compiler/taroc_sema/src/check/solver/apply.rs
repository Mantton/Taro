use crate::{
    check::solver::{ObligationSolver, OverloadGoal},
    error::TypeError,
};

impl<'icx, 'ctx> ObligationSolver<'icx, 'ctx> {
    pub fn resolve_application(&self, goal: OverloadGoal<'ctx>) -> Result<(), TypeError<'ctx>> {
        return Ok(());
    }
}
