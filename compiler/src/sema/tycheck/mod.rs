use crate::{compile::context::GlobalContext, error::CompileResult, hir};

mod check;
mod collect;
mod lower;
mod solve;
mod wf;

pub fn typecheck_package(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    // Collect
    collect::run(package, context)?;
    // WellFormed?
    wf::run(package, context)?;
    // Check Body
    check::run(package, context)?;
    Ok(())
}
