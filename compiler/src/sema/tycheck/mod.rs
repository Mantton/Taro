use crate::{compile::state::CompilerState, error::CompileResult, hir};

mod collect;
pub mod models;

pub fn check_package(package: &hir::Package, state: CompilerState) -> CompileResult<()> {
    collect::generics::run(package, state)?;
    Ok(())
}
