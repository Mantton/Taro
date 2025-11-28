use crate::{compile::context::GlobalContext, error::CompileResult, hir};

mod collect;
pub mod models;

pub fn check_package(package: &hir::Package, gcx: GlobalContext) -> CompileResult<()> {
    collect::generics::run(package, gcx)?;
    Ok(())
}
