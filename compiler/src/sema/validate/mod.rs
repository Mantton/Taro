use crate::{compile::context::GlobalContext, error::CompileResult, hir};

pub fn validate_package(package: &hir::Package, gcx: GlobalContext) -> CompileResult<()> {
    // TODO
    Ok(())
}
