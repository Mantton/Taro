use crate::{compile::context::GlobalContext, error::CompileResult, hir};

pub fn validate_package(_package: &hir::Package, _gcx: GlobalContext) -> CompileResult<()> {
    // TODO
    Ok(())
}
