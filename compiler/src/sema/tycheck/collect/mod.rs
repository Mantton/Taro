use crate::{compile::context::GlobalContext, error::CompileResult, hir};

mod field;
mod function;
mod header;

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    header::run(package, context)?;
    field::run(package, context)?;
    function::run(package, context)?;
    Ok(())
}
