use crate::{compile::context::GlobalContext, error::CompileResult, hir};

mod function;
mod structs;

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    function::run(package, context)?;
    structs::run(package, context)?;
    Ok(())
}
