#![feature(let_chains)]
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::Package;

mod collect;
mod lower;
mod utils;

pub fn run(package: &Package, context: GlobalContext) -> CompileResult<()> {
    collect::run(package, context)?;
    Ok(())
}
