#![feature(let_chains)]
#![feature(if_let_guard)]
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::Package;

mod analysis;
mod collect;
mod full;
mod lower;
mod models;
mod utils;

pub fn run(package: &Package, context: GlobalContext) -> CompileResult<()> {
    collect::run(package, context)?;
    analysis::run(package, context)?;
    full::run(package, context)?;
    Ok(())
}
