#![feature(let_chains)]
use std::rc::Rc;
use taroc_context::CompilerSession;
use taroc_error::CompileResult;
use taroc_hir::Package;

mod collect;
mod lower;

pub fn run(package: &Package, session: Rc<CompilerSession>) -> CompileResult<()> {
    collect::run(package, session)?;
    Ok(())
}
