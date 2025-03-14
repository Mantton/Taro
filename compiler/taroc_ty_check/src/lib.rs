#![feature(let_chains)]
use std::rc::Rc;
use taroc_context::CompilerSession;
use taroc_error::CompileResult;
use taroc_hir::Package;

mod collect;

pub fn run(package: &Package, session: Rc<CompilerSession>) -> CompileResult<()> {
    collect::run(package, session)?;
    Ok(())
}
