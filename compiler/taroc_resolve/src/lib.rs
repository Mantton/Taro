#![feature(let_chains)]
#![feature(if_let_guard)]
use resolver::Resolver;
use std::rc::Rc;
use taroc_context::CompilerSession;
use taroc_error::CompileResult;
mod arena;
mod define;
mod find;
mod full;
mod models;
mod paths;
mod resolver;
mod tag;
mod usage;

pub fn run(package: &taroc_hir::Package, session: Rc<CompilerSession>) -> CompileResult<()> {
    let mut r = Resolver::new(session.clone());
    // Collection Stage
    tag::run(&package, &mut r);
    define::run(&package, &mut r)?;

    // Resolution Stage
    usage::run(&package, &mut r)?; // Imports & Exports Resolution
    full::run(&package, &mut r)?;
    let data = r.produce();

    // Cleanup
    session
        .context
        .store
        .resolutions
        .borrow_mut()
        .insert(session.index, data);

    Ok(())
}
