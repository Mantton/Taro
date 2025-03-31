#![feature(let_chains)]
#![feature(if_let_guard)]
use resolver::Resolver;
use taroc_context::GlobalContext;
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

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut r = Resolver::new(context);
    // Collection Stage
    tag::run(&package, &mut r);
    define::run(&package, &mut r)?;

    // Resolution Stage
    usage::run(&package, &mut r)?; // Imports & Exports Resolution
    full::run(&package, &mut r)?;
    let data = r.produce();

    // Cleanup
    context
        .store
        .resolutions
        .borrow_mut()
        .insert(context.session().package_index, data);

    Ok(())
}
