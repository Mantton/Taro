#![feature(let_chains)]
#![feature(if_let_guard)]
use arena::ResolverArena;
use resolver::Resolver;
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_resolve_models::ResolverOutput;
mod arena;
mod define;
mod find;
mod full;
mod models;
mod paths;
mod resolver;
mod tag;
mod usage;

pub fn run(package: taroc_hir::Package, context: GlobalContext) -> CompileResult<ResolverOutput> {
    let arena = ResolverArena::new();
    let mut r = Resolver::new(context, &arena);
    // Collection Stage
    tag::run(&package, &mut r);
    define::run(&package, &mut r)?;

    // Resolution Stage
    usage::run(&package, &mut r)?; // Imports & Exports Resolution
    full::run(&package, &mut r)?;
    let output = r.produce();

    Ok(output)
}
