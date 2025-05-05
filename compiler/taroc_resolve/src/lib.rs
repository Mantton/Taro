#![feature(let_chains)]
#![feature(if_let_guard)]
use define::DefinitionCollector;
use iterative::IterativeResolver;
use resolver::Resolver;
use tag::HirNodeTagger;
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
mod alias;
mod arena;
mod define;
mod extend;
mod find;
mod full;
mod iterative;
mod models;
mod resolver;
mod tag;
mod usage;

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    // Create Resolver
    let mut r = Resolver::new(context);
    // Collection Phase
    HirNodeTagger::run(&package, &mut r);
    DefinitionCollector::run(&package, &mut r)?; // Collect Definitions

    // Resolution Phase
    IterativeResolver::run(&mut r)?; // Using an Iterative Fixed-Point Approach Perform Import Resolution, Extension Binding & Type Alias resolution
    // full::run(&package, &mut r)?;
    let data = r.produce();

    // Cleanup
    context
        .store
        .resolutions
        .borrow_mut()
        .insert(context.session().package_index, data);

    Ok(())
}
