#![feature(let_chains)]
#![feature(if_let_guard)]
use define::DefinitionCollector;
use generics::GenericsCollector;
use resolver::Resolver;
use tag::HirNodeTagger;
use taroc_error::CompileResult;
use taroc_sema::GlobalContext;
use usage::UsageResolver;
mod arena;
mod define;
mod find;
mod full;
mod generics;
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
    GenericsCollector::run(package, &mut r)?; // Collect Generics

    // Resolution Phase
    UsageResolver::run(&mut r)?;
    full::run(&package, &mut r)?;

    // Store Resolutions
    let data = r.produce();
    context
        .store
        .resolutions
        .borrow_mut()
        .insert(context.session().index(), data);

    Ok(())
}
