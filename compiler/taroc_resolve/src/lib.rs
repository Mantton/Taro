#![feature(let_chains)]
#![feature(if_let_guard)]
use define::DefinitionCollector;
use full::GenericsCollector;
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
    let mut r = Resolver::new(context);
    HirNodeTagger::run(&package, &mut r);
    DefinitionCollector::run(&package, &mut r)?; // Defines Symbols and their names spaces
    GenericsCollector::run(&package, &mut r)?;
    // Resolution Stage
    IterativeResolver::run(&mut r)?; // Using an Iterative Fixed-Point Approach Perform Import Resolution, Extension Binding & Type Alias resolution
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
