use crate::compile::context::GlobalContext;
use crate::sema::resolve::arena::ResolverArenas;
use crate::sema::resolve::models::ResolutionOutput;
use crate::sema::resolve::resolver::Resolver;
use crate::{ast, error::CompileResult};

mod arena;
mod define;
mod full;
pub mod models;
mod resolver;
mod tag;
mod usage;

pub fn resolve_package(
    package: &ast::Package,
    gcx: GlobalContext,
) -> CompileResult<ResolutionOutput> {
    let arenas = ResolverArenas::default();
    let mut resolver = Resolver::new(&arenas, gcx);
    tag::tag_package_symbols(package, &mut resolver)?;
    define::define_package_symbols(package, &mut resolver)?;
    usage::resolve_usages(&mut resolver)?;
    full::resolve_package(package, &mut resolver)?;
    Ok(resolver.build_output())
}
