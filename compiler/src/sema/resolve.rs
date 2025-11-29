use crate::compile::context::GlobalContext;
use crate::sema::resolve::models::ResolutionOutput;
use crate::sema::resolve::resolver::Resolver;
use crate::{ast, error::CompileResult};

mod define;
mod full;
pub mod models;
mod resolver;
mod tag;
mod usage;

pub fn resolve_package<'a>(
    package: &ast::Package,
    gcx: GlobalContext<'a>,
) -> CompileResult<ResolutionOutput<'a>> {
    let mut resolver = Resolver::new(gcx);
    tag::tag_package_symbols(package, &mut resolver)?;
    define::define_package_symbols(package, &mut resolver)?;
    usage::resolve_usages(&mut resolver)?;
    full::resolve_package(package, &mut resolver)?;
    Ok(resolver.build_output())
}
