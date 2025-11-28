use crate::ast::{Identifier, NodeID, Variant, VariantKind};
use crate::compile::state::CompilerState;
use crate::sema::resolve::arena::ResolverArenas;
use crate::sema::resolve::models::ResolutionOutput;
use crate::sema::resolve::resolver::Resolver;
use crate::span::{FileID, Span};
use crate::{ast, error::CompileResult};
use ecow::EcoString;
use index_vec::define_index_type;
use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::RefCell;

mod arena;
mod define;
mod full;
pub mod models;
mod resolver;
mod tag;
mod usage;

pub fn resolve_package(
    package: &ast::Package,
    state: CompilerState,
) -> CompileResult<ResolutionOutput> {
    let arenas = ResolverArenas::default();
    let mut resolver = Resolver::new(&arenas, state);
    tag::tag_package_symbols(package, &mut resolver)?;
    define::define_package_symbols(package, &mut resolver)?;
    usage::resolve_usages(&mut resolver)?;
    full::resolve_package(package, &mut resolver)?;
    Ok(resolver.build_output())
}
