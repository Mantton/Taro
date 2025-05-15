#![feature(let_chains)]
#![feature(if_let_guard)]
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::Package;

mod collect;
mod extend;
mod lower;
mod models;
mod utils;

pub fn run(package: &Package, context: GlobalContext) -> CompileResult<()> {
    collect::generics::run(package, context)?; // generics
    collect::header::run(package, context)?; // type headers
    collect::interface::collect::run(package, context)?; // interface definitions
    collect::interface::hierarchy::run(package, context)?; // build interace superset graph
    extend::identify::run(package, context)?; // extension identities
    extend::alias::run(package, context)?; // assoc types
    collect::constraints::run(package, context)?; // constraints
    collect::conformance::run(package, context)?; // conformances
    collect::fields::run(package, context)?; // adt fields
    collect::function::run(package, context)?; // function signatures
    extend::members::run(package, context)?; // assoc members
    Ok(())
}
