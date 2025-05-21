use taroc_error::CompileResult;

use crate::GlobalContext;

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    super::collect::generics::run(package, context)?; // generics
    super::collect::header::run(package, context)?; // type headers
    super::collect::interface::collect::run(package, context)?; // interface definitions
    super::collect::interface::hierarchy::run(package, context)?; // build interace superinterface graph
    super::extend::identify::run(package, context)?; // extension identities
    super::extend::alias::run(package, context)?; // assoc types
    super::collect::constraints::run(package, context)?; // constraints
    super::collect::conformance::run(package, context)?; // conformances
    super::collect::function::run(package, context)?; // function signatures
    super::extend::members::run(package, context)?; // assoc members
    super::collect::fields::run(package, context)?; // adt fields
    // TODO: Validate Interface Conformance
    // TODO: Check Recursive Types
    Ok(())
}
