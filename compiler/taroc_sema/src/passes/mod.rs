use taroc_error::CompileResult;

use crate::GlobalContext;

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    super::extend::identify::run(package, context)?; // extension identities
    super::collect::generics::run(package, context)?; // generics
    super::collect::header::run(package, context)?; // type headers
    super::collect::interface::collect::run(package, context)?; // interface definitions
    super::collect::interface::hierarchy::run(package, context)?; // build interace superinterface graph
    super::extend::alias::run(package, context)?; // assoc types
    super::collect::constraints::run(package, context)?; // constraints
    super::collect::conformance::run(package, context)?; // conformances
    super::collect::function::run(package, context)?; // function signatures
    super::extend::table::run(package, context)?; // assoc members and overload table generation
    super::collect::fields::run(package, context)?; // adt fields
    super::collect::interface::requirements::run(package, context)?; // interface requirements
    super::collect::interface::conformance::run(context)?; // validate interface conformance
    super::recursive::types::run(package, context)?; // recursive types
    super::check::run(package, context)?;
    Ok(())
}
