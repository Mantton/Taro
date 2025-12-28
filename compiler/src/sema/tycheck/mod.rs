use crate::{compile::context::GlobalContext, error::CompileResult, hir};

mod check;
mod collect;
mod extend;
mod fold;
pub mod infer;
mod lower;
pub mod results;
pub mod solve;
pub mod utils;
mod wf;

pub fn typecheck_package<'ctx>(
    package: &hir::Package,
    context: GlobalContext<'ctx>,
) -> CompileResult<results::TypeCheckResults<'ctx>> {
    collect::attributes::run(package, context)?; // Collect Attributes
    collect::generics::run(package, context)?; // Collect Generics Headers
    collect::adt::run(package, context)?; // Collect ADT Definitions
    collect::interface::collect::run(package, context)?; // Collect Interface Definition
    collect::field::run(package, context)?; // Collect ADT Type Definitions
    collect::variant::run(package, context)?; // Collect Enum Variant Definitions
    extend::identify::run(package, context)?; // Resolve Extension Identities
    collect::function::run(package, context)?; // Collect Function Type Signatures
    collect::interface::requirements::run(package, context)?; // Collect Interface Requirements
    extend::member::run(package, context)?; // Collect Extension Members
    collect::conformances::run(package, context)?; // Collect Conformances
    // WellFormed?
    wf::run(package, context)?;
    // Check Body
    let results = check::run(package, context)?;
    Ok(results)
}
