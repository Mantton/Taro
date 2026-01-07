use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir,
    sema::{
        models::{ConformanceWitness, InterfaceReference},
        resolve::models::TypeHead,
    },
};

mod check;
mod collect;
pub mod constraints;
pub mod derive;
mod fold;
pub mod freshen;
mod impls;
pub mod infer;
pub mod lower;
pub mod results;
pub mod solve;
pub mod utils;
mod wf;

pub fn resolve_conformance_witness<'ctx>(
    context: GlobalContext<'ctx>,
    type_head: TypeHead,
    interface: InterfaceReference<'ctx>,
) -> Option<ConformanceWitness<'ctx>> {
    collect::interface::conform::resolve_conformance_witness(context, type_head, interface)
}

pub fn typecheck_package<'ctx>(
    package: &hir::Package,
    context: GlobalContext<'ctx>,
) -> CompileResult<results::TypeCheckResults<'ctx>> {
    collect::attributes::run(package, context)?; // Collect Attributes
    collect::generics::run(package, context)?; // Collect Generics Headers
    collect::adt::run(package, context)?; // Collect ADT Definitions
    collect::interface::collect::run(package, context)?; // Collect Interface Definition
    impls::identify::run(package, context)?; // Resolve Impl Block Identities
    collect::alias::run(package, context)?; // Collect Type Aliases
    collect::constant::run(package, context)?; // Collect Constant Types
    collect::constraints::run(package, context)?; // Collect Generic Constraints
    impls::target::run(package, context)?; // Cache Impl Target Types
    collect::function::run(package, context)?; // Collect Function Type Signatures
    collect::variant::run(package, context)?; // Collect Enum Variant Definitions
    collect::field::run(package, context)?; // Collect ADT Type Definitions
    collect::interface::requirements::run(package, context)?; // Collect Interface Requirements
    impls::member::run(package, context)?; // Collect Impl Block Members
    collect::conformances::run(package, context)?; // Collect Conformances
    collect::interface::conform::run(package, context)?; // Validate Conformances

    // WellFormed?
    wf::run(package, context)?;
    // Check Body
    let results = check::run(package, context)?;
    Ok(results)
}
