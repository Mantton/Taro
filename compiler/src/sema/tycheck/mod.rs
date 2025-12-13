use crate::{compile::context::GlobalContext, error::CompileResult, hir};

mod check;
mod collect;
mod extend;
mod fold;
pub mod infer;
mod lower;
mod solve;
mod wf;

pub fn typecheck_package(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    collect::adt::run(package, context)?; // Collect ADT Type Headers
    collect::field::run(package, context)?; // Collect ADT Type Definitions
    extend::identify::run(package, context)?; // Resolve Extension Identities
    collect::function::run(package, context)?; // Collect Function Type Signatures
    extend::member::run(package, context)?; // Collect Extension Members
    // WellFormed?
    wf::run(package, context)?;
    // Check Body
    check::run(package, context)?;
    Ok(())
}
