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
    collect::function::run(package, context)?; // Collect Function Type Signatures
    extend::identify::run(package, context)?; // Resolve Extension Identities
    // WellFormed?
    wf::run(package, context)?;
    // Check Body
    check::run(package, context)?;
    Ok(())
}
