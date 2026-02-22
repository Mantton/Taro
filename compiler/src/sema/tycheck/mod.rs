use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir,
    sema::{
        models::{ConformanceWitness, InterfaceReference},
        resolve::models::TypeHead,
    },
};
use std::time::{Duration, Instant};

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

#[derive(Debug, Clone)]
pub struct TypecheckPhaseTiming {
    pub name: &'static str,
    pub duration: Duration,
}

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

pub fn typecheck_package_with_timings<'ctx>(
    package: &hir::Package,
    context: GlobalContext<'ctx>,
) -> CompileResult<(results::TypeCheckResults<'ctx>, Vec<TypecheckPhaseTiming>)> {
    let mut phase_timings = Vec::with_capacity(18);

    macro_rules! run_timed {
        ($name:literal, $expression:expr) => {{
            let started_at = Instant::now();
            let value = $expression;
            phase_timings.push(TypecheckPhaseTiming {
                name: $name,
                duration: started_at.elapsed(),
            });
            value
        }};
    }

    run_timed!(
        "sema.typecheck.collect.attributes",
        collect::attributes::run(package, context)
    )?; // Collect Attributes
    run_timed!(
        "sema.typecheck.collect.generics",
        collect::generics::run(package, context)
    )?; // Collect Generics Headers
    run_timed!(
        "sema.typecheck.collect.adt",
        collect::adt::run(package, context)
    )?; // Collect ADT Definitions
    run_timed!(
        "sema.typecheck.collect.interface.collect",
        collect::interface::collect::run(package, context)
    )?; // Collect Interface Definition
    run_timed!(
        "sema.typecheck.impls.identify",
        impls::identify::run(package, context)
    )?; // Resolve Impl Block Identities
    run_timed!(
        "sema.typecheck.collect.alias",
        collect::alias::run(package, context)
    )?; // Collect Type Aliases
    run_timed!(
        "sema.typecheck.collect.constant",
        collect::constant::run(package, context)
    )?; // Collect Constant Types
    run_timed!(
        "sema.typecheck.collect.constraints",
        collect::constraints::run(package, context)
    )?; // Collect Generic Constraints
    run_timed!(
        "sema.typecheck.impls.target",
        impls::target::run(package, context)
    )?; // Cache Impl Target Types
    run_timed!(
        "sema.typecheck.collect.function",
        collect::function::run(package, context)
    )?; // Collect Function Type Signatures
    run_timed!(
        "sema.typecheck.collect.variant",
        collect::variant::run(package, context)
    )?; // Collect Enum Variant Definitions
    run_timed!(
        "sema.typecheck.collect.field",
        collect::field::run(package, context)
    )?; // Collect ADT Type Definitions
    run_timed!(
        "sema.typecheck.collect.interface.requirements",
        collect::interface::requirements::run(package, context)
    )?; // Collect Interface Requirements
    run_timed!(
        "sema.typecheck.impls.member",
        impls::member::run(package, context)
    )?; // Collect Impl Block Members
    run_timed!(
        "sema.typecheck.collect.conformances",
        collect::conformances::run(package, context)
    )?; // Collect Conformances
    run_timed!(
        "sema.typecheck.collect.interface.conform",
        collect::interface::conform::run(package, context)
    )?; // Validate Conformances

    // WellFormed?
    run_timed!("sema.typecheck.wf", wf::run(package, context))?;
    // Check Body
    let results = run_timed!("sema.typecheck.check", check::run(package, context))?;
    Ok((results, phase_timings))
}
