pub(crate) mod class_layout;
use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir,
    sema::models::{ConformanceWitness, Constraint, InterfaceReference, SelectionMode},
};
use std::time::{Duration, Instant};

mod check;
pub(crate) use check::{check_const_expr_on_demand, check_const_fn_on_demand};
mod collect;
pub(crate) use collect::adt::HeaderFields;
pub(crate) use collect::class_hierarchy::ensure_base as ensure_class_base;
pub(crate) use collect::conformances::{
    Header as ConformanceHeader, ensure_candidates as ensure_conformance_headers,
};
pub(crate) use collect::function::{InitializerHeader, find_decoder_header};
pub mod constraints;
pub mod derive;
pub(crate) mod fold;
mod impls;
pub mod infer;
pub mod lower;
pub(crate) mod opaque;
mod overloads;
pub mod results;
pub mod solve;
pub mod utils;
pub(crate) mod visit;
mod wf;

#[derive(Debug, Clone)]
pub struct TypecheckPhaseTiming {
    pub name: &'static str,
    pub duration: Duration,
}

const TYPECHECK_PHASE_COUNT: usize = 27;

pub fn resolve_conformance_witness<'ctx>(
    context: GlobalContext<'ctx>,
    interface: InterfaceReference<'ctx>,
) -> Option<ConformanceWitness<'ctx>> {
    collect::interface::conform::resolve_conformance_witness(context, interface)
}

pub fn resolve_conformance_witness_with_mode<'ctx>(
    context: GlobalContext<'ctx>,
    interface: InterfaceReference<'ctx>,
    mode: SelectionMode,
) -> Option<ConformanceWitness<'ctx>> {
    collect::interface::conform::resolve_conformance_witness_with_mode(context, interface, mode)
}

pub fn resolve_conformance_witness_with_param_env<'ctx>(
    context: GlobalContext<'ctx>,
    interface: InterfaceReference<'ctx>,
    param_env: &'ctx [Constraint<'ctx>],
) -> Option<ConformanceWitness<'ctx>> {
    collect::interface::conform::resolve_conformance_witness_with_param_env(
        context, interface, param_env,
    )
}

pub fn typecheck_package<'ctx>(
    package: &hir::Package,
    context: GlobalContext<'ctx>,
) -> CompileResult<results::TypeCheckResults<'ctx>> {
    let mut phase_timings = None;
    run_typecheck_pipeline(package, context, &mut phase_timings)
}

pub fn typecheck_package_with_timings<'ctx>(
    package: &hir::Package,
    context: GlobalContext<'ctx>,
) -> CompileResult<(results::TypeCheckResults<'ctx>, Vec<TypecheckPhaseTiming>)> {
    let mut phase_timings = Vec::with_capacity(TYPECHECK_PHASE_COUNT);
    let results = {
        let mut timings = Some(&mut phase_timings);
        run_typecheck_pipeline(package, context, &mut timings)?
    };
    Ok((results, phase_timings))
}

fn run_typecheck_pipeline<'ctx>(
    package: &hir::Package,
    context: GlobalContext<'ctx>,
    phase_timings: &mut Option<&mut Vec<TypecheckPhaseTiming>>,
) -> CompileResult<results::TypeCheckResults<'ctx>> {
    prepare_declarations(package, context, phase_timings)?;
    run_typecheck_phase(phase_timings, "sema.typecheck.check", || {
        check_prepared_bodies(package, context)
    })
}

/// Materialize the package-wide solver environment before checking bodies.
pub(crate) fn prepare_declarations<'ctx>(
    package: &hir::Package,
    context: GlobalContext<'ctx>,
    phase_timings: &mut Option<&mut Vec<TypecheckPhaseTiming>>,
) -> CompileResult<()> {
    run_typecheck_phase(phase_timings, "sema.typecheck.collect.attributes", || {
        collect::attributes::run(package, context)
    })?; // Collect Attributes
    run_typecheck_phase(
        phase_timings,
        "sema.typecheck.collect.constant_definitions",
        || collect::constant::register(package, context),
    )?; // Register constant definitions before compile-time values are consumed
    let parameter_owners =
        run_typecheck_phase(phase_timings, "sema.typecheck.collect.generics", || {
            collect::generics::run(package, context)
        })?; // Collect Generics Headers
    run_typecheck_phase(phase_timings, "sema.typecheck.collect.adt", || {
        collect::adt::run(package, context)
    })?; // Collect ADT Definitions
    run_typecheck_phase(
        phase_timings,
        "sema.typecheck.collect.interface_alias",
        || collect::interface_alias::run(package, context),
    )?; // Expand interface-set aliases before any interface positions are lowered
    run_typecheck_phase(
        phase_timings,
        "sema.typecheck.collect.interface.collect",
        || collect::interface::collect::run(package, context),
    )?; // Collect Interface Definition
    run_typecheck_phase(phase_timings, "sema.typecheck.impls.identify", || {
        impls::identify::run(package, context)
    })?; // Resolve Impl Block Identities
    let aliases = run_typecheck_phase(
        phase_timings,
        "sema.typecheck.collect.alias_headers",
        || collect::alias::register(package, context),
    )?;
    let conformances = collect::conformances::register(package, context);
    run_typecheck_phase(phase_timings, "sema.typecheck.collect.constraints", || {
        collect::constraints::run(package, context)
    })?; // Collect Generic Constraints
    run_typecheck_phase(phase_timings, "sema.typecheck.impls.target", || {
        impls::target::run(package, context)
    })?; // Cache Impl Target Types
    run_typecheck_phase(phase_timings, "sema.typecheck.collect.conformances", || {
        collect::conformances::finish(conformances, context)
    })?;
    collect::class_hierarchy::finish_bases(context)?;
    run_typecheck_phase(phase_timings, "sema.typecheck.collect.alias", || {
        collect::alias::resolve(aliases, context)
    })?;
    run_typecheck_phase(
        phase_timings,
        "sema.typecheck.collect.generic_defaults",
        || collect::generics::collect_defaults(parameter_owners, context),
    )?;
    run_typecheck_phase(
        phase_timings,
        "sema.typecheck.collect.static_variable",
        || collect::static_variable::run(package, context),
    )?; // Collect Static Variable Types
    run_typecheck_phase(phase_timings, "sema.typecheck.collect.function", || {
        collect::function::run(package, context)
    })?; // Collect Function Type Signatures
    collect::subscript::run(package, context);
    run_typecheck_phase(phase_timings, "sema.typecheck.collect.variant", || {
        collect::variant::run(package, context)
    })?; // Collect Enum Variant Definitions
    run_typecheck_phase(phase_timings, "sema.typecheck.collect.constant", || {
        collect::constant::run(package, context)
    })?;
    run_typecheck_phase(phase_timings, "sema.typecheck.collect.field", || {
        collect::field::run(package, context)
    })?; // Collect ADT Type Definitions
    run_typecheck_phase(
        phase_timings,
        "sema.typecheck.collect.interface.requirements",
        || collect::interface::requirements::run(package, context),
    )?; // Collect Interface Requirements
    run_typecheck_phase(phase_timings, "sema.typecheck.collect.lifecycle", || {
        collect::lifecycle::register(package, context)
    })?;
    run_typecheck_phase(phase_timings, "sema.typecheck.impls.member", || {
        impls::member::run(package, context)
    })?; // Collect Impl Block Members
    context.store.collecting_constant_headers.set(false);
    context.store.header_fields.take();
    context.store.decoder_headers.take();
    // Header queries precede complete field layouts and member signatures.
    context.with_session_type_database(|db| {
        db.selection_cache.clear();
        db.witness_cache.clear();
    });
    impls::delegation::register(package, context)?;
    crate::sema::lowering::class_codable::prepare(context)?;
    run_typecheck_phase(
        phase_timings,
        "sema.typecheck.impls.class_adoptions",
        || impls::class_adoptions::run(package, context),
    )?;
    run_typecheck_phase(phase_timings, "sema.typecheck.impls.classes", || {
        impls::classes::run(package, context)
    })?;
    impls::class_adoptions::refresh(context);
    run_typecheck_phase(phase_timings, "sema.typecheck.impls.initializers", || {
        impls::initializers::run(package, context)
    })?;
    crate::sema::lowering::class_codable::validate(context)?;
    run_typecheck_phase(
        phase_timings,
        "sema.typecheck.collect.interface.conform",
        || collect::interface::conform::run(package, context),
    )?; // Validate Conformances

    run_typecheck_phase(
        phase_timings,
        "sema.typecheck.collect.constant_values",
        || collect::constant::collect_values(package, context),
    )?;
    // WellFormed?
    run_typecheck_phase(phase_timings, "sema.typecheck.wf", || {
        wf::run(package, context)
    })?;
    run_typecheck_phase(
        phase_timings,
        "sema.typecheck.cache_default_signatures",
        || {
            crate::sema::lowering::class_defaults::cache_provider_signatures(context);
            Ok(())
        },
    )
}

/// Use the regular checker and its body validators on a selected HIR
/// projection. Its headers must already have been prepared in this context.
pub(crate) fn check_prepared_bodies<'ctx>(
    package: &hir::Package,
    context: GlobalContext<'ctx>,
) -> CompileResult<results::TypeCheckResults<'ctx>> {
    check::run(package, context)
}

fn run_typecheck_phase<R>(
    phase_timings: &mut Option<&mut Vec<TypecheckPhaseTiming>>,
    name: &'static str,
    phase: impl FnOnce() -> CompileResult<R>,
) -> CompileResult<R> {
    let started_at = Instant::now();
    let value = phase();
    if let Some(phase_timings) = phase_timings.as_deref_mut() {
        phase_timings.push(TypecheckPhaseTiming {
            name,
            duration: started_at.elapsed(),
        });
    }
    value
}
