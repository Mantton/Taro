use crate::{
    compile::context::GlobalContext,
    hir::{self, DefinitionID},
    mir::Body,
    sema::{models::GenericArguments, tycheck::utils::instantiate::instantiate_generic_args},
    specialize::{Instance, resolve_instance},
};
use rustc_hash::FxHashSet;

/// Collects all function instantiations needed for a MIR package.
///
/// Implements a reachability analysis:
/// 1. Start with concrete entry points (roots)
/// 2. Scan each instance's MIR for generic calls
/// 3. Add discovered instantiations to worklist
/// 4. Repeat until fixpoint
pub fn collect_instances<'ctx>(
    package: &crate::mir::MirPackage<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> crate::error::CompileResult<()> {
    let mut collector = Collector {
        gcx,
        items: FxHashSet::default(),
        worklist: Vec::new(),
    };

    // 1. Find roots: concrete entry points
    collector.find_roots(package);

    // 2. Worklist algorithm: visit each instance, discover calls
    while let Some(instance) = collector.worklist.pop() {
        // Do not instantiate placeholder types after a prior specialization
        // reported a source error (notably unbound erased associated storage).
        gcx.dcx().ok()?;
        // Get the MIR body for this function.
        let def_id = instance.def_id();

        if instance.is_item()
            && matches!(
                crate::sema::lowering::erased_opening::plan(gcx, def_id, instance.args()),
                Ok(Some(_))
            )
        {
            // This instance is the erased bridge ABI, never the generic body
            // instantiated with an owning container as its concrete T.
            gcx.store
                .erased_opening_calls
                .borrow_mut()
                .entry(gcx.package_index())
                .or_default()
                .insert(instance);
            continue;
        }

        if gcx.is_instance_generated(def_id) {
            let body = gcx.get_instance_mir_body(instance)?;
            validate_instance_types(gcx, instance, body)?;
            // These calls are already concrete. Even nongeneric cleanup hooks
            // must be discovered when the thunk's owning package is imported.
            crate::mir::for_each_function_constant_in_body(body, |callee, args| {
                let target = resolve_instance(gcx, callee, args);
                if target.is_item() {
                    collector.enqueue(target);
                }
            });
            continue;
        }

        // Skip intrinsic functions - they don't have MIR bodies and are
        // handled specially during codegen via try_lower_intrinsic_call.
        if collector.is_intrinsic(def_id) {
            continue;
        }

        // Skip abstract interface methods that couldn't be devirtualized.
        // This happens when default interface method bodies reference other
        // interface methods with still-generic Self types.
        let Some(body) = collector.mir_body(def_id) else {
            continue;
        };
        validate_instance_types(gcx, instance, body)?;
        collector.visit_body(instance, body);
    }

    gcx.dcx().ok()?;
    gcx.cache_specializations(gcx.package_index(), collector.items);
    Ok(())
}

pub struct Collector<'ctx> {
    gcx: GlobalContext<'ctx>,
    /// Discovered instances
    items: FxHashSet<Instance<'ctx>>,
    /// Worklist for graph traversal
    worklist: Vec<Instance<'ctx>>,
}

/// Validate substituted storage before inlining or layout. Reference results
/// still require a known ABI for their associated type.
pub(crate) fn validate_instance_types<'ctx>(
    gcx: GlobalContext<'ctx>,
    instance: Instance<'ctx>,
    body: &Body<'ctx>,
) -> crate::error::CompileResult<()> {
    crate::mir::analysis::class_self::validate_instance(gcx, instance.def_id(), instance.args())?;
    use crate::sema::tycheck::utils::{
        instantiate::instantiate_ty_with_args, try_normalize_post_monomorphization,
        unresolved::storage_needs_substitution,
    };
    let mut seen = FxHashSet::default();
    for local in &body.locals {
        let ty = instantiate_ty_with_args(gcx, local.ty, instance.args());
        if seen.insert(ty) && !storage_needs_substitution(gcx, ty) {
            let normalized = try_normalize_post_monomorphization(gcx, ty).map_err(|error| {
                gcx.dcx().emit_error(error.format(gcx), Some(local.span));
                crate::error::ReportedError
            })?;
            crate::sema::tycheck::utils::atomic_handle::validate(gcx, normalized, local.span)?;
        }
    }
    Ok(())
}

impl<'ctx> Collector<'ctx> {
    fn enqueue(&mut self, instance: Instance<'ctx>) {
        if self.items.insert(instance) {
            self.worklist.push(instance);
        }
    }

    /// Find concrete entry points (roots of the reachability graph).
    fn find_roots(&mut self, package: &crate::mir::MirPackage<'ctx>) {
        // Add the entry point if it exists and is concrete
        if let Some(entry_id) = package.entry {
            let generics = self.gcx.generics_of(entry_id);
            if generics.is_empty() {
                let root = Instance::item(entry_id, GenericArguments::empty());
                self.enqueue(root);
            }
        }

        // Add all other concrete (non-generic) functions
        for &def_id in package.functions.keys() {
            // Nested closure bodies are instantiated from the closure value's
            // captured generics at use sites. Treating them as zero-arg roots
            // leaks raw parent type parameters into codegen.
            if self.gcx.get_closure_captures(def_id).is_some() {
                continue;
            }
            let generics = self.gcx.generics_of(def_id);
            if generics.is_empty() {
                let root = Instance::item(def_id, GenericArguments::empty());
                self.enqueue(root);
            }
        }
    }

    /// Visit a body and discover generic calls.
    fn visit_body(&mut self, parent: Instance<'ctx>, body: &Body<'ctx>) {
        crate::mir::for_each_function_constant_in_body(body, |callee_id, call_args| {
            // Only process if there are generic arguments
            if !call_args.is_empty() {
                // Substitute parent's types into the call's arguments
                let concrete_args = instantiate_generic_args(self.gcx, call_args, parent.args());

                // Compute the instantiation key
                let instance = resolve_instance(self.gcx, callee_id, concrete_args);
                if instance.is_item() {
                    self.enqueue(instance);
                }
            }
        });
    }

    fn mir_body(&self, def_id: DefinitionID) -> Option<&'ctx Body<'ctx>> {
        let packages = self.gcx.store.mir_packages.borrow();
        let package = *packages
            .get(&def_id.package())
            .expect("mir package for definition");
        package.functions.get(&def_id).cloned()
    }

    /// Check if a function is an intrinsic (has no MIR body).
    fn is_intrinsic(&self, def_id: DefinitionID) -> bool {
        matches!(
            self.gcx.get_signature(def_id).abi,
            Some(hir::Abi::Intrinsic)
        )
    }
}
