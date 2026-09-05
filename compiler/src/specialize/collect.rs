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
pub fn collect_instances<'ctx>(package: &crate::mir::MirPackage<'ctx>, gcx: GlobalContext<'ctx>) {
    let mut collector = Collector {
        gcx,
        items: FxHashSet::default(),
        worklist: Vec::new(),
    };

    // 1. Find roots: concrete entry points
    collector.find_roots(package);

    // 2. Worklist algorithm: visit each instance, discover calls
    while let Some(instance) = collector.worklist.pop() {
        // Get the MIR body for this function.
        let def_id = instance.def_id();

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
        collector.visit_body(instance, body);
    }

    gcx.cache_specializations(gcx.package_index(), collector.items);
}

pub struct Collector<'ctx> {
    gcx: GlobalContext<'ctx>,
    /// Discovered instances
    items: FxHashSet<Instance<'ctx>>,
    /// Worklist for graph traversal
    worklist: Vec<Instance<'ctx>>,
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
