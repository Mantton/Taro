//! Publish checked source bodies through the canonical GC and instance pipelines.

// The class-construction kernel still has GC-promoted temporaries, but MCJIT
// does not register its production stack maps. It is not a source/GC activation
// test. Do not let a separate whole-process collection fixture reclaim that
// kernel's live temporaries. Production stack-map/stress tests run separately.
pub(super) static GC_TEST_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

use super::*;
pub(super) fn publish<'ctx>(
    gcx: Gcx<'ctx>,
    bodies: Vec<(hir::DefinitionID, mir::Body<'ctx>)>,
) -> &'ctx mir::MirPackage<'ctx> {
    let mut pending = std::collections::VecDeque::from(bodies);
    let mut functions = FxHashMap::default();
    while let Some((id, mut body)) = pending.pop_front() {
        mir::optimize::lower_async_for_canonical_mir(gcx, &mut body)
            .unwrap_or_else(|_| panic!("canonical: {:#?}", gcx.dcx().take_recorded_diagnostics()));
        functions.insert(id, &*gcx.store.arenas.mir_bodies.alloc(body));
        for (id, mut queued) in gcx.take_queued_mir_bodies() {
            mir::optimize::run_local_passes(gcx, &mut queued)
                .unwrap_or_else(|_| panic!("queued: {:#?}", gcx.dcx().take_recorded_diagnostics()));
            pending.push_back((id, queued));
        }
    }
    let canonical = gcx.store.alloc_mir_package(mir::MirPackage {
        functions,
        entry: None,
    });
    gcx.store
        .inline_mir_packages
        .borrow_mut()
        .insert(gcx.package_index(), canonical);
    let mut functions = FxHashMap::default();
    for (&id, body) in &canonical.functions {
        let mut body = (*body).clone();
        mir::optimize::run_global_passes(gcx, &mut body)
            .unwrap_or_else(|_| panic!("global: {:#?}", gcx.dcx().take_recorded_diagnostics()));
        functions.insert(id, &*gcx.store.arenas.mir_bodies.alloc(body));
    }
    let package = gcx.store.alloc_mir_package(mir::MirPackage {
        functions,
        entry: None,
    });
    gcx.store
        .mir_packages
        .borrow_mut()
        .insert(gcx.package_index(), package);
    crate::specialize::collect::collect_instances(package, gcx)
        .unwrap_or_else(|_| panic!("instances: {:#?}", gcx.dcx().take_recorded_diagnostics()));
    package
}
