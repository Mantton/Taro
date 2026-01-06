use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::DefinitionID,
    mir::{Body, MirPackage, builder::MirBuilder, optimize, pretty::PrettyPrintMir},
    thir,
};
use rustc_hash::FxHashMap;

pub fn build_package<'ctx>(
    package: thir::ThirPackage<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> CompileResult<&'ctx MirPackage<'ctx>> {
    // Phase 1: Build MIR for all functions and run local passes
    // Local passes (prune, simplify, validate) don't need other function bodies
    let mut bodies: FxHashMap<DefinitionID, Body<'ctx>> = FxHashMap::default();

    for (id, func) in package.functions {
        if func.body.is_none() {
            continue;
        }
        let mut body = MirBuilder::build_function(gcx, &func);
        
        // Run local passes (prune, simplify, validate)
        optimize::run_local_passes(gcx, &mut body)?;
        
        bodies.insert(id, body);
    }

    // Store the package early so inlining can find callee bodies
    let mut functions: FxHashMap<DefinitionID, &'ctx Body<'ctx>> = FxHashMap::default();
    for (id, body) in bodies {
        let alloc = gcx.store.arenas.mir_bodies.alloc(body);
        functions.insert(id, alloc);
    }

    let mut pkg = MirPackage::default();
    pkg.functions = functions;
    pkg.entry = package.entry;
    let pkg = gcx.store.alloc_mir_package(pkg);
    gcx.store
        .mir_packages
        .borrow_mut()
        .insert(gcx.package_index(), pkg);

    // Phase 2: Run global passes (inlining, lowering, escape analysis, safepoints)
    // These passes need access to other function bodies
    let mut final_functions: FxHashMap<DefinitionID, &'ctx Body<'ctx>> = FxHashMap::default();
    for def_id in pkg.functions.keys().copied().collect::<Vec<_>>() {
        let body_ref = pkg.functions.get(&def_id).unwrap();
        let mut body = (*body_ref).clone();
        
        optimize::run_global_passes(gcx, &mut body)?;
        
        let alloc = gcx.store.arenas.mir_bodies.alloc(body);
        final_functions.insert(def_id, alloc);
    }

    let mut final_pkg = MirPackage::default();
    final_pkg.functions = final_functions;
    final_pkg.entry = package.entry;
    let final_pkg = gcx.store.alloc_mir_package(final_pkg);
    
    // Update the stored package with the fully optimized version
    gcx.store
        .mir_packages
        .borrow_mut()
        .insert(gcx.package_index(), final_pkg);

    if gcx.config.debug.dump_mir {
        eprintln!("\n=== MIR Dump for {} ===", gcx.config.name);
        for (def_id, body) in final_pkg.functions.iter() {
            let ident = gcx.definition_ident(*def_id);
            eprintln!("\nfn {}() {{", ident.symbol);
            let pretty = PrettyPrintMir { body, gcx };
            eprintln!("{}", pretty);
            eprintln!("}}");
        }
        eprintln!("=== End MIR Dump ===\n");
    }

    Ok(final_pkg)
}
