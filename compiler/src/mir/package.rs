use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::DefinitionID,
    mir::{MirPackage, builder::MirBuilder, optimize},
    thir,
};
use rustc_hash::FxHashMap;

pub fn build_package<'ctx>(
    package: thir::ThirPackage<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> CompileResult<&'ctx MirPackage<'ctx>> {
    let mut functions: FxHashMap<DefinitionID, &'ctx crate::mir::Body<'ctx>> = FxHashMap::default();

    for (id, func) in package.functions {
        if func.body.is_none() {
            continue;
        }
        let mut body = MirBuilder::build_function(gcx, &func);
        optimize::run_default_passes(gcx, &mut body);

        // Validate mutable borrows
        super::validate::validate_mutability(gcx, &body)?;

        // Validate use-after-move
        super::validate::validate_moves(gcx, &body)?;

        // let ident = gcx.definition_ident(id);
        // println!("{} MIR", ident.symbol);
        // println!("{}", super::pretty::PrettyPrintMir { body: &body, gcx });
        let alloc = gcx.store.arenas.mir_bodies.alloc(body);
        functions.insert(id, alloc);
    }
    
    // Check if synthetic IDs are present

    let mut pkg = MirPackage::default();
    pkg.functions = functions;
    pkg.entry = package.entry;
    let pkg = gcx.store.alloc_mir_package(pkg);
    gcx.store
        .mir_packages
        .borrow_mut()
        .insert(gcx.package_index(), pkg);
    Ok(pkg)
}
