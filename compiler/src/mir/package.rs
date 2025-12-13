use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::DefinitionID,
    mir::{MirPackage, builder::MirBuilder},
    thir,
};
use rustc_hash::FxHashMap;

pub fn build_package<'ctx>(
    package: thir::ThirPackage<'ctx>,
    gcx: GlobalContext<'ctx>,
) -> CompileResult<&'ctx MirPackage<'ctx>> {
    let mut functions: FxHashMap<DefinitionID, &'ctx crate::mir::Body<'ctx>> = FxHashMap::default();

    for (id, func) in package.functions {
        let body = MirBuilder::build_function(gcx, &func);
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
    Ok(pkg)
}
