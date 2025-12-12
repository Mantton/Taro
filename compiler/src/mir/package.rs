use crate::{
    compile::{context::GlobalContext, entry::validate_entry_point},
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    mir::{MirPackage, builder::MirBuilder},
};
use rustc_hash::FxHashMap;

pub fn build_package<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
) -> CompileResult<&'ctx MirPackage<'ctx>> {
    let entry = validate_entry_point(&package, gcx)?;
    let package = Actor::run(package, gcx, entry)?;
    let package = gcx.store.alloc_mir_package(package);
    gcx.store
        .mir_packages
        .borrow_mut()
        .insert(gcx.package_index(), package);
    Ok(package)
}

struct Actor<'ctx> {
    gcx: GlobalContext<'ctx>,
    functions: FxHashMap<DefinitionID, &'ctx crate::mir::Body<'ctx>>,
    entry: Option<DefinitionID>,
}

impl<'ctx> Actor<'ctx> {
    fn new(gcx: GlobalContext<'ctx>, entry: Option<DefinitionID>) -> Self {
        Actor {
            gcx,
            functions: FxHashMap::default(),
            entry,
        }
    }

    fn run(
        package: &hir::Package,
        gcx: GlobalContext<'ctx>,
        entry: Option<DefinitionID>,
    ) -> CompileResult<MirPackage<'ctx>> {
        let mut actor = Actor::new(gcx, entry);
        hir::walk_package(&mut actor, package);
        let mut pkg = MirPackage::default();
        pkg.functions = actor.functions;
        pkg.entry = actor.entry;
        gcx.dcx().ok()?;
        Ok(pkg)
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) -> Self::Result {
        let body = MirBuilder::build_function(self.gcx, id, node);
        let alloc = self.gcx.store.arenas.mir_bodies.alloc(body);
        self.functions.insert(id, alloc);
        hir::walk_function(self, id, node, fn_ctx);
    }
}
