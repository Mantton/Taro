use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    mir::builder::MirBuilder,
};
use rustc_hash::FxHashMap;

#[derive(Debug, Default)]
pub struct MirPackage<'ctx> {
    pub functions: FxHashMap<DefinitionID, &'ctx crate::mir::Body<'ctx>>,
}

pub fn build_package(package: &hir::Package, gcx: GlobalContext<'_>) -> CompileResult<()> {
    Actor::run(package, gcx)
}

struct Actor<'ctx> {
    gcx: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(gcx: GlobalContext<'ctx>) -> Self {
        Actor { gcx }
    }

    fn run(package: &hir::Package, gcx: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(gcx);
        hir::walk_package(&mut actor, package);
        gcx.dcx().ok()
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
        self.gcx.cache_mir_body(id, body);
        hir::walk_function(self, id, node, fn_ctx);
    }
}
