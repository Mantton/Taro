use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
};

mod checker;
mod gather;
mod node;

pub fn run(package: &hir::Package, context: Gcx) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: Gcx<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(package: &hir::Package, context: Gcx<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        hir::walk_package(&mut actor, package);
        context.dcx().ok()
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_function(
        &mut self,
        id: hir::DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) -> Self::Result {
        self.check_function(id, node, fn_ctx);
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_function(&self, id: DefinitionID, node: &hir::Function, fn_ctx: hir::FunctionContext) {
        let checker = checker::Checker::new(self.context);
        checker.check_function(id, node, fn_ctx);
    }
}
