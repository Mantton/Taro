use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::visitor::HirVisitor;

use crate::lower::{ItemCtx, LoweringRequest, TypeLowerer};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package);
        context.diagnostics.report()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_field_definition(&mut self, f: &taroc_hir::FieldDefinition) -> Self::Result {
        let icx = ItemCtx::new(self.context);
        let _ = icx.lowerer().lower_type(&f.ty, &LoweringRequest::default());
    }
}
