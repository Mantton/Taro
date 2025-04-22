use taroc_context::GlobalContext;
use taroc_error::CompileResult;

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    FullChecker::run(package, context)?;
    context.diagnostics.report()
}

struct FullChecker<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> FullChecker<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> FullChecker<'ctx> {
        FullChecker { context }
    }

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = FullChecker::new(context);
        context.diagnostics.report()
    }
}
