use taroc_context::GlobalContext;
use taroc_error::CompileResult;

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    TypeChecker::run(package, context)?;
    context.diagnostics.report()
}

struct TypeChecker<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> TypeChecker<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> TypeChecker<'ctx> {
        TypeChecker { context }
    }

    fn run<'a>(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = TypeChecker::new(context);
        context.diagnostics.report()
    }
}
