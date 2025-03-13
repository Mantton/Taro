use taroc_context::GlobalContext;
use taroc_error::CompileResult;

pub fn run(package: taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    taroc_resolve::run(package, context)?;
    context.diagnostics.report()
}
