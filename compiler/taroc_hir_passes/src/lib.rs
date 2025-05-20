use taroc_error::CompileResult;
use taroc_sema::GlobalContext;

pub fn run(package: taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    taroc_resolve::run(&package, context)?;
    taroc_sema::passes::run(&package, context)?;
    context.diagnostics.report()
}
