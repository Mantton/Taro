use taroc_error::CompileResult;
use taroc_sema::GlobalContext;

pub fn run<'ctx>(
    package: &taroc_hir::Package,
    context: GlobalContext<'ctx>,
) -> CompileResult<taroc_thir::Package<'ctx>> {
    taroc_resolve::run(package, context)?;
    taroc_sema::passes::run(package, context)?;
    taroc_thir_build::run(&package, context)
}
