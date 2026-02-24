use crate::{
    compile::context::GlobalContext, error::CompileResult, hir,
    sema::tycheck::results::TypeCheckResults,
};

mod printf;

pub fn validate_package(_package: &hir::Package, _gcx: GlobalContext) -> CompileResult<()> {
    // Intentionally a no-op for now.
    // Pre-typecheck validation rules should only be added here if they can run
    // purely on HIR shape without requiring type inference results.
    _gcx.dcx().ok()
}

pub fn validate_post_typecheck<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
    results: &TypeCheckResults<'ctx>,
) -> CompileResult<()> {
    printf::run(package, gcx, results)?;
    gcx.dcx().ok()
}
