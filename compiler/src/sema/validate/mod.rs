use crate::{
    compile::context::GlobalContext, error::CompileResult, hir,
    sema::tycheck::results::TypeCheckResults,
};

mod printf;

pub fn validate_post_typecheck<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
    results: &TypeCheckResults<'ctx>,
) -> CompileResult<()> {
    printf::run(package, gcx, results)?;
    gcx.dcx().ok()
}
