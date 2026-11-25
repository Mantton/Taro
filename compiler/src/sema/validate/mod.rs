use crate::{
    compile::context::GlobalContext, error::CompileResult, hir,
    sema::tycheck::results::TypeCheckResults,
};

pub mod deprecated;
mod printf;
pub mod unused_names;
pub mod unused_result;

pub fn validate_post_typecheck<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
    results: &TypeCheckResults<'ctx>,
) -> CompileResult<()> {
    printf::run(package, gcx, results)?;
    deprecated::run(package, gcx, results);
    unused_result::run(package, gcx, results);
    unused_names::run(gcx);
    gcx.dcx().ok()
}
