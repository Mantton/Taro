use crate::{
    compile::context::GlobalContext, error::CompileResult, hir,
    sema::tycheck::results::TypeCheckResults, span::Span,
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
    validate_body_facts(package, gcx, results)?;
    unused_names::run(gcx);
    gcx.dcx().ok()
}

/// Apply only the post-check diagnostics whose primary source is in the
/// selected declaration. The caller checks for cross-body dependencies.
pub(crate) fn validate_selected_body<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
    results: &TypeCheckResults<'ctx>,
    span: Span,
) -> CompileResult<()> {
    validate_body_facts(package, gcx, results)?;
    unused_names::run_in(gcx, |name| {
        name.file == span.file && span.start <= name.start && name.end <= span.end
    });
    gcx.dcx().ok()
}

fn validate_body_facts<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
    results: &TypeCheckResults<'ctx>,
) -> CompileResult<()> {
    printf::run(package, gcx, results)?;
    deprecated::run(package, gcx, results);
    unused_result::run(package, gcx, results);
    Ok(())
}
