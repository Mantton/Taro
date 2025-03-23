use std::rc::Rc;

use taroc_context::CompilerSession;
use taroc_error::CompileResult;

pub fn run(package: taroc_hir::Package, session: Rc<CompilerSession>) -> CompileResult<()> {
    return Ok(());
    let context = session.context;
    taroc_resolve::run(&package, session.clone())?;
    taroc_ty_check::run(&package, session.clone())?;
    context.diagnostics.report()
}
