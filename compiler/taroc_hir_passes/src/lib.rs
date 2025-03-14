use std::rc::Rc;

use taroc_context::CompilerSession;
use taroc_error::CompileResult;

pub fn run(package: taroc_hir::Package, session: Rc<CompilerSession>) -> CompileResult<()> {
    let context = session.context;
    taroc_resolve::run(&package, session)?;
    taroc_ty_check::run(&package, context)?;
    context.diagnostics.report()
}
