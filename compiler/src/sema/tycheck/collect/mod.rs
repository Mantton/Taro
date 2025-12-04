use crate::{compile::context::GlobalContext, error::CompileResult, hir};

mod functions;

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    functions::run(package, context)
}
