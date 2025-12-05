use crate::{compile::context::GlobalContext, error::CompileResult, hir};

mod function;

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    function::run(package, context)
}
