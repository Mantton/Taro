use crate::{compile::state::CompilerState, error::CompileResult, hir};

pub fn run(package: &hir::Package, context: CompilerState) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: CompilerState<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: CompilerState<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(package: &hir::Package, context: CompilerState<'ctx>) -> CompileResult<()> {
        todo!()
    }
}
