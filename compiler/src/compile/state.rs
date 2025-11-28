use crate::{
    compile::{config::Config, global::GlobalContext},
    diagnostics::DiagCtx,
};
use std::{ops::Deref, rc::Rc};

#[derive(Clone, Copy)]
pub struct CompilerState<'state> {
    context: &'state CompilerContext<'state>,
}

impl<'state> Deref for CompilerState<'state> {
    type Target = &'state CompilerContext<'state>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.context
    }
}

pub struct CompilerContext<'gcx> {
    pub dcx: Rc<DiagCtx>,
    pub gcx: &'gcx GlobalContext<'gcx>,
    pub config: Config,
}

impl<'state> CompilerState<'state> {
    pub fn new(context: &'state CompilerContext<'state>) -> CompilerState<'state> {
        CompilerState { context }
    }
}
