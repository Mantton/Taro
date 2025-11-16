use std::rc::Rc;

use crate::{
    compile::{config::Config, context::GlobalContext},
    diagnostics::DiagCtx,
};

pub struct CompilerState {
    pub dcx: Rc<DiagCtx>,
    pub gcx: GlobalContext,
    pub config: Config,
}

impl CompilerState {
    pub fn new(config: Config, dcx: Rc<DiagCtx>) -> CompilerState {
        CompilerState {
            dcx,
            gcx: GlobalContext::new(),
            config,
        }
    }
}
