use crate::{
    compile::{config::Config, context::GlobalContext},
    diagnostics::DiagCtx,
};

pub struct CompilerState {
    pub dcx: DiagCtx,
    pub gcx: GlobalContext,
    pub config: Config,
}

impl CompilerState {
    pub fn new(config: Config) -> CompilerState {
        CompilerState {
            dcx: DiagCtx::new(config.cwd.clone()),
            gcx: GlobalContext::new(),
            config,
        }
    }
}
