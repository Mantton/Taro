use crate::{compile::config::Config, diagnostics::DiagCtx};
use std::ops::Deref;

pub type Gcx<'gcx> = GlobalContext<'gcx>;

#[derive(Clone, Copy)]
pub struct GlobalContext<'state> {
    context: &'state CompilerContext<'state>,
    pub config: &'state Config,
}

impl<'state> GlobalContext<'state> {
    pub fn new(
        context: &'state CompilerContext<'state>,
        config: &'state Config,
    ) -> GlobalContext<'state> {
        GlobalContext { context, config }
    }
}

impl<'state> Deref for GlobalContext<'state> {
    type Target = &'state CompilerContext<'state>;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.context
    }
}

pub struct CompilerContext<'arena> {
    pub dcx: DiagCtx,
    pub store: CompilerStore<'arena>,
}

impl<'arena> CompilerContext<'arena> {
    pub fn new(dcx: DiagCtx, store: CompilerStore<'arena>) -> CompilerContext<'arena> {
        CompilerContext { dcx, store }
    }
}

pub struct CompilerArenas<'arena> {
    _p: &'arena (),
}

impl<'ctx> CompilerArenas<'ctx> {
    pub fn new() -> CompilerArenas<'ctx> {
        CompilerArenas { _p: &() }
    }
}

pub struct CompilerStore<'arena> {
    arenas: &'arena CompilerArenas<'arena>,
}

impl<'ctx> CompilerStore<'ctx> {
    pub fn new(arenas: &'ctx CompilerArenas) -> CompilerStore<'ctx> {
        CompilerStore { arenas }
    }
}
