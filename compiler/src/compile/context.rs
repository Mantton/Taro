use bumpalo::Bump;
use ecow::EcoString;
use rustc_hash::FxHashMap;

use crate::{
    PackageIndex, compile::config::Config, diagnostics::DiagCtx,
    sema::resolve::models::ResolutionOutput,
};
use std::{cell::RefCell, ops::Deref};

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
    pub allocator: Bump,
}

impl<'ctx> CompilerArenas<'ctx> {
    pub fn new() -> CompilerArenas<'ctx> {
        CompilerArenas {
            _p: &(),
            allocator: Bump::new(),
        }
    }
}

pub struct CompilerStore<'arena> {
    pub arenas: &'arena CompilerArenas<'arena>,
    pub resolution_outputs: RefCell<FxHashMap<PackageIndex, &'arena ResolutionOutput<'arena>>>,
    pub package_mapping: RefCell<FxHashMap<EcoString, PackageIndex>>,
}

impl<'ctx> CompilerStore<'ctx> {
    pub fn new(arenas: &'ctx CompilerArenas<'ctx>) -> CompilerStore<'ctx> {
        CompilerStore {
            arenas,
            package_mapping: Default::default(),
            resolution_outputs: Default::default(),
        }
    }
}
