use std::marker::PhantomData;

pub type Gcx<'gcx> = GlobalContext<'gcx>;

pub struct GlobalContext<'gcx> {
    store: GlobalStore<'gcx>,
}

impl<'ctx> GlobalContext<'ctx> {
    pub fn new(arenas: &'ctx GlobalArenas<'ctx>) -> GlobalContext<'ctx> {
        GlobalContext {
            store: GlobalStore::new(arenas),
        }
    }
}

pub struct GlobalArenas<'arena> {
    _p: &'arena (),
}

impl<'ctx> GlobalArenas<'ctx> {
    pub fn new() -> GlobalArenas<'ctx> {
        GlobalArenas { _p: &() }
    }
}

pub struct GlobalStore<'arena> {
    arenas: &'arena GlobalArenas<'arena>,
}

impl<'ctx> GlobalStore<'ctx> {
    pub fn new(arenas: &'ctx GlobalArenas<'ctx>) -> GlobalStore<'ctx> {
        GlobalStore { arenas }
    }
}
