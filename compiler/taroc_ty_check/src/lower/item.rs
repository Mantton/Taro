use taroc_context::GlobalContext;

use super::TypeLowerer;

pub struct ItemCtx<'ctx> {
    pub gcx: GlobalContext<'ctx>,
}

impl<'ctx> ItemCtx<'ctx> {
    pub fn new(gcx: GlobalContext<'ctx>) -> ItemCtx<'ctx> {
        ItemCtx { gcx }
    }
}

impl<'ctx> TypeLowerer<'ctx> for ItemCtx<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }
}
