use crate::{
    compile::context::GlobalContext, hir::DefinitionID, sema::tycheck::lower::TypeLowerer,
};

pub struct DefTyLoweringCtx<'ctx> {
    gcx: GlobalContext<'ctx>,
    id: DefinitionID,
}

type Ctx<'ctx> = DefTyLoweringCtx<'ctx>;

impl<'ctx> Ctx<'ctx> {
    pub fn new(id: DefinitionID, gcx: GlobalContext<'ctx>) -> Ctx<'ctx> {
        Ctx { id, gcx }
    }
}

impl<'ctx> TypeLowerer<'ctx> for Ctx<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }
}
