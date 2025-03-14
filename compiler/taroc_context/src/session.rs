use std::rc::Rc;

use taroc_package::CompilerConfig;

use crate::GlobalContext;

pub struct CompilerSession<'ctx> {
    pub index: usize,
    pub config: CompilerConfig,
    pub context: GlobalContext<'ctx>,
}
