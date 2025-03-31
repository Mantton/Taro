use std::rc::Rc;

use taroc_package::CompilerConfig;

#[derive(Clone)]
pub struct CompilerSession {
    pub package_index: usize,
    pub config: Rc<CompilerConfig>,
}
