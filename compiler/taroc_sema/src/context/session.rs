use std::rc::Rc;

use taroc_hir::PackageIndex;
use taroc_package::CompilerConfig;

#[derive(Clone)]
pub struct CompilerSession {
    pub package_index: usize,
    pub config: Rc<CompilerConfig>,
}

impl CompilerSession {
    pub fn index(&self) -> PackageIndex {
        PackageIndex::from_usize(self.package_index)
    }
}
