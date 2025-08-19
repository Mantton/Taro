use std::cell::RefCell;

use taroc_hir::DefinitionID;

#[derive(Debug, Default)]
pub struct LoweringRequest {
    pub alias_visits: RefCell<Vec<DefinitionID>>,
}

impl LoweringRequest {
    pub fn new() -> Self {
        Self {
            alias_visits: Default::default(),
        }
    }
}
