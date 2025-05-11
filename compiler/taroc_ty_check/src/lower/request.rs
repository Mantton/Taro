use std::cell::RefCell;

use taroc_hir::DefinitionID;

#[derive(Debug, Default)]
pub struct LoweringRequest {
    pub alias_visits: RefCell<Vec<DefinitionID>>,
    pub context: LoweringContext,
}

#[derive(Debug, Default)]
pub enum LoweringContext {
    #[default]
    Default,
    ExtensionSelfTy,
}

impl LoweringRequest {
    pub fn new(context: LoweringContext) -> Self {
        Self {
            alias_visits: Default::default(),
            context,
        }
    }
}
