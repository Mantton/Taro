pub mod item;
pub mod lowerer;

use std::cell::RefCell;

pub use item::*;
pub use lowerer::*;

use crate::hir::DefinitionID;

/// The alias resolution stack for one compiler session.
#[derive(Debug, Default)]
pub(crate) struct LoweringRequest {
    alias_visits: RefCell<Vec<DefinitionID>>,
}

impl LoweringRequest {
    /// Enter an alias until the returned guard drops. A cycle returns its path.
    pub(crate) fn enter_alias(
        &self,
        id: DefinitionID,
    ) -> Result<AliasVisit<'_>, Vec<DefinitionID>> {
        let mut visits = self.alias_visits.borrow_mut();
        if let Some(start) = visits.iter().position(|&alias| alias == id) {
            return Err(visits[start..].to_vec());
        }
        visits.push(id);
        Ok(AliasVisit { request: self, id })
    }
}

pub(crate) struct AliasVisit<'a> {
    request: &'a LoweringRequest,
    id: DefinitionID,
}

impl Drop for AliasVisit<'_> {
    fn drop(&mut self) {
        let removed = self.request.alias_visits.borrow_mut().pop();
        debug_assert_eq!(removed, Some(self.id));
    }
}
