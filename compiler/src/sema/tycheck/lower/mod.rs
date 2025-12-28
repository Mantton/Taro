pub mod item;
pub mod lowerer;

use std::cell::RefCell;

pub use item::*;
pub use lowerer::*;

use crate::hir::DefinitionID;

/// Tracks state during type lowering, specifically for cycle detection in aliases
#[derive(Debug, Default)]
pub struct LoweringRequest {
    /// Stack of alias IDs currently being lowered (for cycle detection)
    pub alias_visits: RefCell<Vec<DefinitionID>>,
}

impl LoweringRequest {
    pub fn new() -> Self {
        Self {
            alias_visits: Default::default(),
        }
    }

    /// Enter an alias lowering. Returns Err with cycle path if cycle detected.
    pub fn enter_alias(&self, id: DefinitionID) -> Result<(), Vec<DefinitionID>> {
        let mut visits = self.alias_visits.borrow_mut();
        if let Some(pos) = visits.iter().position(|&v| v == id) {
            // Found cycle - return the cycle path
            let cycle = visits[pos..].to_vec();
            return Err(cycle);
        }
        visits.push(id);
        Ok(())
    }

    /// Exit an alias lowering
    pub fn exit_alias(&self, id: DefinitionID) {
        let mut visits = self.alias_visits.borrow_mut();
        debug_assert_eq!(visits.last(), Some(&id));
        visits.pop();
    }
}
