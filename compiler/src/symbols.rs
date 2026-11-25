//! Compact symbol handles with session-owned spelling storage.

use ecow::EcoString;
use indexmap::IndexSet;
use rustc_hash::FxBuildHasher;
use std::{
    cell::{Ref, RefCell},
    num::NonZeroU32,
    sync::atomic::{AtomicU32, Ordering},
};

/// An interned name. The owner is part of its identity, including in release builds.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol {
    owner: NonZeroU32,
    index: u32,
}

/// Owns the names for one compiler session.
///
/// The same spelling deduplicates within the table. To compare spellings from
/// separate sessions, resolve each handle through its own table.
#[derive(Debug)]
pub struct SymbolTable {
    id: NonZeroU32,
    names: RefCell<IndexSet<EcoString, FxBuildHasher>>,
}

impl Default for SymbolTable {
    fn default() -> Self {
        static NEXT_OWNER: AtomicU32 = AtomicU32::new(1);
        let id = NEXT_OWNER
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .expect("symbol table identities exhausted");
        Self {
            id: NonZeroU32::new(id).unwrap(),
            names: RefCell::new(IndexSet::default()),
        }
    }
}

impl SymbolTable {
    pub fn intern(&self, spelling: &str) -> Symbol {
        let mut names = self.names.borrow_mut();
        let index = names
            .get_index_of(spelling)
            .unwrap_or_else(|| names.insert_full(spelling.into()).0);
        Symbol {
            owner: self.id,
            index: u32::try_from(index).expect("symbol table exhausted"),
        }
    }

    /// Borrow a spelling for as long as its table is borrowed.
    ///
    /// ```compile_fail,E0597
    /// use compiler::symbols::SymbolTable;
    ///
    /// let spelling;
    /// {
    ///     let names = SymbolTable::default();
    ///     spelling = names.try_resolve(names.intern("local")).unwrap();
    /// }
    /// assert_eq!(&*spelling, "local");
    /// ```
    pub fn try_resolve(&self, symbol: Symbol) -> Option<Ref<'_, str>> {
        if self.id != symbol.owner {
            return None;
        }
        Ref::filter_map(self.names.borrow(), |names| {
            names.get_index(symbol.index as usize).map(EcoString::as_str)
        })
        .ok()
    }

    /// Copy the spelling out of the table before calling code that can intern names.
    pub(crate) fn text(&self, symbol: Symbol) -> EcoString {
        assert_eq!(self.id, symbol.owner, "symbol belongs to another session");
        self.names.borrow()[symbol.index as usize].clone()
    }

    pub(crate) fn matches(&self, symbol: Symbol, spelling: &str) -> bool {
        &*self
            .try_resolve(symbol)
            .expect("symbol belongs to another session")
            == spelling
    }
}

#[cfg(test)]
mod tests {
    use super::SymbolTable;

    #[test]
    fn a_slot_cannot_resolve_through_another_owner() {
        let first = SymbolTable::default();
        let second = SymbolTable::default();
        for i in 0..17 {
            first.intern(&format!("first_{i}"));
            second.intern(&format!("second_{i}"));
        }
        let lhs = first.intern("customerDraft");
        let rhs = second.intern("customerFinal");
        assert_eq!(lhs.index, 17);
        assert_eq!(rhs.index, lhs.index);
        assert_ne!(rhs, lhs);
        assert!(first.try_resolve(rhs).is_none());
        assert!(second.try_resolve(lhs).is_none());
        assert_eq!(&*first.try_resolve(lhs).unwrap(), "customerDraft");
        assert_eq!(&*second.try_resolve(rhs).unwrap(), "customerFinal");
        assert_eq!(first.intern("customerDraft"), lhs);
    }

    #[test]
    fn dropping_an_owner_does_not_reuse_its_identity() {
        let old = SymbolTable::default().intern("removed");
        let replacement = SymbolTable::default();
        let current = replacement.intern("replacement");
        assert_eq!(old.index, current.index);
        assert!(replacement.try_resolve(old).is_none());
    }
}
