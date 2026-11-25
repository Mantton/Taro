//! Interned names and literals owned by one compiler session.

use crate::sema::models::ConstValue;
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
pub struct Symbol(Slot);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Slot {
    owner: NonZeroU32,
    index: u32,
}

/// Interned byte literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InternedBytes(Slot);

/// Interned fixed-size constant array, which can contain other interned values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InternedConstArray(Slot);

/// Owns the names and literals for one compiler session.
///
/// The same spelling deduplicates within the table. To compare spellings from
/// separate sessions, resolve each handle through its own table.
#[derive(Debug)]
pub struct SessionInterner {
    id: NonZeroU32,
    names: RefCell<IndexSet<EcoString, FxBuildHasher>>,
    bytes: RefCell<IndexSet<Box<[u8]>, FxBuildHasher>>,
    arrays: RefCell<IndexSet<Box<[ConstValue]>, FxBuildHasher>>,
}

impl Default for SessionInterner {
    fn default() -> Self {
        static NEXT_OWNER: AtomicU32 = AtomicU32::new(1);
        let id = NEXT_OWNER
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .expect("compiler session identities exhausted");
        Self {
            id: NonZeroU32::new(id).unwrap(),
            names: RefCell::new(IndexSet::default()),
            bytes: RefCell::new(IndexSet::default()),
            arrays: RefCell::new(IndexSet::default()),
        }
    }
}

impl SessionInterner {
    pub fn intern(&self, spelling: &str) -> Symbol {
        let mut names = self.names.borrow_mut();
        let index = names
            .get_index_of(spelling)
            .unwrap_or_else(|| names.insert_full(spelling.into()).0);
        Symbol(self.slot(index))
    }

    /// Borrow a spelling for as long as its table is borrowed.
    ///
    /// ```compile_fail,E0597
    /// use compiler::interner::SessionInterner;
    ///
    /// let spelling;
    /// {
    ///     let names = SessionInterner::default();
    ///     spelling = names.try_resolve(names.intern("local")).unwrap();
    /// }
    /// assert_eq!(&*spelling, "local");
    /// ```
    pub fn try_resolve(&self, symbol: Symbol) -> Option<Ref<'_, str>> {
        if self.id != symbol.0.owner {
            return None;
        }
        Ref::filter_map(self.names.borrow(), |names| {
            names
                .get_index(symbol.0.index as usize)
                .map(EcoString::as_str)
        })
        .ok()
    }

    /// Copy the spelling out of the table before calling code that can intern names.
    pub(crate) fn text(&self, symbol: Symbol) -> EcoString {
        assert_eq!(self.id, symbol.0.owner, "symbol belongs to another session");
        self.names.borrow()[symbol.0.index as usize].clone()
    }

    pub(crate) fn matches(&self, symbol: Symbol, spelling: &str) -> bool {
        &*self
            .try_resolve(symbol)
            .expect("symbol belongs to another session")
            == spelling
    }

    pub(crate) fn intern_bytes(&self, value: &[u8]) -> InternedBytes {
        let mut bytes = self.bytes.borrow_mut();
        let index = bytes
            .get_index_of(value)
            .unwrap_or_else(|| bytes.insert_full(value.into()).0);
        InternedBytes(self.slot(index))
    }

    pub(crate) fn bytes(&self, value: InternedBytes) -> Ref<'_, [u8]> {
        let index = self.checked_index(value.0);
        Ref::map(self.bytes.borrow(), |values| values[index].as_ref())
    }

    pub(crate) fn intern_const_array(&self, elements: Vec<ConstValue>) -> InternedConstArray {
        for value in &elements {
            match *value {
                ConstValue::String(symbol) => {
                    self.checked_index(symbol.0);
                }
                ConstValue::Bytes(bytes) => {
                    self.checked_index(bytes.0);
                }
                ConstValue::Array(array) => {
                    self.checked_index(array.0);
                }
                _ => {}
            }
        }
        let mut arrays = self.arrays.borrow_mut();
        let index = arrays
            .get_index_of(elements.as_slice())
            .unwrap_or_else(|| arrays.insert_full(elements.into_boxed_slice()).0);
        InternedConstArray(self.slot(index))
    }

    pub(crate) fn const_elements(&self, array: InternedConstArray) -> Ref<'_, [ConstValue]> {
        let index = self.checked_index(array.0);
        Ref::map(self.arrays.borrow(), |arrays| arrays[index].as_ref())
    }

    fn slot(&self, index: usize) -> Slot {
        Slot {
            owner: self.id,
            index: u32::try_from(index).expect("compiler interner exhausted"),
        }
    }

    fn checked_index(&self, slot: Slot) -> usize {
        assert_eq!(
            self.id, slot.owner,
            "interned value belongs to another session"
        );
        slot.index as usize
    }
}

#[cfg(test)]
mod tests {
    use super::{ConstValue, SessionInterner};
    use crate::{
        PackageIndex,
        metadata::wire::{const_value_from_wire, const_value_to_wire},
        sema::resolve::models::{DefinitionID, DefinitionIndex},
        test_support::with_test_gcx,
    };
    use std::{
        panic::{AssertUnwindSafe, catch_unwind, panic_any},
        rc::Rc,
    };

    #[test]
    fn a_slot_cannot_resolve_through_another_owner() {
        let first = SessionInterner::default();
        let second = SessionInterner::default();
        for i in 0..17 {
            first.intern(&format!("first_{i}"));
            second.intern(&format!("second_{i}"));
        }
        let lhs = first.intern("customerDraft");
        let rhs = second.intern("customerFinal");
        assert_eq!(lhs.0.index, 17);
        assert_eq!(rhs.0.index, lhs.0.index);
        assert_ne!(rhs, lhs);
        assert!(first.try_resolve(rhs).is_none());
        assert!(second.try_resolve(lhs).is_none());
        assert_eq!(&*first.try_resolve(lhs).unwrap(), "customerDraft");
        assert_eq!(&*second.try_resolve(rhs).unwrap(), "customerFinal");
        assert_eq!(first.intern("customerDraft"), lhs);
    }

    #[test]
    fn dropping_an_owner_does_not_reuse_its_identity() {
        let old = SessionInterner::default().intern("removed");
        let replacement = SessionInterner::default();
        let current = replacement.intern("replacement");
        assert_eq!(old.0.index, current.0.index);
        assert!(replacement.try_resolve(old).is_none());
    }

    #[test]
    fn another_owner_cannot_read_literals_at_matching_slots() {
        let first = SessionInterner::default();
        let second = SessionInterner::default();
        let first_bytes = first.intern_bytes(b"first");
        let second_bytes = second.intern_bytes(b"second");
        let first_array = first.intern_const_array(vec![ConstValue::Bytes(first_bytes)]);
        let second_array = second.intern_const_array(vec![ConstValue::Bytes(second_bytes)]);
        assert_eq!(first_bytes.0.index, second_bytes.0.index);
        assert_eq!(first_array.0.index, second_array.0.index);
        assert_ne!(first_bytes, second_bytes);
        assert_ne!(first_array, second_array);
        assert!(catch_unwind(AssertUnwindSafe(|| second.bytes(first_bytes))).is_err());
        assert!(catch_unwind(AssertUnwindSafe(|| second.const_elements(first_array))).is_err());
        for foreign in [
            ConstValue::String(first.intern("first")),
            ConstValue::Bytes(first_bytes),
            ConstValue::Array(first_array),
        ] {
            assert!(
                catch_unwind(AssertUnwindSafe(|| second.intern_const_array(vec![foreign])))
                    .is_err()
            );
        }
        assert_eq!(&*second.bytes(second_bytes), b"second");
        assert_eq!(
            &*second.const_elements(second_array),
            &[ConstValue::Bytes(second_bytes)]
        );
    }

    #[test]
    fn unwinding_one_session_leaves_its_peer_and_nested_literals_intact() {
        #[derive(Debug, PartialEq, Eq)]
        struct Cancelled;

        with_test_gcx(|survivor| {
            let id = DefinitionID::new(PackageIndex::new(1), DefinitionIndex::new(2));
            let request = &survivor.store.lowering;
            let active_visit = request.enter_alias(id).unwrap();
            let interner = survivor.interner();
            let text = interner.intern("survivor");
            let bytes = interner.intern_bytes(&[0, 0xFF]);
            let inner = interner.intern_const_array(vec![
                ConstValue::String(text),
                ConstValue::Bytes(bytes),
                ConstValue::EnumUnitVariant(id),
            ]);
            let array = interner.intern_const_array(vec![ConstValue::Array(inner)]);
            survivor
                .dcx()
                .emit_error("surviving diagnostic".into(), None);

            let mut discarded_interner = None;
            let unwind = catch_unwind(AssertUnwindSafe(|| {
                with_test_gcx(|discarded| {
                    let _discarded_visit = discarded.store.lowering.enter_alias(id).unwrap();
                    discarded_interner = Some(Rc::downgrade(&discarded.dcx().symbols));
                    let interner = discarded.interner();
                    interner.intern("different text");
                    interner.intern_bytes(b"different bytes");
                    interner.intern_const_array(vec![ConstValue::Bool(false)]);

                    let value = ConstValue::Array(array);
                    let wire = const_value_to_wire(survivor.interner(), value);
                    let decoded = const_value_from_wire(interner, &wire);
                    assert_ne!(decoded, value);
                    assert_eq!(
                        bincode::serialize(&wire).unwrap(),
                        bincode::serialize(&const_value_to_wire(interner, decoded)).unwrap(),
                    );
                    discarded
                        .dcx()
                        .emit_error("discarded diagnostic".into(), None);
                    panic_any(Cancelled);
                });
            }));
            assert_eq!(
                unwind.unwrap_err().downcast_ref::<Cancelled>(),
                Some(&Cancelled)
            );
            assert!(discarded_interner.unwrap().upgrade().is_none());

            assert!(matches!(request.enter_alias(id), Err(cycle) if cycle == [id]));
            assert_eq!(
                &*interner.const_elements(array),
                &[ConstValue::Array(inner)]
            );
            assert_eq!(
                &*interner.const_elements(inner),
                &[
                    ConstValue::String(text),
                    ConstValue::Bytes(bytes),
                    ConstValue::EnumUnitVariant(id),
                ],
            );
            assert_eq!(&*interner.try_resolve(text).unwrap(), "survivor");
            assert_eq!(&*interner.bytes(bytes), &[0, 0xFF]);
            let diagnostics = survivor.dcx().take_recorded_diagnostics();
            assert_eq!(diagnostics.len(), 1);
            assert_eq!(diagnostics[0].message, "surviving diagnostic");
            drop(active_visit);

            let unwind = catch_unwind(AssertUnwindSafe(|| {
                let _interrupted_visit = request.enter_alias(id).unwrap();
                panic_any(Cancelled);
            }));
            assert_eq!(
                unwind.unwrap_err().downcast_ref::<Cancelled>(),
                Some(&Cancelled)
            );
            assert!(request.enter_alias(id).is_ok());
        });
    }
}
