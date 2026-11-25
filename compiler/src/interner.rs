use std::cell::RefCell;

thread_local! {
    static SESSION_BYTES: RefCell<indexmap::IndexSet<Box<[u8]>>> = RefCell::new(Default::default());
}

/// Arbitrary byte literals are interned for the same lifetime as symbols.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InternedBytes(u32);

impl InternedBytes {
    pub fn new(bytes: &[u8]) -> Self {
        SESSION_BYTES.with_borrow_mut(|values| {
            let index = values
                .get_index_of(bytes)
                .unwrap_or_else(|| values.insert_full(bytes.into()).0);
            Self(u32::try_from(index).expect("byte literal table exhausted"))
        })
    }

    pub fn with_bytes<R>(self, read: impl FnOnce(&[u8]) -> R) -> R {
        SESSION_BYTES.with_borrow(|values| read(&values[self.0 as usize]))
    }

    pub fn len(self) -> usize {
        self.with_bytes(<[u8]>::len)
    }
}
