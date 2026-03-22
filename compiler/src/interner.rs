use bumpalo::Bump;
use rustc_hash::FxHashMap;
use std::cell::RefCell;

/// A session-scoped string interner.
///
/// Strings are allocated in a bump arena and deduplicated via a hash map.
/// The arena (and all interned strings) can be freed by dropping the interner
/// or calling [`reset_session`].
pub(crate) struct StringInterner {
    arena: Bump,
    lookup: FxHashMap<&'static str, u32>,
    strings: Vec<&'static str>,
}

impl StringInterner {
    fn new() -> Self {
        let mut interner = StringInterner {
            arena: Bump::new(),
            lookup: FxHashMap::default(),
            strings: Vec::new(),
        };
        // Index 0 is always the empty string.
        interner.intern("");
        interner
    }

    fn intern(&mut self, s: &str) -> u32 {
        if let Some(&idx) = self.lookup.get(s) {
            return idx;
        }
        let idx = self.strings.len() as u32;
        let allocated = self.arena.alloc_str(s);
        // SAFETY: The allocated string lives as long as the arena, which lives
        // as long as this interner (or until `reset_session` is called). We
        // cast to 'static so that the returned &str can escape the RefCell
        // borrow in `Symbol::as_str()`. Callers must not use Symbol values
        // after the session is reset.
        let stable: &'static str = unsafe { &*(allocated as *const str) };
        self.lookup.insert(stable, idx);
        self.strings.push(stable);
        idx
    }

    fn resolve(&self, idx: u32) -> &'static str {
        self.strings[idx as usize]
    }

    fn len(&self) -> usize {
        self.strings.len()
    }
}

thread_local! {
    static SESSION_INTERNER: RefCell<StringInterner> = RefCell::new(StringInterner::new());
}

/// Intern a string in the current session, returning its index.
pub(crate) fn intern(s: &str) -> u32 {
    SESSION_INTERNER.with(|cell| cell.borrow_mut().intern(s))
}

/// Resolve a symbol index to its string.
pub(crate) fn resolve(idx: u32) -> &'static str {
    SESSION_INTERNER.with(|cell| cell.borrow().resolve(idx))
}

/// Return the number of interned symbols in the current session.
pub fn interned_symbol_count() -> usize {
    SESSION_INTERNER.with(|cell| cell.borrow().len())
}

/// Reset the interner, freeing all interned strings.
///
/// After calling this, any previously created `Symbol` values are invalid.
/// This is intended to be called between LSP analysis passes.
pub fn reset_session() {
    SESSION_INTERNER.with(|cell| {
        *cell.borrow_mut() = StringInterner::new();
    });
}
