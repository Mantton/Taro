use super::{FileID, Span, session::with_session_globals};
use core::fmt;
use std::hash::{Hash, Hasher};
use string_interner::symbol::SymbolU32;

#[derive(Debug, Clone, Copy, Eq)]
pub struct Identifier {
    pub span: Span,
    pub symbol: Symbol,
}

impl Identifier {
    pub fn emtpy(file: FileID) -> Self {
        Identifier {
            span: Span::empty(file),
            symbol: Symbol::with(""),
        }
    }
}

impl PartialEq for Identifier {
    #[inline]
    fn eq(&self, rhs: &Self) -> bool {
        self.symbol == rhs.symbol
    }
}

impl Hash for Identifier {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.symbol.hash(state);
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(SymbolU32);

impl Symbol {
    pub const fn new(n: SymbolU32) -> Self {
        Symbol(n)
    }

    pub fn intern(string: &str) -> Self {
        with_session_globals(|s| s.intern_symbol(string))
    }

    pub fn with(string: &str) -> Self {
        Self::intern(string)
    }

    pub fn as_str(&self) -> &str {
        with_session_globals(|s| unsafe { std::mem::transmute(s.get_symbol(*self)) })
    }

    pub fn index(self) -> SymbolU32 {
        return self.0;
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}
