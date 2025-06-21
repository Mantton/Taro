use crate::SourceMap;

use super::{FileID, SourceFile, symbol::Symbol};
use std::{cell::RefCell, path::PathBuf, sync::Arc};
use string_interner::{DefaultBackend, StringInterner};

scoped_tls::scoped_thread_local!(static SESSION_GLOBALS: SessionGlobals);

pub struct SessionGlobals {
    symbol_: RefCell<StringInterner<DefaultBackend>>,
    source_: RefCell<SourceMap>,
}

impl SessionGlobals {
    pub fn new(mapping: SourceMap) -> SessionGlobals {
        SessionGlobals {
            symbol_: Default::default(),
            source_: RefCell::new(mapping),
        }
    }

    pub fn intern_symbol(&self, string: &str) -> Symbol {
        Symbol::new(self.symbol_.borrow_mut().get_or_intern(string))
    }

    pub fn get_symbol(&self, symbol: Symbol) -> &str {
        unsafe {
            std::mem::transmute(
                self.symbol_
                    .borrow()
                    .resolve(symbol.index())
                    .expect("value not interned"),
            )
        }
    }

    pub fn get_file(&self, file: FileID) -> Arc<SourceFile> {
        self.source_.borrow().get_file(file)
    }

    pub fn tag_file(&self, path: PathBuf) -> FileID {
        self.source_.borrow_mut().tag_file(path)
    }

    pub fn tag_file_with_contents(&self, path: PathBuf, contents: String) -> FileID {
        self.source_
            .borrow_mut()
            .tag_file_with_contents(path, contents)
    }
}

pub fn with_session_globals<R, F>(f: F) -> R
where
    F: FnOnce(&SessionGlobals) -> R,
{
    SESSION_GLOBALS.with(f)
}

pub fn create_session_globals_then<R>(f: impl FnOnce() -> R) -> R {
    assert!(
        !SESSION_GLOBALS.is_set(),
        "SESSION_GLOBALS should never be overwritten! \
         Use another thread if you need another SessionGlobals"
    );
    let session_globals = SessionGlobals::new(Default::default());
    SESSION_GLOBALS.set(&session_globals, f)
}

#[macro_export]
macro_rules! session_test {
    ($body:block) => {{ $crate::create_session_globals_then(|| $body) }};
}

#[macro_export]
macro_rules! register_test_file {
    ($content:expr) => {{
        use std::path::PathBuf;
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("time")
            .as_nanos();
        let path = PathBuf::from(format!("test_{}.taro", unique));
        $crate::with_session_globals(|s| s.tag_file_with_contents(path, $content.to_string()))
    }};
}
