use crate::span::FileID;
use index_vec::IndexVec;
use std::{cell::RefCell, path::PathBuf};

pub struct DiagCtx {
    inner: RefCell<DiagCtxInner>,
}

impl DiagCtx {
    pub fn new() -> DiagCtx {
        DiagCtx {
            inner: RefCell::new(Default::default()),
        }
    }
    pub fn add_file_mapping(&self, path: PathBuf) -> FileID {
        self.inner.borrow_mut().file_mappings.push(path)
    }
}

impl DiagCtx {
    pub fn report(&self) -> DiagCtx {
        DiagCtx {
            inner: RefCell::new(Default::default()),
        }
    }
}

#[derive(Default)]
struct DiagCtxInner {
    file_mappings: IndexVec<FileID, PathBuf>,
}
