use crate::{FileID, SourceFile};
use index_vec::IndexVec;
use std::{path::PathBuf, sync::Arc};

#[derive(Default)]
pub struct SourceMap {
    index_to_file: SourceMapFiles,
}

pub type SourceMapFiles = IndexVec<FileID, Arc<SourceFile>>;
impl SourceMap {
    pub fn tag_file(&mut self, path: PathBuf) -> FileID {
        self.index_to_file.push(Arc::new(SourceFile::new(path)))
    }
    pub fn get_file(&self, file: FileID) -> Arc<SourceFile> {
        self.index_to_file[file].clone()
    }
}
