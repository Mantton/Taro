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
    /// Register a new file with preloaded contents.
    pub fn tag_file_with_contents(&mut self, path: PathBuf, contents: String) -> FileID {
        self.index_to_file
            .push(Arc::new(SourceFile::new_with_content(path, contents)))
    }
}
