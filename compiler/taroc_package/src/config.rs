use std::path::PathBuf;

use rustc_hash::FxHashMap;
use taroc_constants::MANIFEST_FILE;
use taroc_error::{CompileError, CompileResult};

use crate::{LockFile, Manifest};

pub struct CompilerConfig {
    identifier: String,
    pub source_path: PathBuf,
    pub working_directory: PathBuf,
    pub is_std: bool,
    pub manifest: Manifest,
    pub dependency_map: FxHashMap<String, String>,
}

impl CompilerConfig {
    pub fn new(
        identifier: String,
        source: PathBuf,
        cwd: PathBuf,
        is_std: bool,
        lockfile: &LockFile,
    ) -> CompileResult<CompilerConfig> {
        let manifest =
            Manifest::parse(&source.join(MANIFEST_FILE)).map_err(CompileError::Message)?;
        let mut mappings = manifest.mappings()?;
        lockfile.normalize_mappings(&mut mappings);
        Ok(CompilerConfig {
            identifier,
            source_path: source,
            working_directory: cwd,
            is_std,
            manifest,
            dependency_map: mappings,
        })
    }

    pub fn package_name(&self) -> String {
        self.manifest.identifier().alias()
    }

    pub fn identifier(&self) -> &String {
        &self.identifier
    }
}
