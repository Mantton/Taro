use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use std::{collections::HashSet, path::PathBuf};

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct LockFile {
    pub package: Vec<LockfilePackage>,
    pub version: u8,
    pub name: String,
}

impl LockFile {
    pub fn parse(path: &PathBuf) -> Result<LockFile, String> {
        let content = std::fs::read_to_string(&path)
            .map_err(|e| format!("failed to read lockfile @ {:?}, {}", path, e))?;
        let manifest = toml::from_str::<LockFile>(&content)
            .map_err(|e| format!("failed to parse lockfile @ {:?}, {}", path, e))?;
        Ok(manifest)
    }
}

impl LockFile {
    pub fn normalize_mappings(&self, table: &mut FxHashMap<String, String>) {
        for (alias, package) in std::mem::take(table) {
            let target = self
                .package
                .iter()
                .find(|dependency| package == dependency.name || dependency.qualified() == package)
                .expect("target should be in lockfile");

            // Replace with qualifed mappings
            table.insert(alias, target.qualified());
        }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct LockfilePackage {
    pub name: String,
    pub source: String,
    pub revision: String,
    pub require: Option<HashSet<String>>,
    pub direct: bool,
}

impl LockfilePackage {
    pub fn qualified(&self) -> String {
        format!("{}@{}", &self.name, &self.revision)
    }
}
