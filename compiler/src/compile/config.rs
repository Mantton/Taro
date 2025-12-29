use ecow::EcoString;
use rustc_hash::FxHashMap;
use std::path::PathBuf;

use crate::PackageIndex;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum PackageKind {
    Library,
    Executable,
    Both,
}

impl Default for PackageKind {
    fn default() -> Self {
        PackageKind::Executable
    }
}

#[derive(Debug, Clone)]
pub struct Config {
    pub name: EcoString,
    pub identifier: EcoString,
    pub src: PathBuf,
    pub dependencies: FxHashMap<EcoString, String>,
    pub index: PackageIndex,
    pub kind: PackageKind,
    pub executable_out: Option<PathBuf>,
    pub no_std_prelude: bool,
}
