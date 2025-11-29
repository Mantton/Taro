use ecow::EcoString;
use rustc_hash::FxHashMap;
use std::path::PathBuf;

use crate::PackageIndex;

#[derive(Debug, Clone)]
pub struct Config {
    pub name: EcoString,
    pub identifier: EcoString,
    pub src: PathBuf,
    pub dependencies: FxHashMap<EcoString, String>,
    pub index: PackageIndex,
}
