use ecow::EcoString;
use rustc_hash::FxHashMap;
use std::path::PathBuf;

#[derive(Debug, Clone)]
pub struct Config {
    pub name: EcoString,
    pub src: PathBuf,
    pub cwd: PathBuf,
    pub dependencies: FxHashMap<EcoString, String>,
}
