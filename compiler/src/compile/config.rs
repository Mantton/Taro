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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BuildProfile {
    Debug,
    Release,
}

impl Default for BuildProfile {
    fn default() -> Self {
        BuildProfile::Debug
    }
}

/// Debug options for compiler diagnostics and dumps.
#[derive(Debug, Clone, Copy, Default)]
pub struct DebugOptions {
    /// Dump MIR for all functions to stderr
    pub dump_mir: bool,
    /// Dump LLVM IR to stderr
    pub dump_llvm: bool,
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
    /// True for single-file scripts (no package structure)
    pub is_script: bool,
    pub profile: BuildProfile,
    pub overflow_checks: bool,
    /// Debug options for dumps
    pub debug: DebugOptions,
}
