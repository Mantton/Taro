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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StdMode {
    BootstrapStd,
    FullStd,
}

impl Default for StdMode {
    fn default() -> Self {
        StdMode::FullStd
    }
}

/// Debug options for compiler diagnostics and dumps.
#[derive(Debug, Clone, Copy, Default)]
pub struct DebugOptions {
    /// Dump MIR for all functions to stderr
    pub dump_mir: bool,
    /// Dump LLVM IR to stderr
    pub dump_llvm: bool,
    /// Print per-phase compiler timings to stderr
    pub timings: bool,
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
    /// True when building in test mode (`taro test`)
    pub test_mode: bool,
    /// Controls std *availability semantics* during compilation:
    /// - `BootstrapStd`: compile may proceed without an externally-registered std provider.
    /// - `FullStd`: compile expects a std provider to be available for std lookups.
    ///
    /// This is intentionally separate from `is_std_provider` because mode describes
    /// resolution behavior, not package identity/privilege.
    pub std_mode: StdMode,
    /// True when this package is the std provider selected by the driver.
    ///
    /// This is intentionally separate from `std_mode`: provider identity grants
    /// std-owned behavior (e.g., ownership rules for built-in types), while
    /// `std_mode` only describes whether std is expected to be externally available.
    pub is_std_provider: bool,
}
