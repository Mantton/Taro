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

/// LLVM optimization level selected for the middle-end and target backend.
///
/// This is intentionally separate from [`BuildProfile`]. Profiles control
/// language-facing defaults such as overflow checks and `cfg(profile = ...)`,
/// while optimization is an independently selectable code-generation policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum OptLevel {
    O0,
    O1,
    O2,
    O3,
    Os,
    Oz,
}

/// Which LLVM IR optimization pipeline should be used for a package.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum OptimizationMode {
    /// Preserve Taro's pre-LLVM-22-upgrade pipelines for controlled rollout
    /// and benchmark comparisons.
    #[default]
    Baseline,
    /// Use LLVM's maintained default pipeline for the selected level.
    Level(OptLevel),
}

/// Native or LLVM module artifact emitted for one compiled package.
///
/// Object artifacts are consumed by the native linker. LLVM bitcode preserves
/// the optimized module for explicit compiler output and future LTO stages.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum ModuleArtifactKind {
    #[default]
    Object,
    LlvmBitcode,
}

/// Cross-package LLVM optimization policy for linked outputs.
///
/// LTO applies only to participating LLVM bitcode modules. Precompiled native
/// libraries, including the attached standard library and runtime, remain
/// opaque linker inputs.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum LtoMode {
    #[default]
    Off,
    Full,
}

/// Code-generation policy for a package.
///
/// Keeping this separate from a source-level build profile allows callers to
/// select optimization, artifact, and link-time policy independently.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct CodegenOptions {
    pub optimization: OptimizationMode,
    pub artifact: ModuleArtifactKind,
    pub lto: LtoMode,
}

/// Amount of source-level debug metadata emitted into generated objects.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum DebugInfo {
    #[default]
    None,
    /// Emit function metadata and source line tables without local variables.
    LineTables,
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
    /// Source-level debug metadata to emit.
    pub debug_info: DebugInfo,
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
    pub codegen: CodegenOptions,
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
