use std::path::PathBuf;

use crate::compile::config::ModuleArtifactKind;

/// A package-level artifact produced from one optimized LLVM module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleArtifact {
    pub kind: ModuleArtifactKind,
    pub path: PathBuf,
}

impl ModuleArtifact {
    pub fn new(kind: ModuleArtifactKind, path: PathBuf) -> Self {
        Self { kind, path }
    }
}

impl ModuleArtifactKind {
    pub const fn extension(self) -> &'static str {
        match self {
            Self::Object => "o",
            Self::LlvmBitcode => "bc",
        }
    }

    pub const fn display_name(self) -> &'static str {
        match self {
            Self::Object => "object",
            Self::LlvmBitcode => "LLVM bitcode",
        }
    }
}
