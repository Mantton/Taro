use std::path::PathBuf;

use crate::compile::config::ModuleArtifactKind;

/// A package-level artifact produced from one optimized LLVM module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleArtifact {
    pub kind: ModuleArtifactKind,
    pub path: PathBuf,
    /// Compiler descriptors retained until LLVM's machine stack maps are
    /// normalized. Bitcode artifacts carry this through LTO.
    pub stack_map_descriptors: Option<PathBuf>,
    /// Native object containing the registered, runtime-facing PC table.
    /// This is present only once an object artifact has been emitted.
    pub pc_metadata: Option<PathBuf>,
}

impl ModuleArtifact {
    pub fn new(kind: ModuleArtifactKind, path: PathBuf) -> Self {
        Self {
            kind,
            path,
            stack_map_descriptors: None,
            pc_metadata: None,
        }
    }

    pub fn with_stack_maps(
        mut self,
        stack_map_descriptors: PathBuf,
        pc_metadata: Option<PathBuf>,
    ) -> Self {
        self.stack_map_descriptors = Some(stack_map_descriptors);
        self.pc_metadata = pc_metadata;
        self
    }

    /// Native inputs contributed by this artifact in deterministic order.
    pub fn link_inputs(&self) -> impl Iterator<Item = &PathBuf> {
        std::iter::once(&self.path).chain(self.pc_metadata.iter())
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
