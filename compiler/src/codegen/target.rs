//! Target-specific layout information.
//!
//! This module wraps LLVM's target data and exposes it for use in MIR
//! layout computation and codegen.

use crate::{
    compile::config::BuildProfile,
    diagnostics::DiagCtx,
    error::CompileResult,
};
use inkwell::OptimizationLevel;
use inkwell::targets::{
    CodeModel, InitializationConfig, RelocMode, Target, TargetData, TargetMachine, TargetTriple,
};

/// Wrapper around LLVM target information for layout computation.
///
/// Created early in the compilation pipeline and shared between MIR and Codegen.
pub struct TargetLayout {
    pub pointer_size: u64,
    pub pointer_align: u64,
    target_machine: TargetMachine,
}

impl TargetLayout {
    /// Initialize for a specific target, or host if None.
    pub fn new(
        dcx: &DiagCtx,
        target_override: Option<&str>,
        profile: BuildProfile,
    ) -> CompileResult<Self> {
        // Initialize all targets if cross-compiling, otherwise just native
        if target_override.is_some() {
            Target::initialize_all(&InitializationConfig::default());
        } else {
            Target::initialize_native(&InitializationConfig::default()).map_err(|e| {
                dcx.emit_error(
                    format!("failed to initialize LLVM native target: {}", e),
                    None,
                );
                crate::error::ReportedError
            })?;
        }

        let triple = match target_override {
            Some(t) => TargetTriple::create(t),
            None => TargetMachine::get_default_triple(),
        };

        let target = Target::from_triple(&triple).map_err(|e| {
            dcx.emit_error(
                format!("failed to get target from triple '{}': {}", triple, e),
                None,
            );
            crate::error::ReportedError
        })?;

        // Use generic CPU and features for cross-compilation
        let (cpu, features) = if target_override.is_some() {
            ("generic".to_string(), "".to_string())
        } else {
            let cpu = TargetMachine::get_host_cpu_name();
            let features = TargetMachine::get_host_cpu_features();
            (
                cpu.to_str().unwrap_or("").to_string(),
                features.to_str().unwrap_or("").to_string(),
            )
        };

        // Debug builds prioritize compile speed; release builds keep the default LLVM level.
        let optimization = match profile {
            BuildProfile::Debug => OptimizationLevel::None,
            BuildProfile::Release => OptimizationLevel::Default,
        };

        let target_machine = target
            .create_target_machine(
                &triple,
                &cpu,
                &features,
                optimization,
                RelocMode::Default,
                CodeModel::Default,
            )
            .ok_or_else(|| {
                dcx.emit_error(
                    format!("failed to create target machine for triple '{}'", triple),
                    None,
                );
                crate::error::ReportedError
            })?;

        let target_data = target_machine.get_target_data();
        let pointer_size = target_data.get_pointer_byte_size(None) as u64;
        // Pointer alignment is typically equal to pointer size for most targets.
        let pointer_align = pointer_size;

        Ok(TargetLayout {
            pointer_size,
            pointer_align,
            target_machine,
        })
    }

    /// Initialize for the host machine.
    pub fn for_host(dcx: &DiagCtx) -> CompileResult<Self> {
        Self::new(dcx, None, BuildProfile::Debug)
    }

    /// Get the underlying LLVM TargetData for precise layout queries.
    #[inline]
    pub fn target_data(&self) -> TargetData {
        self.target_machine.get_target_data()
    }

    /// Get the target triple.
    #[inline]
    pub fn triple(&self) -> TargetTriple {
        self.target_machine.get_triple()
    }

    /// Get the data layout string for LLVM modules.
    #[inline]
    pub fn data_layout(&self) -> inkwell::data_layout::DataLayout {
        self.target_data().get_data_layout()
    }

    /// Get the underlying target machine (needed for codegen).
    #[inline]
    pub fn target_machine(&self) -> &TargetMachine {
        &self.target_machine
    }
}
