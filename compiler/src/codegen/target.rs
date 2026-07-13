//! Target-specific layout information.
//!
//! This module wraps LLVM's target data and exposes it for use in MIR
//! layout computation and codegen.

use crate::{
    compile::config::{BuildProfile, OptLevel, OptimizationMode},
    diagnostics::DiagCtx,
    error::CompileResult,
};
use inkwell::targets::{
    CodeModel, InitializationConfig, RelocMode, Target, TargetData, TargetMachine, TargetTriple,
};
use inkwell::{AddressSpace, OptimizationLevel as LlvmOptimizationLevel, context::Context};
use std::{ffi::CString, sync::Once};

static CONFIGURE_LLVM_CODEGEN: Once = Once::new();

fn backend_optimization_level(
    profile: BuildProfile,
    optimization: OptimizationMode,
) -> LlvmOptimizationLevel {
    match optimization {
        OptimizationMode::Baseline => match profile {
            BuildProfile::Debug => LlvmOptimizationLevel::None,
            BuildProfile::Release => LlvmOptimizationLevel::Default,
        },
        OptimizationMode::Level(OptLevel::O0) => LlvmOptimizationLevel::None,
        OptimizationMode::Level(OptLevel::O1) => LlvmOptimizationLevel::Less,
        OptimizationMode::Level(OptLevel::O2 | OptLevel::Os | OptLevel::Oz) => {
            LlvmOptimizationLevel::Default
        }
        OptimizationMode::Level(OptLevel::O3) => LlvmOptimizationLevel::Aggressive,
    }
}

fn configure_llvm_codegen() {
    CONFIGURE_LLVM_CODEGEN.call_once(|| {
        // Keep SelectionDAG as Taro's stable instruction selector on LLVM 22.
        // GlobalISel remains an explicit follow-up experiment: changing the
        // selector during the LLVM compatibility upgrade would conflate
        // backend policy with toolchain compatibility.
        let program = CString::new("taro-llvm").expect("static string has no NUL");
        let option = CString::new("--global-isel=0").expect("static string has no NUL");
        let overview = CString::new("Taro LLVM options").expect("static string has no NUL");
        let arguments = [program.as_ptr(), option.as_ptr()];
        unsafe {
            inkwell::llvm_sys::support::LLVMParseCommandLineOptions(
                arguments.len() as i32,
                arguments.as_ptr(),
                overview.as_ptr(),
            );
        }
    });
}

/// Wrapper around LLVM target information for layout computation.
///
/// Created early in the compilation pipeline and shared between MIR and Codegen.
pub struct TargetLayout {
    pub pointer_size: u64,
    pub pointer_align: u64,
    requested_triple: Option<String>,
    cpu: String,
    features: String,
    target_machine: TargetMachine,
}

impl TargetLayout {
    /// Initialize for a specific target, or host if None.
    pub fn new(
        dcx: &DiagCtx,
        target_override: Option<&str>,
        profile: BuildProfile,
    ) -> CompileResult<Self> {
        configure_llvm_codegen();

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
        let optimization = backend_optimization_level(profile, OptimizationMode::Baseline);

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
        let pointer_align = pointer_abi_alignment(&target_data);

        Ok(TargetLayout {
            pointer_size,
            pointer_align,
            requested_triple: target_override.map(ToOwned::to_owned),
            cpu,
            features,
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

    /// Return the target triple explicitly requested by the driver, if any.
    ///
    /// This is kept separately from LLVM's effective triple because LLVM may
    /// canonicalize host triples into a spelling that Cargo does not accept.
    #[inline]
    pub fn requested_triple(&self) -> Option<&str> {
        self.requested_triple.as_deref()
    }

    /// CPU name used to produce native artifacts for this compilation.
    #[inline]
    pub fn cpu(&self) -> &str {
        &self.cpu
    }

    /// Target feature string used to produce native artifacts.
    #[inline]
    pub fn features(&self) -> &str {
        &self.features
    }

    pub fn triple_string(&self) -> String {
        self.triple().as_str().to_string_lossy().into_owned()
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

    /// Create a target machine for one package's optimization policy.
    ///
    /// Layout remains shared across the compilation, but backend optimization
    /// must follow the package policy: attached std and user packages can use
    /// different profiles, and an explicit `-O` overrides either profile.
    pub fn create_target_machine(
        &self,
        dcx: &DiagCtx,
        profile: BuildProfile,
        optimization: OptimizationMode,
    ) -> CompileResult<TargetMachine> {
        let triple = self.triple();
        let target = Target::from_triple(&triple).map_err(|error| {
            dcx.emit_error(
                format!("failed to get target from triple '{}': {error}", triple),
                None,
            );
            crate::error::ReportedError
        })?;
        target
            .create_target_machine(
                &triple,
                &self.cpu,
                &self.features,
                backend_optimization_level(profile, optimization),
                RelocMode::Default,
                CodeModel::Default,
            )
            .ok_or_else(|| {
                dcx.emit_error(
                    format!("failed to create target machine for triple '{}'", triple),
                    None,
                );
                crate::error::ReportedError
            })
    }
}

fn pointer_abi_alignment(target_data: &TargetData) -> u64 {
    let context = Context::create();
    let pointer_ty = context.ptr_type(AddressSpace::default());
    target_data.get_abi_alignment(&pointer_ty) as u64
}

#[cfg(test)]
mod tests {
    use super::{TargetLayout, backend_optimization_level, pointer_abi_alignment};
    use crate::{
        compile::config::{BuildProfile, OptLevel, OptimizationMode},
        diagnostics::DiagCtx,
    };
    use inkwell::{
        OptimizationLevel as LlvmOptimizationLevel,
        context::Context,
        targets::{FileType, TargetData},
    };
    use std::path::PathBuf;

    fn pointer_layout(data_layout: &str) -> (u64, u64) {
        let target_data = TargetData::create(data_layout);
        (
            target_data.get_pointer_byte_size(None) as u64,
            pointer_abi_alignment(&target_data),
        )
    }

    fn diagnostics() -> DiagCtx {
        DiagCtx::new(PathBuf::from("."))
    }

    fn emit_smoke_object(layout: &TargetLayout, module_name: &str) -> Vec<u8> {
        let context = Context::create();
        let module = context.create_module(module_name);
        module.set_data_layout(&layout.data_layout());
        module.set_triple(&layout.triple());
        let builder = context.create_builder();
        let function = module.add_function("smoke", context.i32_type().fn_type(&[], false), None);
        let block = context.append_basic_block(function, "entry");
        builder.position_at_end(block);
        builder
            .build_return(Some(&context.i32_type().const_zero()))
            .unwrap();
        module.verify().expect("smoke module should verify");

        layout
            .target_machine()
            .write_to_memory_buffer(&module, FileType::Object)
            .expect("target machine should emit an object")
            .as_slice()
            .to_vec()
    }

    #[test]
    fn pointer_alignment_can_differ_from_pointer_size() {
        let (pointer_size, pointer_align) =
            pointer_layout("E-m:e-p:32:16:32-i8:8:8-i16:16:16-i32:16:32-n8:16:32-a:0:16-S16");

        assert_eq!(pointer_size, 4);
        assert_eq!(pointer_align, 2);
    }

    #[test]
    fn pointer_alignment_matches_size_on_common_x86_64_layout() {
        let (pointer_size, pointer_align) = pointer_layout(
            "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128",
        );

        assert_eq!(pointer_size, 8);
        assert_eq!(pointer_align, 8);
    }

    #[test]
    fn explicit_optimization_overrides_profile_backend_policy() {
        assert_eq!(
            backend_optimization_level(BuildProfile::Debug, OptimizationMode::Level(OptLevel::O2),),
            LlvmOptimizationLevel::Default
        );
        assert_eq!(
            backend_optimization_level(
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::O0),
            ),
            LlvmOptimizationLevel::None
        );
        assert_eq!(
            backend_optimization_level(BuildProfile::Debug, OptimizationMode::Level(OptLevel::O3),),
            LlvmOptimizationLevel::Aggressive
        );
    }

    #[test]
    fn host_target_emits_objects_for_both_profiles() {
        let dcx = diagnostics();
        for profile in [BuildProfile::Debug, BuildProfile::Release] {
            let layout = TargetLayout::new(&dcx, None, profile)
                .unwrap_or_else(|_| panic!("host target layout should initialize"));
            let object = emit_smoke_object(&layout, "host-object-smoke");
            assert!(!object.is_empty());
        }
    }

    #[test]
    fn cross_targets_emit_linux_and_macos_objects() {
        let dcx = diagnostics();
        let cases: [(&str, &[u8]); 2] = [
            ("x86_64-unknown-linux-gnu", b"\x7fELF"),
            ("aarch64-apple-darwin", b"\xcf\xfa\xed\xfe"),
        ];

        for (triple, magic) in cases {
            let layout = TargetLayout::new(&dcx, Some(triple), BuildProfile::Debug)
                .unwrap_or_else(|_| panic!("cross target layout should initialize"));
            assert_eq!(layout.requested_triple(), Some(triple));
            let object = emit_smoke_object(&layout, "cross-object-smoke");
            assert!(
                object.starts_with(magic),
                "object for {triple} did not use the expected file format"
            );
        }
    }
}
