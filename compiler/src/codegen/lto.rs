use std::{fs, path::Path, time::Instant};

use inkwell::{
    context::Context,
    data_layout::DataLayout,
    memory_buffer::MemoryBuffer,
    module::Module,
    passes::PassBuilderOptions,
    targets::{FileType, TargetMachine, TargetTriple},
};

use crate::{
    codegen::artifact::ModuleArtifact,
    compile::{
        config::{BuildProfile, LtoMode, ModuleArtifactKind, OptLevel, OptimizationMode},
        context::GlobalContext,
    },
    error::CompileResult,
};

fn full_lto_pipeline(profile: BuildProfile, optimization: OptimizationMode) -> &'static str {
    match optimization {
        // Baseline remains useful for compiler comparisons. Debug maps to O0;
        // the historical release baseline is closest to LLVM's O2 backend.
        OptimizationMode::Baseline => match profile {
            BuildProfile::Debug => "lto<O0>",
            BuildProfile::Release => "lto<O2>",
        },
        OptimizationMode::Level(OptLevel::O0) => "lto<O0>",
        OptimizationMode::Level(OptLevel::O1) => "lto<O1>",
        OptimizationMode::Level(OptLevel::O2) => "lto<O2>",
        OptimizationMode::Level(OptLevel::O3) => "lto<O3>",
        OptimizationMode::Level(OptLevel::Os) => "lto<Os>",
        OptimizationMode::Level(OptLevel::Oz) => "lto<Oz>",
    }
}

fn parse_bitcode<'ctx>(
    context: &'ctx Context,
    path: &Path,
    expected_triple: &TargetTriple,
    expected_layout: &DataLayout,
) -> Result<Module<'ctx>, String> {
    // Inkwell's path-based loader requires Unicode paths. Reading bytes through
    // std::fs preserves every valid platform path and lets us attach a stable
    // diagnostic name to the LLVM memory buffer.
    let mut bytes = fs::read(path)
        .map_err(|error| format!("failed to read LTO input '{}': {error}", path.display()))?;
    bytes.push(0);
    let buffer = MemoryBuffer::create_from_memory_range_copy(&bytes, "taro-full-lto-input");
    let module = Module::parse_bitcode_from_buffer(&buffer, context).map_err(|error| {
        format!(
            "failed to parse LLVM bitcode for full LTO from '{}': {error}",
            path.display()
        )
    })?;

    if module.get_triple() != *expected_triple {
        return Err(format!(
            "LTO input '{}' targets `{}`, expected `{}`",
            path.display(),
            module.get_triple(),
            expected_triple
        ));
    }
    if module.get_data_layout().as_str() != expected_layout.as_str() {
        return Err(format!(
            "LTO input '{}' has an incompatible target data layout",
            path.display()
        ));
    }

    Ok(module)
}

fn optimize_full_lto_module(
    module: &Module<'_>,
    target_machine: &TargetMachine,
    pipeline: &'static str,
) -> Result<(), String> {
    let options = PassBuilderOptions::create();
    options.set_verify_each(cfg!(test));
    module
        .run_passes(pipeline, target_machine, options)
        .map_err(|error| error.to_string())
}

/// Merge every participating Taro bitcode module, run LLVM's full-LTO
/// post-link pipeline, and emit one native object for the platform linker.
///
/// Native inputs such as attached std and the Rust runtime intentionally stay
/// outside this operation and are linked after the returned object.
pub fn emit_full_lto_object(gcx: GlobalContext<'_>) -> CompileResult<ModuleArtifact> {
    if gcx.config.codegen.lto != LtoMode::Full
        || gcx.config.codegen.artifact != ModuleArtifactKind::LlvmBitcode
    {
        gcx.dcx().emit_error(
            "full LTO requires LLVM bitcode module artifacts".into(),
            None,
        );
        return Err(crate::error::ReportedError);
    }

    let Some(root_artifact) = gcx.get_module_artifact(gcx.package_index()) else {
        gcx.dcx().emit_error(
            "root LLVM bitcode artifact is missing for full LTO".into(),
            None,
        );
        return Err(crate::error::ReportedError);
    };
    if root_artifact.kind != ModuleArtifactKind::LlvmBitcode {
        gcx.dcx().emit_error(
            "root module artifact is not LLVM bitcode for full LTO".into(),
            None,
        );
        return Err(crate::error::ReportedError);
    }

    let mut inputs = vec![root_artifact];
    inputs.extend(
        gcx.module_artifacts()
            .into_iter()
            .filter(|(package, artifact)| {
                *package != gcx.package_index() && artifact.kind == ModuleArtifactKind::LlvmBitcode
            })
            .map(|(_, artifact)| artifact),
    );

    let started_at = Instant::now();
    let context = Context::create();
    let expected_triple = gcx.store.target_layout.triple();
    let expected_layout = gcx.store.target_layout.data_layout();
    let mut modules = inputs.iter().map(|artifact| {
        parse_bitcode(&context, &artifact.path, &expected_triple, &expected_layout)
    });
    let merged = modules
        .next()
        .expect("root bitcode guarantees at least one LTO module")
        .map_err(|message| {
            gcx.dcx().emit_error(message, None);
            crate::error::ReportedError
        })?;
    for module in modules {
        let module = module.map_err(|message| {
            gcx.dcx().emit_error(message, None);
            crate::error::ReportedError
        })?;
        merged.link_in_module(module).map_err(|error| {
            gcx.dcx().emit_error(
                format!("failed to merge LLVM modules for full LTO: {error}"),
                None,
            );
            crate::error::ReportedError
        })?;
    }

    merged.verify().map_err(|error| {
        gcx.dcx().emit_error(
            format!("full-LTO module verification failed before optimization: {error}"),
            None,
        );
        crate::error::ReportedError
    })?;

    let target_machine = gcx.store.target_layout.create_target_machine(
        gcx.dcx(),
        gcx.config.profile,
        gcx.config.codegen.optimization,
    )?;
    let pipeline = full_lto_pipeline(gcx.config.profile, gcx.config.codegen.optimization);
    optimize_full_lto_module(&merged, &target_machine, pipeline).map_err(|error| {
        gcx.dcx().emit_error(
            format!("LLVM full-LTO pipeline `{pipeline}` failed: {error}"),
            None,
        );
        crate::error::ReportedError
    })?;
    merged.verify().map_err(|error| {
        gcx.dcx().emit_error(
            format!("full-LTO module verification failed after optimization: {error}"),
            None,
        );
        crate::error::ReportedError
    })?;

    if gcx.config.debug.dump_llvm {
        eprintln!("\n=== Full LTO LLVM IR for {} ===", gcx.config.name);
        eprintln!("{}", merged.print_to_string());
        eprintln!("=== End Full LTO LLVM Dump ===\n");
    }

    fs::create_dir_all(gcx.output_root()).map_err(|error| {
        gcx.dcx().emit_error(
            format!("failed to create full-LTO output directory: {error}"),
            None,
        );
        crate::error::ReportedError
    })?;
    let output = gcx
        .output_root()
        .join(format!("{}.lto.o", gcx.config.identifier));
    target_machine
        .write_to_file(&merged, FileType::Object, &output)
        .map_err(|error| {
            gcx.dcx()
                .emit_error(format!("failed to write full-LTO object: {error}"), None);
            crate::error::ReportedError
        })?;

    let module_suffix = if inputs.len() == 1 { "" } else { "s" };
    if gcx.config.debug.timings {
        eprintln!(
            "Full LTO – {} module{} in {:.3} ms",
            inputs.len(),
            module_suffix,
            started_at.elapsed().as_secs_f64() * 1000.0
        );
    } else {
        eprintln!("Full LTO – {} module{}", inputs.len(), module_suffix);
    }
    Ok(ModuleArtifact::new(ModuleArtifactKind::Object, output))
}

#[cfg(test)]
mod tests {
    use super::{full_lto_pipeline, optimize_full_lto_module, parse_bitcode};
    use crate::{
        codegen::target::TargetLayout,
        compile::config::{BuildProfile, OptLevel, OptimizationMode},
        diagnostics::DiagCtx,
    };
    use inkwell::{context::Context, values::AnyValue};
    use std::{fs, path::PathBuf};

    fn temporary_bitcode_path(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "taro-full-lto-{name}-{}-{}.bc",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ))
    }

    #[test]
    fn full_lto_pipeline_tracks_optimization_policy() {
        assert_eq!(
            full_lto_pipeline(BuildProfile::Debug, OptimizationMode::Baseline),
            "lto<O0>"
        );
        assert_eq!(
            full_lto_pipeline(BuildProfile::Release, OptimizationMode::Level(OptLevel::O3)),
            "lto<O3>"
        );
        assert_eq!(
            full_lto_pipeline(BuildProfile::Release, OptimizationMode::Level(OptLevel::Oz)),
            "lto<Oz>"
        );
    }

    #[test]
    fn bitcode_loader_validates_target_identity() {
        let diagnostics = DiagCtx::new(PathBuf::from("."));
        let layout = TargetLayout::new(&diagnostics, None, BuildProfile::Release)
            .unwrap_or_else(|_| panic!("host target layout"));
        let source_context = Context::create();
        let module = source_context.create_module("lto-input");
        module.set_triple(&layout.triple());
        module.set_data_layout(&layout.data_layout());
        module.add_function(
            "dependency",
            source_context.void_type().fn_type(&[], false),
            None,
        );
        let path = temporary_bitcode_path("target-identity");
        let bytes = module.write_bitcode_to_memory();
        let bytes = bytes
            .as_slice()
            .strip_suffix(&[0])
            .unwrap_or(bytes.as_slice());
        fs::write(&path, bytes).expect("write bitcode");

        let parse_context = Context::create();
        let parsed = parse_bitcode(
            &parse_context,
            &path,
            &layout.triple(),
            &layout.data_layout(),
        )
        .expect("matching target should parse");
        assert!(parsed.get_function("dependency").is_some());

        let x86_linux = inkwell::targets::TargetTriple::create("x86_64-unknown-linux-gnu");
        let wrong_triple = if layout.triple() == x86_linux {
            inkwell::targets::TargetTriple::create("aarch64-unknown-linux-gnu")
        } else {
            x86_linux
        };
        let error = parse_bitcode(&parse_context, &path, &wrong_triple, &layout.data_layout())
            .expect_err("mismatched target should fail");
        assert!(error.contains("expected"));
        let _ = fs::remove_file(path);
    }

    #[test]
    fn full_lto_optimizes_across_linked_module_boundaries() {
        let diagnostics = DiagCtx::new(PathBuf::from("."));
        let layout = TargetLayout::new(&diagnostics, None, BuildProfile::Release)
            .unwrap_or_else(|_| panic!("host target layout"));
        let context = Context::create();
        let root = context.create_module("root");
        let dependency = context.create_module("dependency");
        for module in [&root, &dependency] {
            module.set_triple(&layout.triple());
            module.set_data_layout(&layout.data_layout());
        }

        let function_type = context.i32_type().fn_type(&[], false);
        let dependency_function = dependency.add_function("dependency_value", function_type, None);
        let dependency_block = context.append_basic_block(dependency_function, "entry");
        let dependency_builder = context.create_builder();
        dependency_builder.position_at_end(dependency_block);
        dependency_builder
            .build_return(Some(&context.i32_type().const_int(42, false)))
            .expect("dependency return");

        let dependency_declaration = root.add_function("dependency_value", function_type, None);
        let entry = root.add_function("main", function_type, None);
        let entry_block = context.append_basic_block(entry, "entry");
        let entry_builder = context.create_builder();
        entry_builder.position_at_end(entry_block);
        let call = entry_builder
            .build_call(dependency_declaration, &[], "dependency_call")
            .expect("dependency call")
            .try_as_basic_value()
            .basic()
            .expect("dependency return value");
        entry_builder
            .build_return(Some(&call))
            .expect("entry return");

        root.link_in_module(dependency)
            .expect("modules should link");
        let target_machine = layout
            .create_target_machine(
                &diagnostics,
                BuildProfile::Release,
                OptimizationMode::Level(OptLevel::O2),
            )
            .unwrap_or_else(|_| panic!("target machine"));
        optimize_full_lto_module(&root, &target_machine, "lto<O2>")
            .expect("full LTO should optimize");

        let entry_ir = root
            .get_function("main")
            .expect("main should remain")
            .print_to_string()
            .to_string();
        assert!(entry_ir.contains("ret i32 42"), "{entry_ir}");
        assert!(
            !entry_ir.contains("call i32 @dependency_value"),
            "{entry_ir}"
        );
    }
}
