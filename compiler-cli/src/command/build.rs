use super::{
    compile_paths::{profile_dir_name, script_target_dir},
    incremental, runtime_artifact, std_attached,
};
use crate::{
    BuildEmit, CommonCompileArgs, CompileModeOptions, Lto, TestArgs,
    package::{
        manifest::ValidatedDependencyGraph,
        sync::sync_dependencies,
        utils::{get_package_name, language_home},
    },
};
use compiler::{
    PackageIndex, codegen,
    codegen::artifact::ModuleArtifact,
    compile::{
        Compiler,
        config::{Config, DebugOptions, ModuleArtifactKind, PackageKind, StdMode},
        context::{CompilerArenas, CompilerContext, CompilerStore, GlobalContext},
        test_collector::TestSelection,
    },
    constants::STD_PREFIX,
    diagnostics::DiagCtx,
    error::ReportedError,
    metadata::{self, MetadataLoadStatus, ReuseMode},
};
use rustc_hash::FxHashMap;
use std::{fs, path::PathBuf, process::Command, rc::Rc};

pub fn run(
    arguments: CommonCompileArgs,
    require_executable: bool,
    emit: BuildEmit,
    lto: Lto,
) -> Result<Option<std::path::PathBuf>, ReportedError> {
    if let Err(message) = validate_build_modes(emit, lto) {
        eprintln!("error: {message}");
        return Err(ReportedError);
    }
    if arguments.is_single_file() {
        run_single_file(arguments, emit, lto)
    } else {
        run_package(arguments, require_executable, emit, lto)
    }
}

fn validate_build_modes(emit: BuildEmit, lto: Lto) -> Result<(), &'static str> {
    if matches!((emit, lto), (BuildEmit::LlvmBitcode, Lto::Full)) {
        return Err(
            "--emit llvm-bc cannot be combined with --lto full; LLVM bitcode output is package-scoped",
        );
    }
    Ok(())
}

fn run_single_file(
    arguments: CommonCompileArgs,
    emit: BuildEmit,
    lto: Lto,
) -> Result<Option<std::path::PathBuf>, ReportedError> {
    let mut compile_options = arguments.compile_mode_options();
    compile_options.codegen.artifact = emit.module_artifact_kind(lto);
    compile_options.codegen.lto = lto.mode();
    let profile_dir = profile_dir_name(compile_options.profile);
    let cwd = std::env::current_dir().map_err(|e| {
        eprintln!("error: failed to get current directory: {}", e);
        ReportedError
    })?;
    let dcx = Rc::new(DiagCtx::new(cwd.clone()));
    let arenas = CompilerArenas::new();

    // Resolve file path and extract name
    let file_path = arguments.path.canonicalize().map_err(|e| {
        eprintln!(
            "error: failed to canonicalize file path '{}': {}",
            arguments.path.display(),
            e
        );
        ReportedError
    })?;

    let file_stem = file_path
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| {
            eprintln!(
                "error: failed to extract filename from '{}'",
                file_path.display()
            );
            ReportedError
        })?;
    let bitcode_output = arguments
        .output
        .clone()
        .unwrap_or_else(|| default_script_bitcode_output(&cwd, file_stem));

    // Create target directory based on file path hash
    let target_root = script_target_dir(&file_path, profile_dir);
    std::fs::create_dir_all(&target_root).map_err(|e| {
        eprintln!(
            "error: failed to create target directory '{}': {}",
            target_root.display(),
            e
        );
        ReportedError
    })?;

    let store = CompilerStore::new(
        &arenas,
        target_root.join("objects"),
        &dcx,
        arguments.target.clone(),
        compile_options.profile,
    )?;
    store.configure_linker(arguments.linker.clone(), arguments.sysroot.clone());
    let icx = CompilerContext::new(dcx, store);
    let mut package_fingerprints = FxHashMap::default();
    let incremental_enabled = !arguments.no_incremental;

    // Compile std (index 0)
    compile_std(
        &icx,
        arguments.std_path.clone(),
        compile_options,
        arguments.build_std,
        &mut package_fingerprints,
    )?;
    if matches!(emit, BuildEmit::Link) {
        build_runtime(&icx, &target_root, arguments.runtime_path.clone())?;
    }

    // Create virtual config for single file
    let package_index = PackageIndex::new(1);
    let mut dependencies = FxHashMap::default();
    dependencies.insert("std".into(), "std".into());

    let config = icx.store.arenas.configs.alloc(Config {
        name: file_stem.into(),
        identifier: format!("script-{}", file_stem).into(),
        src: file_path.clone(),
        dependencies,
        index: package_index,
        kind: PackageKind::Executable,
        executable_out: if matches!(emit, BuildEmit::Link) {
            arguments.output.clone()
        } else {
            None
        },
        no_std_prelude: false,
        is_script: true,
        profile: compile_options.profile,
        codegen: compile_options.codegen,
        overflow_checks: compile_options.overflow_checks,
        debug: DebugOptions {
            dump_mir: arguments.dump_mir,
            dump_llvm: arguments.dump_llvm,
            timings: arguments.timings,
            debug_info: compile_options.debug_info,
        },
        test_mode: false,
        std_mode: StdMode::FullStd,
        is_std_provider: false,
    });

    let mut compiler = Compiler::new(&icx, config);
    let fingerprint_input =
        incremental::compute_package_fingerprint_input(&icx, config, &package_fingerprints)
            .map_err(|e| {
                icx.dcx.emit_error(
                    format!(
                        "failed to compute fingerprint for script '{}': {}",
                        file_stem, e
                    ),
                    None,
                );
                ReportedError
            })?;

    let reused = if incremental_enabled {
        match metadata::try_load_package_metadata(
            compiler.context,
            &fingerprint_input,
            ReuseMode::CodegenRoot,
        ) {
            MetadataLoadStatus::Hit(hit) => match metadata::hydrate_loaded_metadata(
                compiler.context,
                &hit,
                ReuseMode::CodegenRoot,
            ) {
                Ok(()) => {
                    eprintln!(
                        "Reusing (metadata+{}) – {}",
                        artifact_label(compile_options.codegen.artifact),
                        file_stem
                    );
                    true
                }
                Err(e) => {
                    eprintln!("Compiling – {} (metadata hydrate miss: {})", file_stem, e);
                    false
                }
            },
            MetadataLoadStatus::Miss(reason) => {
                if compiler.context.config.debug.timings {
                    eprintln!("Compiling – {} (metadata miss: {})", file_stem, reason);
                } else {
                    eprintln!("Compiling – {}", file_stem);
                }
                false
            }
        }
    } else {
        eprintln!("Compiling – {}", file_stem);
        false
    };

    if reused {
        match emit {
            BuildEmit::Link => link_emitted_modules(compiler.context, lto),
            BuildEmit::LlvmBitcode => {
                let artifact = cached_module_artifact(compiler.context)?;
                publish_bitcode(&artifact, bitcode_output).map(Some)
            }
        }
    } else {
        let output = match emit {
            BuildEmit::Link => match lto {
                Lto::Off => compiler.build()?,
                Lto::Full => {
                    let _ = compiler.emit_module()?;
                    None
                }
            },
            BuildEmit::LlvmBitcode => {
                let artifact = compiler.emit_module()?;
                Some(publish_bitcode(&artifact, bitcode_output)?)
            }
        };
        if let Err(e) = metadata::write_package_metadata(
            compiler.context,
            &fingerprint_input,
            ReuseMode::CodegenRoot,
        ) {
            eprintln!(
                "warning: failed to write metadata for '{}': {}",
                file_stem, e
            );
        }
        if matches!((emit, lto), (BuildEmit::Link, Lto::Full)) {
            link_emitted_modules(compiler.context, lto)
        } else {
            Ok(output)
        }
    }
}

fn run_package(
    arguments: CommonCompileArgs,
    require_executable: bool,
    emit: BuildEmit,
    lto: Lto,
) -> Result<Option<std::path::PathBuf>, ReportedError> {
    let mut compile_options = arguments.compile_mode_options();
    compile_options.codegen.artifact = emit.module_artifact_kind(lto);
    compile_options.codegen.lto = lto.mode();
    let profile_dir = profile_dir_name(compile_options.profile);
    let cwd = std::env::current_dir().map_err(|e| {
        eprintln!("error: failed to get current directory: {}", e);
        ReportedError
    })?;
    let dcx = Rc::new(DiagCtx::new(cwd));
    let arenas = CompilerArenas::new();
    let project_root = arguments.path.canonicalize().map_err(|e| {
        eprintln!(
            "error: failed to canonicalize project root path '{}': {}",
            arguments.path.display(),
            e
        );
        ReportedError
    })?;
    let profile_root = project_root.join("target").join(profile_dir);
    let target_root = profile_root.join("objects");
    let store = CompilerStore::new(
        &arenas,
        target_root,
        &dcx,
        arguments.target.clone(),
        compile_options.profile,
    )?;
    store.configure_linker(arguments.linker.clone(), arguments.sysroot.clone());
    let icx = CompilerContext::new(dcx, store);
    let mut package_fingerprints = FxHashMap::default();
    let incremental_enabled = !arguments.no_incremental;
    let sync_options = arguments.sync_options();

    let graph = sync_dependencies(arguments.path.clone(), sync_options)?;

    let root_is_std = is_root_std_package(&graph, arguments.std_path.clone(), &icx)?;

    if !root_is_std {
        let _ = compile_std(
            &icx,
            arguments.std_path.clone(),
            compile_options,
            arguments.build_std,
            &mut package_fingerprints,
        )?;
        if matches!(emit, BuildEmit::Link) {
            build_runtime(&icx, &project_root, arguments.runtime_path.clone())?;
        }
    }

    let total = graph.ordered.len();

    for (index, package) in graph.ordered.iter().enumerate() {
        let is_root = index + 1 == total;
        if !is_root && !matches!(package.kind, PackageKind::Library | PackageKind::Both) {
            icx.dcx.emit_error(
                format!(
                    "dependency `{}` must be a library (found {:?})",
                    package.package.0, package.kind
                ),
                None,
            );
            return Err(ReportedError);
        }

        if is_root && require_executable {
            if package.kind == PackageKind::Library {
                icx.dcx.emit_error(
                    "`run` requires the root package to be executable".into(),
                    None,
                );
                return Err(ReportedError);
            }
        }

        let package_index = PackageIndex::new(index + 1);
        let name = get_package_name(&package.package.0).map_err(|e| {
            icx.dcx.emit_error(
                format!(
                    "failed to get package name for '{}': {}",
                    package.package.0, e
                ),
                None,
            );
            ReportedError
        })?;
        let bitcode_output = is_root.then(|| {
            arguments
                .output
                .clone()
                .unwrap_or_else(|| default_package_bitcode_output(&profile_root, &name))
        });
        let is_std_package = root_is_std && is_root;
        let identifier = if is_std_package {
            STD_PREFIX.into()
        } else {
            package.unique_identifier().map_err(|e| {
                icx.dcx.emit_error(
                    format!(
                        "failed to generate unique identifier for '{}': {}",
                        package.package.0, e
                    ),
                    None,
                );
                ReportedError
            })?
        };
        let mut dependencies = graph.dependencies_for(package).map_err(|e| {
            icx.dcx.emit_error(
                format!(
                    "failed to resolve dependencies for '{}': {}",
                    package.package.0, e
                ),
                None,
            );
            ReportedError
        })?;
        if !is_std_package {
            dependencies.insert("std".into(), "std".into());
        }

        let src = package
            .path()
            .and_then(|p| {
                p.canonicalize()
                    .map_err(|e| format!("failed to resolve path – {}", e))
            })
            .map_err(|e| format!("failed to resolve path – {}", e))
            .map_err(|e| {
                icx.dcx.emit_error(
                    format!(
                        "failed to resolve source path for '{}': {}",
                        package.package.0, e
                    ),
                    None,
                );
                ReportedError
            })?;
        let config = icx.store.arenas.configs.alloc(Config {
            name,
            identifier,
            src,
            dependencies,
            index: package_index,
            kind: package.kind,
            executable_out: if matches!(emit, BuildEmit::Link) {
                arguments.output.clone()
            } else {
                None
            },
            no_std_prelude: package.no_std_prelude,
            is_script: false,
            profile: compile_options.profile,
            codegen: compile_options.codegen,
            // std intentionally relies on wrapping arithmetic (e.g. SipHash)
            // and always compiles without overflow checks, like attached std.
            overflow_checks: compile_options.overflow_checks && !is_std_package,
            debug: DebugOptions {
                dump_mir: arguments.dump_mir,
                dump_llvm: arguments.dump_llvm,
                timings: arguments.timings,
                debug_info: compile_options.debug_info,
            },
            test_mode: false,
            std_mode: if is_std_package {
                StdMode::BootstrapStd
            } else {
                StdMode::FullStd
            },
            is_std_provider: is_std_package,
        });

        let fingerprint_input =
            incremental::compute_package_fingerprint_input(&icx, config, &package_fingerprints)
                .map_err(|e| {
                    icx.dcx.emit_error(
                        format!(
                            "failed to compute fingerprint for package '{}': {}",
                            package.package.0, e
                        ),
                        None,
                    );
                    ReportedError
                })?;

        let mut compiler = Compiler::new(&icx, config);
        let reuse_mode = if is_root {
            ReuseMode::CodegenRoot
        } else {
            ReuseMode::CodegenDependency
        };
        let can_attempt_reuse = incremental_enabled;
        let reused = if can_attempt_reuse {
            match metadata::try_load_package_metadata(
                compiler.context,
                &fingerprint_input,
                reuse_mode,
            ) {
                MetadataLoadStatus::Hit(hit) => {
                    match metadata::hydrate_loaded_metadata(compiler.context, &hit, reuse_mode) {
                        Ok(()) => {
                            if is_root || compiler.context.config.debug.timings {
                                eprintln!(
                                    "Reusing (metadata+{}) – {}",
                                    artifact_label(compile_options.codegen.artifact),
                                    package.package.0
                                );
                            }
                            true
                        }
                        Err(e) => {
                            eprintln!(
                                "Compiling – {} (metadata hydrate miss: {})",
                                package.package.0, e
                            );
                            false
                        }
                    }
                }
                MetadataLoadStatus::Miss(reason) => {
                    if compiler.context.config.debug.timings {
                        eprintln!(
                            "Compiling – {} (metadata miss: {})",
                            package.package.0, reason
                        );
                    } else {
                        eprintln!("Compiling – {}", package.package.0);
                    }
                    false
                }
            }
        } else {
            eprintln!("Compiling – {}", package.package.0);
            false
        };

        let exe_path = if reused {
            if is_root {
                match emit {
                    BuildEmit::Link => match lto {
                        Lto::Off => codegen::link::link_executable(compiler.context)?,
                        // Finalization happens below after both cold and cached
                        // paths have restored every participating module.
                        Lto::Full => None,
                    },
                    BuildEmit::LlvmBitcode => {
                        let artifact = cached_module_artifact(compiler.context)?;
                        Some(publish_bitcode(
                            &artifact,
                            bitcode_output
                                .clone()
                                .expect("root bitcode output should be selected"),
                        )?)
                    }
                }
            } else {
                None
            }
        } else {
            let exe_path = match emit {
                BuildEmit::Link => match lto {
                    Lto::Off => compiler.build()?,
                    Lto::Full => {
                        let _ = compiler.emit_module()?;
                        None
                    }
                },
                BuildEmit::LlvmBitcode => {
                    let artifact = compiler.emit_module()?;
                    if is_root {
                        Some(publish_bitcode(
                            &artifact,
                            bitcode_output
                                .clone()
                                .expect("root bitcode output should be selected"),
                        )?)
                    } else {
                        None
                    }
                }
            };
            if let Err(e) =
                metadata::write_package_metadata(compiler.context, &fingerprint_input, reuse_mode)
            {
                eprintln!(
                    "warning: failed to write metadata for '{}': {}",
                    package.package.0, e
                );
            }
            exe_path
        };

        let exe_path = if is_root
            && matches!(lto, Lto::Full)
            && matches!(config.kind, PackageKind::Executable | PackageKind::Both)
        {
            link_emitted_modules(compiler.context, lto)?
        } else {
            exe_path
        };

        package_fingerprints.insert(
            config.identifier.to_string(),
            fingerprint_input.package_fingerprint,
        );

        if exe_path.is_some() {
            return Ok(exe_path);
        }
    }
    Ok(None)
}

fn link_emitted_modules(
    context: GlobalContext<'_>,
    lto: Lto,
) -> Result<Option<PathBuf>, ReportedError> {
    if matches!(lto, Lto::Full) {
        let artifact = codegen::lto::emit_full_lto_object(context)?;
        context.store.add_link_input(artifact.path);
    }
    codegen::link::link_executable(context)
}

fn artifact_label(kind: ModuleArtifactKind) -> &'static str {
    match kind {
        ModuleArtifactKind::Object => "object",
        ModuleArtifactKind::LlvmBitcode => "bitcode",
    }
}

fn default_script_bitcode_output(cwd: &std::path::Path, file_stem: &str) -> PathBuf {
    cwd.join(format!("{file_stem}.bc"))
}

fn default_package_bitcode_output(profile_root: &std::path::Path, package_name: &str) -> PathBuf {
    profile_root.join(format!("{package_name}.bc"))
}

fn cached_module_artifact(context: GlobalContext<'_>) -> Result<ModuleArtifact, ReportedError> {
    context
        .get_module_artifact(context.package_index())
        .ok_or_else(|| {
            context.dcx().emit_error(
                "incremental metadata did not restore a module artifact".into(),
                None,
            );
            ReportedError
        })
}

fn publish_bitcode(artifact: &ModuleArtifact, output: PathBuf) -> Result<PathBuf, ReportedError> {
    if artifact.kind != ModuleArtifactKind::LlvmBitcode {
        eprintln!(
            "error: expected LLVM bitcode, compiler produced {}",
            artifact.kind.display_name()
        );
        return Err(ReportedError);
    }

    if let Some(parent) = output
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
    {
        fs::create_dir_all(parent).map_err(|error| {
            eprintln!(
                "error: failed to create bitcode output directory '{}': {}",
                parent.display(),
                error
            );
            ReportedError
        })?;
    }

    let source_is_output = artifact.path == output
        || output.exists() && artifact.path.canonicalize().ok() == output.canonicalize().ok();
    if !source_is_output {
        fs::copy(&artifact.path, &output).map_err(|error| {
            eprintln!(
                "error: failed to publish LLVM bitcode to '{}': {}",
                output.display(),
                error
            );
            ReportedError
        })?;
    }

    eprintln!("Emitted LLVM bitcode – {}", output.display());
    Ok(output)
}

/// Locates and links the Taro runtime library.
///
/// This function attempts to find `libtaro_runtime.a` using the following priority:
/// 1. `--runtime-path` CLI argument.
/// 2. `TARO_RUNTIME_LIB` environment variable.
/// 3. Target-specific `TARO_HOME/lib/taro/runtime` directory.
/// 4. Relative to the executable (distribution layout).
/// 5. Fallback to `cargo build` (dev mode only).
fn build_runtime(
    ctx: &CompilerContext<'_>,
    project_root: &PathBuf,
    runtime_arg: Option<PathBuf>,
) -> Result<(), ReportedError> {
    // 1. CLI Arg
    if let Some(path) = runtime_arg {
        if path.exists() {
            return add_runtime_link_input(ctx, path);
        }
        ctx.dcx.emit_error(
            format!(
                "runtime library not found at specified path: {}",
                path.display()
            ),
            None,
        );
        return Err(ReportedError);
    }

    // 2. Env Var
    if let Ok(val) = std::env::var("TARO_RUNTIME_LIB") {
        let path = PathBuf::from(val);
        if path.exists() {
            return add_runtime_link_input(ctx, path);
        }
        ctx.dcx.emit_error(
            format!(
                "runtime library from TARO_RUNTIME_LIB does not exist: {}",
                path.display()
            ),
            None,
        );
        return Err(ReportedError);
    }

    // 3. TARO_HOME
    if let Ok(home) = language_home() {
        let path = installed_runtime_path(&home, ctx.store.target_layout.requested_triple());
        if path.exists() {
            return add_runtime_link_input(ctx, path);
        }
    }

    // 4. Relative to Executable (Dist)
    if let Ok(exe) = std::env::current_exe() {
        if let Some(bin_dir) = exe.parent() {
            if let Some(root) = bin_dir.parent() {
                let path = installed_runtime_path(root, ctx.store.target_layout.requested_triple());
                if path.exists() {
                    return add_runtime_link_input(ctx, path);
                }
            }
        }
    }

    // 5. Fallback (Development Mode)
    // If we're strictly in a dev environment (source checkout), we invoke cargo to build it.
    // This supports `cargo run` workflows for compiler developers without needing a full `dist` build.
    // We detect this relying on `CARGO_MANIFEST_DIR` which is set at compile time of the CLI.

    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .ok_or(ReportedError)?
        .to_path_buf();
    let target_dir = project_root.join("target").join("runtime");

    // Check if the runtime crate exists in the workspace before trying to build it.
    if !workspace_root.join("runtime").join("Cargo.toml").exists() {
        ctx.dcx.emit_error(
            "runtime library not found and cannot be built (not in a workspace)".into(),
            None,
        );
        return Err(ReportedError);
    }

    let requested_target = ctx.store.target_layout.requested_triple();
    let mut command = Command::new("cargo");
    command
        .arg("build")
        .arg("--release")
        .arg("--quiet")
        .arg("-p")
        .arg("taro-runtime")
        .arg("--manifest-path")
        .arg(workspace_root.join("Cargo.toml"))
        .arg("--target-dir")
        .arg(&target_dir);
    if let Some(target) = requested_target {
        command.arg("--target").arg(target);
    }
    let status = command.status().map_err(|e| {
        ctx.dcx.emit_error(
            format!("failed to invoke cargo to build runtime: {e}"),
            None,
        );
        ReportedError
    })?;

    if !status.success() {
        let target = requested_target
            .map(|target| format!(" for target `{target}`"))
            .unwrap_or_default();
        ctx.dcx.emit_error(
            format!("failed to build runtime crate{target}; install the Rust target or pass --runtime-path"),
            None,
        );
        return Err(ReportedError);
    }

    let lib_path = if let Some(target) = requested_target {
        target_dir
            .join(target)
            .join("release")
            .join("libtaro_runtime.a")
    } else {
        target_dir.join("release").join("libtaro_runtime.a")
    };
    if !lib_path.exists() {
        ctx.dcx.emit_error(
            format!("runtime archive not found at {}", lib_path.display()),
            None,
        );
        return Err(ReportedError);
    }

    if let Err(error) = runtime_artifact::write_manifest(&lib_path, requested_target) {
        ctx.dcx.emit_error(error, None);
        return Err(ReportedError);
    }

    // Make the runtime archive available to the existing link step by treating it like another
    // "object file" input.
    add_runtime_link_input(ctx, lib_path)
}

fn add_runtime_link_input(
    ctx: &CompilerContext<'_>,
    runtime: PathBuf,
) -> Result<(), ReportedError> {
    if let Err(error) = runtime_artifact::validate(
        &runtime,
        ctx.store.target_layout.requested_triple(),
        &ctx.store.target_layout.triple_string(),
    ) {
        ctx.dcx.emit_error(error, None);
        return Err(ReportedError);
    }
    ctx.store.add_link_input(runtime);
    Ok(())
}

fn installed_runtime_path(toolchain_root: &std::path::Path, target: Option<&str>) -> PathBuf {
    let runtime_root = toolchain_root.join("lib").join("taro").join("runtime");
    match target {
        Some(target) => runtime_root.join(target).join("libtaro_runtime.a"),
        None => runtime_root.join("libtaro_runtime.a"),
    }
}

fn compile_std<'a>(
    ctx: &'a CompilerContext<'a>,
    std_path: Option<PathBuf>,
    compile_options: CompileModeOptions,
    build_std: bool,
    package_fingerprints: &mut FxHashMap<String, String>,
) -> Result<(), ReportedError> {
    std_attached::compile_std(
        ctx,
        std_path,
        compile_options,
        build_std,
        package_fingerprints,
        ReuseMode::CodegenDependency,
    )
}

fn is_root_std_package(
    graph: &ValidatedDependencyGraph,
    std_path: Option<PathBuf>,
    ctx: &CompilerContext<'_>,
) -> Result<bool, ReportedError> {
    std_attached::is_root_std_package(graph, std_path, ctx)
}

// ─── Test mode build ──────────────────────────────────────────────────

pub fn run_test_mode(arguments: TestArgs) -> Result<Option<std::path::PathBuf>, ReportedError> {
    let selection = TestSelection::new(
        arguments.normalized_test_filter(),
        arguments.normalized_test_tags(),
    );
    let arguments = arguments.common;

    if arguments.is_single_file() {
        run_single_file_test(arguments, &selection)
    } else {
        run_package_test(arguments, &selection)
    }
}

fn run_single_file_test(
    arguments: CommonCompileArgs,
    selection: &TestSelection,
) -> Result<Option<std::path::PathBuf>, ReportedError> {
    let compile_options = arguments.compile_mode_options();
    let profile_dir = profile_dir_name(compile_options.profile);
    let cwd = std::env::current_dir().map_err(|e| {
        eprintln!("error: failed to get current directory: {}", e);
        ReportedError
    })?;
    let dcx = Rc::new(DiagCtx::new(cwd));
    let arenas = CompilerArenas::new();

    let file_path = arguments.path.canonicalize().map_err(|e| {
        eprintln!(
            "error: failed to canonicalize file path '{}': {}",
            arguments.path.display(),
            e
        );
        ReportedError
    })?;

    let file_stem = file_path
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| {
            eprintln!(
                "error: failed to extract filename from '{}'",
                file_path.display()
            );
            ReportedError
        })?;

    let target_root = script_target_dir(&file_path, profile_dir);
    std::fs::create_dir_all(&target_root).map_err(|e| {
        eprintln!(
            "error: failed to create target directory '{}': {}",
            target_root.display(),
            e
        );
        ReportedError
    })?;

    let store = CompilerStore::new(
        &arenas,
        target_root.join("objects"),
        &dcx,
        arguments.target.clone(),
        compile_options.profile,
    )?;
    store.configure_linker(arguments.linker.clone(), arguments.sysroot.clone());
    let icx = CompilerContext::new(dcx, store);
    let mut package_fingerprints = FxHashMap::default();
    let incremental_enabled = !arguments.no_incremental;

    compile_std(
        &icx,
        arguments.std_path.clone(),
        compile_options,
        arguments.build_std,
        &mut package_fingerprints,
    )?;
    build_runtime(&icx, &target_root, arguments.runtime_path.clone())?;

    let package_index = PackageIndex::new(1);
    let mut dependencies = FxHashMap::default();
    dependencies.insert("std".into(), "std".into());

    let config = icx.store.arenas.configs.alloc(Config {
        name: file_stem.into(),
        identifier: format!("script-{}", file_stem).into(),
        src: file_path.clone(),
        dependencies,
        index: package_index,
        kind: PackageKind::Executable,
        executable_out: arguments.output.clone(),
        no_std_prelude: false,
        is_script: true,
        profile: compile_options.profile,
        codegen: compile_options.codegen,
        overflow_checks: compile_options.overflow_checks,
        debug: DebugOptions {
            dump_mir: arguments.dump_mir,
            dump_llvm: arguments.dump_llvm,
            timings: arguments.timings,
            debug_info: compile_options.debug_info,
        },
        test_mode: true,
        std_mode: StdMode::FullStd,
        is_std_provider: false,
    });

    let mut compiler = Compiler::new(&icx, config);
    let fingerprint_input = incremental::compute_package_fingerprint_input_with_test_selection(
        &icx,
        config,
        &package_fingerprints,
        Some(selection),
    )
    .map_err(|e| {
        icx.dcx.emit_error(
            format!(
                "failed to compute test fingerprint for script '{}': {}",
                file_stem, e
            ),
            None,
        );
        ReportedError
    })?;

    let reused = if incremental_enabled {
        match metadata::try_load_package_metadata(
            compiler.context,
            &fingerprint_input,
            ReuseMode::CodegenRoot,
        ) {
            MetadataLoadStatus::Hit(hit) => match metadata::hydrate_loaded_metadata(
                compiler.context,
                &hit,
                ReuseMode::CodegenRoot,
            ) {
                Ok(()) => {
                    eprintln!("Reusing tests (metadata+object) – {}", file_stem);
                    true
                }
                Err(e) => {
                    eprintln!(
                        "Compiling tests – {} (metadata hydrate miss: {})",
                        file_stem, e
                    );
                    false
                }
            },
            MetadataLoadStatus::Miss(reason) => {
                if compiler.context.config.debug.timings {
                    eprintln!(
                        "Compiling tests – {} (metadata miss: {})",
                        file_stem, reason
                    );
                } else {
                    eprintln!("Compiling tests – {}", file_stem);
                }
                false
            }
        }
    } else {
        eprintln!("Compiling tests – {}", file_stem);
        false
    };

    if reused {
        codegen::link::link_executable(compiler.context)
    } else {
        let exe = compiler.test(selection)?;
        if let Err(e) = metadata::write_package_metadata(
            compiler.context,
            &fingerprint_input,
            ReuseMode::CodegenRoot,
        ) {
            eprintln!(
                "warning: failed to write test metadata for '{}': {}",
                file_stem, e
            );
        }
        Ok(exe)
    }
}

fn run_package_test(
    arguments: CommonCompileArgs,
    selection: &TestSelection,
) -> Result<Option<std::path::PathBuf>, ReportedError> {
    let compile_options = arguments.compile_mode_options();
    let profile_dir = profile_dir_name(compile_options.profile);
    let cwd = std::env::current_dir().map_err(|e| {
        eprintln!("error: failed to get current directory: {}", e);
        ReportedError
    })?;
    let dcx = Rc::new(DiagCtx::new(cwd));
    let arenas = CompilerArenas::new();
    let project_root = arguments.path.canonicalize().map_err(|e| {
        eprintln!(
            "error: failed to canonicalize project root path '{}': {}",
            arguments.path.display(),
            e
        );
        ReportedError
    })?;
    let target_root = project_root
        .join("target")
        .join(profile_dir)
        .join("objects");
    let store = CompilerStore::new(
        &arenas,
        target_root,
        &dcx,
        arguments.target.clone(),
        compile_options.profile,
    )?;
    store.configure_linker(arguments.linker.clone(), arguments.sysroot.clone());
    let icx = CompilerContext::new(dcx, store);
    let mut package_fingerprints = FxHashMap::default();
    let incremental_enabled = !arguments.no_incremental;
    let sync_options = arguments.sync_options();

    let graph = sync_dependencies(arguments.path.clone(), sync_options)?;

    let root_is_std = is_root_std_package(&graph, arguments.std_path.clone(), &icx)?;

    if !root_is_std {
        let _ = compile_std(
            &icx,
            arguments.std_path.clone(),
            compile_options,
            arguments.build_std,
            &mut package_fingerprints,
        )?;
    }
    build_runtime(&icx, &project_root, arguments.runtime_path.clone())?;

    let total = graph.ordered.len();

    for (index, package) in graph.ordered.iter().enumerate() {
        let is_root = index + 1 == total;

        // Non-root packages are compiled normally (as libraries)
        if !is_root {
            if !matches!(package.kind, PackageKind::Library | PackageKind::Both) {
                icx.dcx.emit_error(
                    format!(
                        "dependency `{}` must be a library (found {:?})",
                        package.package.0, package.kind
                    ),
                    None,
                );
                return Err(ReportedError);
            }
        }

        let package_index = PackageIndex::new(index + 1);
        let name = get_package_name(&package.package.0).map_err(|e| {
            icx.dcx.emit_error(
                format!(
                    "failed to get package name for '{}': {}",
                    package.package.0, e
                ),
                None,
            );
            ReportedError
        })?;
        let is_std_package = root_is_std && is_root;
        let identifier = if is_std_package {
            STD_PREFIX.into()
        } else {
            package.unique_identifier().map_err(|e| {
                icx.dcx.emit_error(
                    format!(
                        "failed to generate unique identifier for '{}': {}",
                        package.package.0, e
                    ),
                    None,
                );
                ReportedError
            })?
        };
        let mut dependencies = graph.dependencies_for(package).map_err(|e| {
            icx.dcx.emit_error(
                format!(
                    "failed to resolve dependencies for '{}': {}",
                    package.package.0, e
                ),
                None,
            );
            ReportedError
        })?;
        if !is_std_package {
            dependencies.insert("std".into(), "std".into());
        }

        let src = package
            .path()
            .and_then(|p| {
                p.canonicalize()
                    .map_err(|e| format!("failed to resolve path – {}", e))
            })
            .map_err(|e| format!("failed to resolve path – {}", e))
            .map_err(|e| {
                icx.dcx.emit_error(
                    format!(
                        "failed to resolve source path for '{}': {}",
                        package.package.0, e
                    ),
                    None,
                );
                ReportedError
            })?;

        // Root package gets test mode; dependencies are compiled normally
        let test_mode = is_root;
        let kind = if is_root {
            PackageKind::Executable
        } else {
            package.kind
        };

        let config = icx.store.arenas.configs.alloc(Config {
            name,
            identifier,
            src,
            dependencies,
            index: package_index,
            kind,
            executable_out: arguments.output.clone(),
            no_std_prelude: package.no_std_prelude,
            is_script: false,
            profile: compile_options.profile,
            codegen: compile_options.codegen,
            // std intentionally relies on wrapping arithmetic (e.g. SipHash)
            // and always compiles without overflow checks, like attached std.
            overflow_checks: compile_options.overflow_checks && !is_std_package,
            debug: DebugOptions {
                dump_mir: arguments.dump_mir,
                dump_llvm: arguments.dump_llvm,
                timings: arguments.timings,
                debug_info: compile_options.debug_info,
            },
            test_mode,
            std_mode: if is_std_package {
                StdMode::BootstrapStd
            } else {
                StdMode::FullStd
            },
            is_std_provider: is_std_package,
        });

        let fingerprint_input = if is_root {
            incremental::compute_package_fingerprint_input_with_test_selection(
                &icx,
                config,
                &package_fingerprints,
                Some(selection),
            )
        } else {
            incremental::compute_package_fingerprint_input(&icx, config, &package_fingerprints)
        }
        .map_err(|e| {
            icx.dcx.emit_error(
                format!(
                    "failed to compute fingerprint for package '{}': {}",
                    package.package.0, e
                ),
                None,
            );
            ReportedError
        })?;

        let mut compiler = Compiler::new(&icx, config);
        let reuse_mode = if is_root {
            ReuseMode::CodegenRoot
        } else {
            ReuseMode::CodegenDependency
        };
        let reused = if incremental_enabled {
            match metadata::try_load_package_metadata(
                compiler.context,
                &fingerprint_input,
                reuse_mode,
            ) {
                MetadataLoadStatus::Hit(hit) => {
                    match metadata::hydrate_loaded_metadata(compiler.context, &hit, reuse_mode) {
                        Ok(()) => {
                            if is_root {
                                eprintln!(
                                    "Reusing tests (metadata+object) – {}",
                                    package.package.0
                                );
                            } else if compiler.context.config.debug.timings {
                                eprintln!("Reusing (metadata+object) – {}", package.package.0);
                            }
                            true
                        }
                        Err(e) => {
                            if is_root {
                                eprintln!(
                                    "Compiling tests – {} (metadata hydrate miss: {})",
                                    package.package.0, e
                                );
                            } else {
                                eprintln!(
                                    "Compiling – {} (metadata hydrate miss: {})",
                                    package.package.0, e
                                );
                            }
                            false
                        }
                    }
                }
                MetadataLoadStatus::Miss(reason) => {
                    if is_root {
                        if compiler.context.config.debug.timings {
                            eprintln!(
                                "Compiling tests – {} (metadata miss: {})",
                                package.package.0, reason
                            );
                        } else {
                            eprintln!("Compiling tests – {}", package.package.0);
                        }
                    } else if compiler.context.config.debug.timings {
                        eprintln!(
                            "Compiling – {} (metadata miss: {})",
                            package.package.0, reason
                        );
                    } else {
                        eprintln!("Compiling – {}", package.package.0);
                    }
                    false
                }
            }
        } else {
            if is_root {
                eprintln!("Compiling tests – {}", package.package.0);
            } else {
                eprintln!("Compiling – {}", package.package.0);
            }
            false
        };

        let exe_path = if reused {
            if is_root {
                codegen::link::link_executable(compiler.context)?
            } else {
                None
            }
        } else {
            let exe_path = if is_root {
                compiler.test(selection)?
            } else {
                compiler.build()?
            };
            if let Err(e) =
                metadata::write_package_metadata(compiler.context, &fingerprint_input, reuse_mode)
            {
                eprintln!(
                    "warning: failed to write metadata for '{}': {}",
                    package.package.0, e
                );
            }
            exe_path
        };

        package_fingerprints.insert(
            config.identifier.to_string(),
            fingerprint_input.package_fingerprint,
        );

        if exe_path.is_some() {
            return Ok(exe_path);
        }
    }
    Ok(None)
}

#[cfg(test)]
mod target_runtime_tests {
    use super::{
        default_package_bitcode_output, default_script_bitcode_output, installed_runtime_path,
        publish_bitcode, validate_build_modes,
    };
    use crate::{BuildEmit, Lto};
    use compiler::{codegen::artifact::ModuleArtifact, compile::config::ModuleArtifactKind};
    use std::{fs, path::Path};

    #[test]
    fn host_runtime_uses_legacy_toolchain_location() {
        assert_eq!(
            installed_runtime_path(Path::new("/toolchain"), None),
            Path::new("/toolchain/lib/taro/runtime/libtaro_runtime.a")
        );
    }

    #[test]
    fn requested_target_runtime_is_triple_scoped() {
        assert_eq!(
            installed_runtime_path(Path::new("/toolchain"), Some("aarch64-unknown-linux-gnu")),
            Path::new("/toolchain/lib/taro/runtime/aarch64-unknown-linux-gnu/libtaro_runtime.a")
        );
    }

    #[test]
    fn bitcode_defaults_are_user_facing_and_profile_scoped() {
        assert_eq!(
            default_script_bitcode_output(Path::new("/workspace"), "hello"),
            Path::new("/workspace/hello.bc")
        );
        assert_eq!(
            default_package_bitcode_output(Path::new("/workspace/target/release"), "app"),
            Path::new("/workspace/target/release/app.bc")
        );
    }

    #[test]
    fn full_lto_rejects_package_scoped_bitcode_output() {
        assert!(validate_build_modes(BuildEmit::Link, Lto::Full).is_ok());
        let error = validate_build_modes(BuildEmit::LlvmBitcode, Lto::Full).unwrap_err();
        assert!(error.contains("package-scoped"));
    }

    #[test]
    fn publishing_bitcode_copies_the_internal_artifact() {
        let root = std::env::temp_dir().join(format!(
            "taro-publish-bitcode-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        let source = root.join("objects/app.bc");
        let output = root.join("published/app.bc");
        fs::create_dir_all(source.parent().expect("source parent")).expect("source directory");
        fs::write(&source, b"BC\xc0\xde").expect("source bitcode");

        let published = publish_bitcode(
            &ModuleArtifact::new(ModuleArtifactKind::LlvmBitcode, source),
            output.clone(),
        )
        .unwrap_or_else(|_| panic!("bitcode should publish"));

        assert_eq!(published, output);
        assert_eq!(
            fs::read(published).expect("published bitcode"),
            b"BC\xc0\xde"
        );
        let _ = fs::remove_dir_all(root);
    }
}
