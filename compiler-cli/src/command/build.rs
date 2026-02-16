use crate::{
    CommandLineArguments, CompileModeOptions,
    package::{
        sync::sync_dependencies,
        utils::{get_package_name, language_home},
    },
};
use compiler::{
    PackageIndex,
    compile::{
        Compiler,
        config::{BuildProfile, Config, DebugOptions, PackageKind},
        context::{CompilerArenas, CompilerContext, CompilerStore},
    },
    constants::STD_PREFIX,
    diagnostics::DiagCtx,
    error::ReportedError,
};
use rustc_hash::FxHashMap;
use std::{
    hash::{Hash, Hasher},
    path::PathBuf,
    process::Command,
    rc::Rc,
};

pub fn run(
    arguments: CommandLineArguments,
    require_executable: bool,
) -> Result<Option<std::path::PathBuf>, ReportedError> {
    if arguments.is_single_file() {
        run_single_file(arguments)
    } else {
        run_package(arguments, require_executable)
    }
}

fn run_single_file(
    arguments: CommandLineArguments,
) -> Result<Option<std::path::PathBuf>, ReportedError> {
    let compile_options = arguments.compile_mode_options();
    let profile_dir = profile_dir_name(compile_options.profile);
    let cwd = std::env::current_dir().map_err(|e| {
        eprintln!("error: failed to get current directory: {}", e);
        ReportedError
    })?;
    let dcx = Rc::new(DiagCtx::new(cwd));
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
    )?;
    let icx = CompilerContext::new(dcx, store);

    // Compile std (index 0)
    compile_std(&icx, arguments.std_path.clone(), compile_options)?;
    build_runtime(&icx, &target_root, arguments.runtime_path.clone())?;

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
        executable_out: arguments.output.clone(),
        no_std_prelude: false,
        is_script: true,
        profile: compile_options.profile,
        overflow_checks: compile_options.overflow_checks,
        debug: DebugOptions {
            dump_mir: arguments.dump_mir,
            dump_llvm: arguments.dump_llvm,
        },
    });

    eprintln!("Compiling – {}", file_stem);
    let mut compiler = Compiler::new(&icx, config);
    compiler.build()
}

fn script_target_dir(file_path: &PathBuf, profile_dir: &str) -> PathBuf {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    file_path.hash(&mut hasher);
    let hash = format!("{:x}", hasher.finish());

    std::env::temp_dir()
        .join("taro-scripts")
        .join(hash)
        .join(profile_dir)
}

fn run_package(
    arguments: CommandLineArguments,
    require_executable: bool,
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
    let target_root = project_root.join("target").join(profile_dir).join("objects");
    let store = CompilerStore::new(&arenas, target_root, &dcx, arguments.target.clone())?;
    let icx = CompilerContext::new(dcx, store);

    let graph = sync_dependencies(arguments.path)?;

    let _ = compile_std(&icx, arguments.std_path.clone(), compile_options)?;
    build_runtime(&icx, &project_root, arguments.runtime_path.clone())?;

    let total = graph.ordered.len();

    for (index, package) in graph.ordered.iter().enumerate() {
        let is_root = index + 1 == total;
        if !is_root && package.kind != PackageKind::Library {
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
        eprintln!("Compiling – {}", package.package.0);
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
        let identifier = package.unique_identifier().map_err(|e| {
            icx.dcx.emit_error(
                format!(
                    "failed to generate unique identifier for '{}': {}",
                    package.package.0, e
                ),
                None,
            );
            ReportedError
        })?;
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
        dependencies.insert("std".into(), "std".into());

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
            executable_out: arguments.output.clone(),
            no_std_prelude: package.no_std_prelude,
            is_script: false,
            profile: compile_options.profile,
            overflow_checks: compile_options.overflow_checks,
            debug: DebugOptions {
                dump_mir: arguments.dump_mir,
                dump_llvm: arguments.dump_llvm,
            },
        });

        let mut compiler = Compiler::new(&icx, config);
        let exe_path = compiler.build()?;
        if exe_path.is_some() {
            return Ok(exe_path);
        }
    }
    Ok(None)
}

/// Locates and links the Taro runtime library.
///
/// This function attempts to find `libtaro_runtime.a` using the following priority:
/// 1. `--runtime-path` CLI argument.
/// 2. `TARO_RUNTIME_LIB` environment variable.
/// 3. `TARO_HOME/lib` directory.
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
            ctx.store.add_link_input(path);
            return Ok(());
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
            ctx.store.add_link_input(path);
            return Ok(());
        }
    }

    // 3. TARO_HOME
    if let Ok(home) = language_home() {
        let path = home.join("lib").join("libtaro_runtime.a");
        if path.exists() {
            ctx.store.add_link_input(path);
            return Ok(());
        }
    }

    // 4. Relative to Executable (Dist)
    if let Ok(exe) = std::env::current_exe() {
        if let Some(bin_dir) = exe.parent() {
            if let Some(root) = bin_dir.parent() {
                // <root>/lib/taro/runtime/libtaro_runtime.a
                let path = root
                    .join("lib")
                    .join("taro")
                    .join("runtime")
                    .join("libtaro_runtime.a");
                if path.exists() {
                    ctx.store.add_link_input(path);
                    return Ok(());
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

    let status = Command::new("cargo")
        .arg("build")
        .arg("--release")
        .arg("--quiet")
        .arg("-p")
        .arg("taro-runtime")
        .arg("--manifest-path")
        .arg(workspace_root.join("Cargo.toml"))
        .arg("--target-dir")
        .arg(&target_dir)
        .status()
        .map_err(|e| {
            ctx.dcx.emit_error(
                format!("failed to invoke cargo to build runtime: {e}"),
                None,
            );
            ReportedError
        })?;

    if !status.success() {
        ctx.dcx
            .emit_error("failed to build runtime crate".into(), None);
        return Err(ReportedError);
    }

    let lib_path = target_dir.join("release").join("libtaro_runtime.a");
    if !lib_path.exists() {
        ctx.dcx.emit_error(
            format!("runtime archive not found at {}", lib_path.display()),
            None,
        );
        return Err(ReportedError);
    }

    // Make the runtime archive available to the existing link step by treating it like another
    // "object file" input.
    ctx.store.add_link_input(lib_path);
    Ok(())
}

fn profile_dir_name(profile: BuildProfile) -> &'static str {
    match profile {
        BuildProfile::Debug => "debug",
        BuildProfile::Release => "release",
    }
}

fn compile_std<'a>(
    ctx: &'a CompilerContext<'a>,
    std_path: Option<PathBuf>,
    compile_options: CompileModeOptions,
) -> Result<(), ReportedError> {
    eprintln!("Compiling – std");

    let src = resolve_std_path(std_path).map_err(|e| {
        let message = format!("failed to resolve standard library location – {}", e);
        ctx.dcx.emit_error(message, None);
        ReportedError
    })?;

    let index = PackageIndex::new(0);

    let config = ctx.store.arenas.configs.alloc(Config {
        index,
        name: "std".into(),
        identifier: "std".into(),
        src,
        dependencies: Default::default(),
        kind: PackageKind::Library,
        executable_out: None,
        no_std_prelude: true,
        is_script: false,
        profile: compile_options.profile,
        overflow_checks: compile_options.overflow_checks,
        debug: DebugOptions::default(),
    });
    let mut compiler = Compiler::new(ctx, config);
    let _ = compiler.build()?;
    Ok(())
}

fn resolve_std_path(std_path: Option<PathBuf>) -> Result<PathBuf, String> {
    if let Some(path) = std_path {
        return path
            .canonicalize()
            .map_err(|e| format!("--std-path {} is invalid: {}", path.display(), e));
    }

    let std_root = language_home()?.join(STD_PREFIX);
    std_root
        .canonicalize()
        .map_err(|e| format!("{} is invalid: {}", std_root.display(), e))
}
