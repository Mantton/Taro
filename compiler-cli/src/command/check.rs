use crate::{
    CommandLineArguments, CompileModeOptions,
    package::{
        manifest::ValidatedDependencyGraph,
        sync::sync_dependencies,
        utils::{get_package_name, language_home},
    },
};
use compiler::{
    PackageIndex,
    compile::{
        Compiler,
        config::{BuildProfile, Config, DebugOptions, PackageKind, StdMode},
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
    rc::Rc,
};

pub fn run(arguments: CommandLineArguments) -> Result<(), ReportedError> {
    if arguments.is_single_file() {
        run_single_file(arguments)
    } else {
        run_package(arguments)
    }
}

fn run_single_file(arguments: CommandLineArguments) -> Result<(), ReportedError> {
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
            dump_mir: false,
            dump_llvm: false,
            timings: arguments.timings,
        },
        test_mode: false,
        std_mode: StdMode::FullStd,
        is_std_provider: false,
    });

    eprintln!("Checking – {}", file_stem);
    let mut compiler = Compiler::new(&icx, config);
    let _ = compiler.check()?;
    Ok(())
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

fn run_package(arguments: CommandLineArguments) -> Result<(), ReportedError> {
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

    let root_is_std = is_root_std_package(&graph, arguments.std_path.clone(), &icx)?;

    if !root_is_std {
        compile_std(&icx, arguments.std_path.clone(), compile_options)?;
    }

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

        let package_index = PackageIndex::new(index + 1);
        println!("Checking – {}", package.package.0);
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
                dump_mir: false,
                dump_llvm: false,
                timings: arguments.timings,
            },
            test_mode: false,
            std_mode: if is_std_package {
                StdMode::BootstrapStd
            } else {
                StdMode::FullStd
            },
            is_std_provider: is_std_package,
        });

        let mut compiler = Compiler::new(&icx, config);
        let _ = compiler.check()?;
    }

    Ok(())
}

fn compile_std<'a>(
    ctx: &'a CompilerContext<'a>,
    std_path: Option<PathBuf>,
    compile_options: CompileModeOptions,
) -> Result<(), ReportedError> {
    println!("Checking – std");

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
        debug: DebugOptions {
            dump_mir: false,
            dump_llvm: false,
            timings: compile_options.timings,
        },
        test_mode: false,
        std_mode: StdMode::BootstrapStd,
        is_std_provider: true,
    });

    let mut compiler = Compiler::new(ctx, config);
    let _ = compiler.check()?;
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

fn is_root_std_package(
    graph: &ValidatedDependencyGraph,
    std_path: Option<PathBuf>,
    ctx: &CompilerContext<'_>,
) -> Result<bool, ReportedError> {
    let std_root = resolve_std_path(std_path).map_err(|e| {
        ctx.dcx
            .emit_error(format!("failed to resolve standard library location – {}", e), None);
        ReportedError
    })?;

    let Some(root_pkg) = graph.ordered.last() else {
        return Ok(false);
    };

    let root_src = root_pkg.path().map_err(|e| {
        ctx.dcx.emit_error(
            format!(
                "failed to resolve source path for '{}': {}",
                root_pkg.package.0, e
            ),
            None,
        );
        ReportedError
    })?;
    let root_src = root_src.canonicalize().map_err(|e| {
        ctx.dcx.emit_error(
            format!(
                "failed to canonicalize source path for '{}': {}",
                root_pkg.package.0, e
            ),
            None,
        );
        ReportedError
    })?;

    Ok(root_src == std_root)
}

fn profile_dir_name(profile: BuildProfile) -> &'static str {
    match profile {
        BuildProfile::Debug => "debug",
        BuildProfile::Release => "release",
    }
}
