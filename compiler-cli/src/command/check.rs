use super::{incremental, std_attached};
use crate::{
    CommandLineArguments, CompileModeOptions,
    package::{
        manifest::ValidatedDependencyGraph, sync::sync_dependencies, utils::get_package_name,
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
    metadata::{self, MetadataLoadStatus, ReuseMode},
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
        compile_options.profile,
    )?;
    let icx = CompilerContext::new(dcx, store);
    let mut package_fingerprints = FxHashMap::default();

    // Compile std (index 0)
    compile_std(
        &icx,
        arguments.std_path.clone(),
        compile_options,
        arguments.build_std,
        &mut package_fingerprints,
    )?;

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
    let icx = CompilerContext::new(dcx, store);
    let mut package_fingerprints = FxHashMap::default();
    let incremental_enabled = !arguments.no_incremental;
    let sync_options = arguments.sync_options();

    let graph = sync_dependencies(arguments.path.clone(), sync_options)?;

    let root_is_std = is_root_std_package(&graph, arguments.std_path.clone(), &icx)?;

    if !root_is_std {
        compile_std(
            &icx,
            arguments.std_path.clone(),
            compile_options,
            arguments.build_std,
            &mut package_fingerprints,
        )?;
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
        let reused = if incremental_enabled && !is_root {
            match metadata::try_load_package_metadata(
                compiler.context,
                &fingerprint_input,
                ReuseMode::SemanticDependency,
            ) {
                MetadataLoadStatus::Hit(hit) => {
                    match metadata::hydrate_loaded_metadata(
                        compiler.context,
                        &hit,
                        ReuseMode::SemanticDependency,
                    ) {
                        Ok(()) => {
                            if compiler.context.config.debug.timings {
                                eprintln!("Reusing (metadata) – {}", package.package.0);
                            }
                            true
                        }
                        Err(e) => {
                            eprintln!(
                                "Checking – {} (metadata hydrate miss: {})",
                                package.package.0, e
                            );
                            false
                        }
                    }
                }
                MetadataLoadStatus::Miss(reason) => {
                    if compiler.context.config.debug.timings {
                        eprintln!(
                            "Checking – {} (metadata miss: {})",
                            package.package.0, reason
                        );
                    } else {
                        eprintln!("Checking – {}", package.package.0);
                    }
                    false
                }
            }
        } else {
            eprintln!("Checking – {}", package.package.0);
            false
        };

        if !reused {
            let _ = compiler.check()?;
            if !is_root {
                if let Err(e) = metadata::write_package_metadata(
                    compiler.context,
                    &fingerprint_input,
                    ReuseMode::SemanticDependency,
                ) {
                    eprintln!(
                        "warning: failed to write metadata for '{}': {}",
                        package.package.0, e
                    );
                }
            }
        }

        package_fingerprints.insert(
            config.identifier.to_string(),
            fingerprint_input.package_fingerprint,
        );
    }

    Ok(())
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
        ReuseMode::SemanticDependency,
    )
}

fn is_root_std_package(
    graph: &ValidatedDependencyGraph,
    std_path: Option<PathBuf>,
    ctx: &CompilerContext<'_>,
) -> Result<bool, ReportedError> {
    std_attached::is_root_std_package(graph, std_path, ctx)
}

fn profile_dir_name(profile: BuildProfile) -> &'static str {
    match profile {
        BuildProfile::Debug => "debug",
        BuildProfile::Release => "release",
    }
}
