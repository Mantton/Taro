use crate::{
    CompileModeOptions,
    package::{manifest::ValidatedDependencyGraph, utils::language_home},
};
use compiler::{
    PackageIndex,
    compile::{
        Compiler,
        config::{BuildProfile, Config, DebugOptions, PackageKind, StdMode},
        context::CompilerContext,
    },
    constants::STD_PREFIX,
    error::ReportedError,
    metadata::{self, MetadataLoadStatus, ReuseMode},
};
use rustc_hash::FxHashMap;
use std::{
    fs,
    io::{BufReader, Read},
    path::{Path, PathBuf},
};

pub fn compile_std<'a>(
    ctx: &'a CompilerContext<'a>,
    std_path: Option<PathBuf>,
    compile_options: CompileModeOptions,
    build_std: bool,
    package_fingerprints: &mut FxHashMap<String, String>,
    reuse_mode: ReuseMode,
) -> Result<(), ReportedError> {
    let src = resolve_std_path(std_path).map_err(|e| {
        let message = format!("failed to resolve standard library location – {}", e);
        ctx.dcx.emit_error(message, None);
        ReportedError
    })?;
    let attached = attached_std_artifacts(ctx).map_err(|e| {
        ctx.dcx.emit_error(
            format!("failed to resolve attached std artifact path – {}", e),
            None,
        );
        ReportedError
    })?;

    let index = PackageIndex::new(0);
    // Attached std artifacts are toolchain-level and shared across debug/release user builds.
    // Keep std canonical (release-like) so --build-std is deterministic per target.
    let std_profile = BuildProfile::Release;
    let std_overflow_checks = false;

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
        profile: std_profile,
        overflow_checks: std_overflow_checks,
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

    if build_std {
        let fingerprint_input = super::incremental::compute_package_fingerprint_input(
            ctx,
            config,
            package_fingerprints,
        )
        .map_err(|e| {
            ctx.dcx.emit_error(
                format!("failed to compute fingerprint for package 'std': {}", e),
                None,
            );
            ReportedError
        })?;

        // Build std in codegen mode so one attached artifact set serves build/check/run/test.
        let _ = compiler.build()?;
        metadata::write_package_metadata(
            compiler.context,
            &fingerprint_input,
            ReuseMode::CodegenDependency,
        )
        .map_err(|e| {
            ctx.dcx.emit_error(
                format!("failed to write metadata for built std artifacts: {}", e),
                None,
            );
            ReportedError
        })?;

        let local_metadata =
            metadata::metadata_path_for_config(config, compiler.context.output_root().as_path());
        let local_object = compiler.context.output_root().join("std.o");
        publish_attached_std_artifacts(&local_metadata, &local_object, &attached).map_err(|e| {
            ctx.dcx.emit_error(
                format!("failed to publish attached std artifacts: {}", e),
                None,
            );
            ReportedError
        })?;

        if matches!(reuse_mode, ReuseMode::CodegenDependency) {
            // Ensure downstream codegen links against the attached std object path.
            compiler.context.cache_object_file(attached.object.clone());
        }
    } else {
        let attached_object_for_load = match reuse_mode {
            ReuseMode::CodegenDependency => Some(attached.object.as_path()),
            ReuseMode::SemanticDependency => attached
                .object
                .exists()
                .then_some(attached.object.as_path()),
        };
        match metadata::try_load_package_metadata_from_paths(
            compiler.context,
            reuse_mode,
            &attached.metadata,
            attached_object_for_load,
        ) {
            MetadataLoadStatus::Hit(hit) => {
                metadata::hydrate_loaded_metadata(compiler.context, &hit, reuse_mode).map_err(
                    |e| {
                        ctx.dcx.emit_error(
                            format!(
                                "failed to hydrate attached std metadata: {}\nrun with --build-std to rebuild attached std artifacts",
                                e
                            ),
                            None,
                        );
                        ReportedError
                    },
                )?;
                if compiler.context.config.debug.timings {
                    eprintln!("Reusing attached std artifacts");
                }
            }
            MetadataLoadStatus::Miss(reason) => {
                let expected_files = match reuse_mode {
                    ReuseMode::CodegenDependency => {
                        format!(
                            "  {}\n  {}",
                            attached.metadata.display(),
                            attached.object.display()
                        )
                    }
                    ReuseMode::SemanticDependency => {
                        format!("  {}", attached.metadata.display())
                    }
                };
                ctx.dcx.emit_error(
                    format!(
                        "attached std artifacts are unavailable or invalid: {}\nexpected files:\n{}\nrun with --build-std to rebuild attached std artifacts",
                        reason,
                        expected_files
                    ),
                    None,
                );
                return Err(ReportedError);
            }
        }
    }

    let std_fingerprint =
        fingerprint_attached_std_artifacts(&attached, reuse_mode).map_err(|e| {
            ctx.dcx.emit_error(
                format!("failed to fingerprint attached std artifacts: {}", e),
                None,
            );
            ReportedError
        })?;
    package_fingerprints.insert(config.identifier.to_string(), std_fingerprint);

    Ok(())
}

pub fn is_root_std_package(
    graph: &ValidatedDependencyGraph,
    std_path: Option<PathBuf>,
    ctx: &CompilerContext<'_>,
) -> Result<bool, ReportedError> {
    let std_root = resolve_std_path(std_path).map_err(|e| {
        ctx.dcx.emit_error(
            format!("failed to resolve standard library location – {}", e),
            None,
        );
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

#[derive(Debug, Clone)]
struct AttachedStdArtifacts {
    dir: PathBuf,
    metadata: PathBuf,
    object: PathBuf,
}

fn attached_std_artifacts(ctx: &CompilerContext<'_>) -> Result<AttachedStdArtifacts, String> {
    let home = language_home()?;
    let target = ctx
        .store
        .target_layout
        .triple()
        .as_str()
        .to_string_lossy()
        .into_owned();
    let dir = home
        .join("lib")
        .join("taro")
        .join("std")
        .join(target.as_str());
    Ok(AttachedStdArtifacts {
        metadata: dir.join("std.taro_meta"),
        object: dir.join("std.o"),
        dir,
    })
}

fn publish_attached_std_artifacts(
    metadata: &Path,
    object: &Path,
    attached: &AttachedStdArtifacts,
) -> Result<(), String> {
    if !metadata.exists() {
        return Err(format!(
            "local std metadata missing at '{}'",
            metadata.display()
        ));
    }
    if !object.exists() {
        return Err(format!(
            "local std object missing at '{}'",
            object.display()
        ));
    }

    fs::create_dir_all(&attached.dir).map_err(|e| {
        format!(
            "failed to create std artifact directory '{}': {}",
            attached.dir.display(),
            e
        )
    })?;
    atomic_copy_file(metadata, &attached.metadata).map_err(|e| {
        format!(
            "failed to publish metadata '{}' -> '{}': {}",
            metadata.display(),
            attached.metadata.display(),
            e
        )
    })?;
    atomic_copy_file(object, &attached.object).map_err(|e| {
        format!(
            "failed to publish object '{}' -> '{}': {}",
            object.display(),
            attached.object.display(),
            e
        )
    })?;
    Ok(())
}

fn fingerprint_attached_std_artifacts(
    attached: &AttachedStdArtifacts,
    reuse_mode: ReuseMode,
) -> Result<String, String> {
    if !attached.metadata.exists() {
        return Err(format!(
            "metadata file missing at '{}'",
            attached.metadata.display()
        ));
    }
    if matches!(reuse_mode, ReuseMode::CodegenDependency) && !attached.object.exists() {
        return Err(format!(
            "object file missing at '{}'",
            attached.object.display()
        ));
    }

    let mut hasher = blake3::Hasher::new();
    hasher.update(b"taro.attached.std.v2");
    match reuse_mode {
        ReuseMode::CodegenDependency => {
            hasher.update(b"mode:codegen");
        }
        ReuseMode::SemanticDependency => {
            hasher.update(b"mode:semantic");
        }
    }
    hash_file_into_hasher(&attached.metadata, &mut hasher)?;
    if attached.object.exists() {
        hash_file_into_hasher(&attached.object, &mut hasher)?;
    } else {
        hasher.update(b"object:missing");
    }
    Ok(hasher.finalize().to_hex().to_string())
}

fn hash_file_into_hasher(path: &Path, hasher: &mut blake3::Hasher) -> Result<(), String> {
    let file = fs::File::open(path)
        .map_err(|e| format!("failed to open file '{}': {}", path.display(), e))?;
    let byte_len = file
        .metadata()
        .map_err(|e| format!("failed to stat file '{}': {}", path.display(), e))?
        .len();
    hasher.update(&byte_len.to_le_bytes());

    let mut reader = BufReader::new(file);
    let mut buf = [0_u8; 64 * 1024];
    loop {
        let read = reader
            .read(&mut buf)
            .map_err(|e| format!("failed to read file '{}': {}", path.display(), e))?;
        if read == 0 {
            break;
        }
        hasher.update(&buf[..read]);
    }

    Ok(())
}

fn atomic_copy_file(src: &Path, dst: &Path) -> Result<(), String> {
    let parent = dst
        .parent()
        .ok_or_else(|| format!("destination '{}' has no parent directory", dst.display()))?;

    let dst_name = dst
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("artifact");
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let tmp = parent.join(format!(
        ".{}.tmp-{}-{}",
        dst_name,
        std::process::id(),
        nonce
    ));

    fs::copy(src, &tmp).map_err(|e| {
        format!(
            "failed to copy '{}' to temporary file '{}': {}",
            src.display(),
            tmp.display(),
            e
        )
    })?;

    if let Err(e) = fs::rename(&tmp, dst) {
        let _ = fs::remove_file(&tmp);
        return Err(format!(
            "failed to atomically rename '{}' -> '{}': {}",
            tmp.display(),
            dst.display(),
            e
        ));
    }

    Ok(())
}
