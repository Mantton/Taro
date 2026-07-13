use compiler::{
    compile::{
        config::{
            BuildProfile, Config, DebugInfo, LtoMode, ModuleArtifactKind, OptLevel,
            OptimizationMode, PackageKind, StdMode,
        },
        context::CompilerContext,
        test_collector::TestSelection,
    },
    constants::SOURCE_DIRECTORY,
    metadata::{DependencyFingerprint, PackageFingerprintInput},
};
use rustc_hash::FxHashMap;
use std::path::{Path, PathBuf};

pub fn compute_package_fingerprint_input(
    ctx: &CompilerContext<'_>,
    config: &Config,
    known_fingerprints: &FxHashMap<String, String>,
) -> Result<PackageFingerprintInput, String> {
    compute_package_fingerprint_input_with_test_selection(ctx, config, known_fingerprints, None)
}

pub fn compute_package_fingerprint_input_with_test_selection(
    ctx: &CompilerContext<'_>,
    config: &Config,
    known_fingerprints: &FxHashMap<String, String>,
    test_selection: Option<&TestSelection>,
) -> Result<PackageFingerprintInput, String> {
    let mut dependency_ids: Vec<String> = config
        .dependencies
        .values()
        .map(|id| id.to_string())
        .collect();
    dependency_ids.sort();
    dependency_ids.dedup();

    let mut dependency_fingerprints = Vec::with_capacity(dependency_ids.len());
    for identifier in dependency_ids {
        let fingerprint = known_fingerprints.get(&identifier).ok_or_else(|| {
            format!(
                "missing fingerprint for dependency identifier `{}`",
                identifier
            )
        })?;

        dependency_fingerprints.push(DependencyFingerprint {
            identifier,
            fingerprint: fingerprint.clone(),
        });
    }

    let mut hasher = blake3::Hasher::new();
    hasher.update(b"taro.incremental.v1.package");

    hasher.update(config.identifier.as_bytes());
    hasher.update(&[0]);
    hasher.update(config.name.as_bytes());
    hasher.update(&[0]);
    hasher.update(&(config.index.raw() as u32).to_le_bytes());

    let target_triple = ctx
        .store
        .target_layout
        .triple()
        .as_str()
        .to_string_lossy()
        .into_owned();
    hasher.update(target_triple.as_bytes());
    hasher.update(&[0]);
    hasher.update(ctx.store.target_layout.cpu().as_bytes());
    hasher.update(&[0]);
    hasher.update(ctx.store.target_layout.features().as_bytes());
    hasher.update(&[0]);

    hasher.update(profile_name(config.profile).as_bytes());
    hash_optimization_mode(config.codegen.optimization, &mut hasher);
    hasher.update(&[module_artifact_kind_tag(config.codegen.artifact)]);
    hasher.update(&[lto_mode_tag(config.codegen.lto)]);
    hasher.update(&[
        config.overflow_checks as u8,
        config.no_std_prelude as u8,
        config.test_mode as u8,
        config.is_script as u8,
        config.is_std_provider as u8,
        config.debug.dump_mir as u8,
        config.debug.dump_llvm as u8,
        debug_info_tag(config.debug.debug_info),
    ]);
    hasher.update(&[package_kind_tag(config.kind), std_mode_tag(config.std_mode)]);

    hash_test_selection(config, test_selection, &mut hasher)?;

    // `executable_out` and linker/runtime inputs are intentionally absent: they do not change
    // the compiled module artifact, and linked root cache hits always relink
    // using the current invocation.

    let mut dependency_mapping: Vec<_> = config
        .dependencies
        .iter()
        .map(|(name, id)| (name.to_string(), id.to_string()))
        .collect();
    dependency_mapping.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));

    hasher.update(&(dependency_mapping.len() as u32).to_le_bytes());
    for (name, id) in dependency_mapping {
        hasher.update(name.as_bytes());
        hasher.update(&[0]);
        hasher.update(id.as_bytes());
        hasher.update(&[0]);
    }

    hasher.update(&(dependency_fingerprints.len() as u32).to_le_bytes());
    for dep in &dependency_fingerprints {
        hasher.update(dep.identifier.as_bytes());
        hasher.update(&[0]);
        hasher.update(dep.fingerprint.as_bytes());
        hasher.update(&[0]);
    }

    hash_source_inputs(config, &mut hasher)?;

    Ok(PackageFingerprintInput {
        package_fingerprint: hasher.finalize().to_hex().to_string(),
        dependencies: dependency_fingerprints,
    })
}

fn package_kind_tag(kind: PackageKind) -> u8 {
    match kind {
        PackageKind::Library => 0,
        PackageKind::Executable => 1,
        PackageKind::Both => 2,
    }
}

fn debug_info_tag(debug_info: DebugInfo) -> u8 {
    match debug_info {
        DebugInfo::None => 0,
        DebugInfo::LineTables => 1,
    }
}

fn hash_optimization_mode(mode: OptimizationMode, hasher: &mut blake3::Hasher) {
    match mode {
        OptimizationMode::Baseline => {
            hasher.update(&[0]);
        }
        OptimizationMode::Level(level) => {
            hasher.update(&[1, opt_level_tag(level)]);
        }
    }
}

fn opt_level_tag(level: OptLevel) -> u8 {
    match level {
        OptLevel::O0 => 0,
        OptLevel::O1 => 1,
        OptLevel::O2 => 2,
        OptLevel::O3 => 3,
        OptLevel::Os => 4,
        OptLevel::Oz => 5,
    }
}

fn module_artifact_kind_tag(kind: ModuleArtifactKind) -> u8 {
    match kind {
        ModuleArtifactKind::Object => 0,
        ModuleArtifactKind::LlvmBitcode => 1,
    }
}

fn lto_mode_tag(mode: LtoMode) -> u8 {
    match mode {
        LtoMode::Off => 0,
        LtoMode::Full => 1,
    }
}

fn std_mode_tag(mode: StdMode) -> u8 {
    match mode {
        StdMode::BootstrapStd => 0,
        StdMode::FullStd => 1,
    }
}

fn hash_test_selection(
    config: &Config,
    selection: Option<&TestSelection>,
    hasher: &mut blake3::Hasher,
) -> Result<(), String> {
    if !config.test_mode {
        if selection.is_some() {
            return Err("test selection supplied for a non-test compilation".into());
        }
        hasher.update(&[0]);
        return Ok(());
    }

    let selection =
        selection.ok_or_else(|| "test compilation is missing test selection".to_string())?;
    hasher.update(&[1]);
    if let Some(filter) = selection.normalized_name_filter() {
        hasher.update(&[1]);
        hasher.update(filter.as_bytes());
        hasher.update(&[0]);
    } else {
        hasher.update(&[0]);
    }

    let mut tags = selection.normalized_tags().to_vec();
    tags.sort();
    hasher.update(&(tags.len() as u32).to_le_bytes());
    for tag in tags {
        hasher.update(tag.as_bytes());
        hasher.update(&[0]);
    }
    Ok(())
}

fn profile_name(profile: BuildProfile) -> &'static str {
    match profile {
        BuildProfile::Debug => "debug",
        BuildProfile::Release => "release",
    }
}

fn hash_source_inputs(config: &Config, hasher: &mut blake3::Hasher) -> Result<(), String> {
    if config.is_script {
        let source_path = config.src.canonicalize().map_err(|e| {
            format!(
                "failed to canonicalize script source '{}': {}",
                config.src.display(),
                e
            )
        })?;

        hasher.update(source_path.to_string_lossy().as_bytes());
        hasher.update(&[0]);

        let content = std::fs::read(&source_path).map_err(|e| {
            format!(
                "failed to read script source '{}': {}",
                source_path.display(),
                e
            )
        })?;
        hasher.update(&(content.len() as u64).to_le_bytes());
        hasher.update(&content);
        return Ok(());
    }

    let package_root = config.src.canonicalize().map_err(|e| {
        format!(
            "failed to canonicalize package source root '{}': {}",
            config.src.display(),
            e
        )
    })?;
    let source_root = package_root.join(SOURCE_DIRECTORY);
    if !source_root.exists() {
        return Err(format!(
            "source directory missing: '{}'",
            source_root.display()
        ));
    }

    hasher.update(package_root.to_string_lossy().as_bytes());
    hasher.update(&[0]);

    let mut files = Vec::new();
    collect_source_files(&source_root, &mut files)?;
    files.sort();

    hasher.update(&(files.len() as u32).to_le_bytes());
    for file in files {
        let relative = file
            .strip_prefix(&source_root)
            .unwrap_or(file.as_path())
            .to_string_lossy();
        hasher.update(relative.as_bytes());
        hasher.update(&[0]);

        let content = std::fs::read(&file)
            .map_err(|e| format!("failed to read source file '{}': {}", file.display(), e))?;
        hasher.update(&(content.len() as u64).to_le_bytes());
        hasher.update(&content);
    }

    Ok(())
}

fn collect_source_files(directory: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let mut entries = std::fs::read_dir(directory)
        .map_err(|e| {
            format!(
                "failed to read source directory '{}': {}",
                directory.display(),
                e
            )
        })?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| {
            format!(
                "failed to enumerate entries in '{}': {}",
                directory.display(),
                e
            )
        })?;

    entries.sort_by(|a, b| a.path().cmp(&b.path()));

    for entry in entries {
        let path = entry.path();
        if path.is_symlink() {
            continue;
        }

        if path.is_dir() {
            collect_source_files(&path, out)?;
            continue;
        }

        if path.is_file() {
            if path.extension().and_then(|ext| ext.to_str()) == Some("tr") {
                out.push(path);
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{
        compute_package_fingerprint_input, compute_package_fingerprint_input_with_test_selection,
    };
    use compiler::{
        PackageIndex,
        compile::{
            config::{
                BuildProfile, Config, DebugInfo, DebugOptions, LtoMode, ModuleArtifactKind,
                OptLevel, OptimizationMode, PackageKind, StdMode,
            },
            context::{CompilerArenas, CompilerContext, CompilerStore},
            test_collector::TestSelection,
        },
        diagnostics::DiagCtx,
    };
    use rustc_hash::FxHashMap;
    use std::{
        fs,
        path::PathBuf,
        rc::Rc,
        sync::atomic::{AtomicU64, Ordering},
    };

    static NEXT_TEST_DIRECTORY: AtomicU64 = AtomicU64::new(0);

    fn test_root() -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "taro-fingerprint-test-{}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos(),
            NEXT_TEST_DIRECTORY.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&root).expect("temp root");
        root
    }

    fn base_config(source: PathBuf) -> Config {
        Config {
            name: "fingerprint-test".into(),
            identifier: "fingerprint-test".into(),
            src: source,
            dependencies: FxHashMap::default(),
            index: PackageIndex::new(1),
            kind: PackageKind::Executable,
            executable_out: None,
            no_std_prelude: true,
            is_script: true,
            profile: BuildProfile::Debug,
            codegen: Default::default(),
            overflow_checks: true,
            debug: DebugOptions::default(),
            test_mode: false,
            std_mode: StdMode::BootstrapStd,
            is_std_provider: true,
        }
    }

    fn with_context<R>(f: impl for<'ctx> FnOnce(&CompilerContext<'ctx>, PathBuf) -> R) -> R {
        let root = test_root();
        let source = root.join("main.tr");
        fs::write(&source, "func main() {}\n").expect("source");
        let dcx = Rc::new(DiagCtx::new(root.clone()));
        let arenas = CompilerArenas::new();
        let store = CompilerStore::new(
            &arenas,
            root.join("objects"),
            &dcx,
            None,
            BuildProfile::Debug,
        )
        .unwrap_or_else(|_| panic!("store"));
        let context = CompilerContext::new(dcx, store);
        let result = f(&context, source);
        let _ = fs::remove_dir_all(root);
        result
    }

    #[test]
    fn output_path_does_not_change_compilation_fingerprint() {
        with_context(|context, source| {
            let first = base_config(source.clone());
            let mut second = base_config(source);
            second.executable_out = Some(PathBuf::from("elsewhere/program"));
            let known = FxHashMap::default();

            let first = compute_package_fingerprint_input(context, &first, &known).unwrap();
            let second = compute_package_fingerprint_input(context, &second, &known).unwrap();
            assert_eq!(first.package_fingerprint, second.package_fingerprint);
        });
    }

    #[test]
    fn output_kind_and_overflow_mode_change_compilation_fingerprint() {
        with_context(|context, source| {
            let base = base_config(source.clone());
            let mut library = base_config(source.clone());
            library.kind = PackageKind::Library;
            let mut wrapping = base_config(source);
            wrapping.overflow_checks = false;
            let known = FxHashMap::default();

            let base = compute_package_fingerprint_input(context, &base, &known)
                .unwrap()
                .package_fingerprint;
            let library = compute_package_fingerprint_input(context, &library, &known)
                .unwrap()
                .package_fingerprint;
            let wrapping = compute_package_fingerprint_input(context, &wrapping, &known)
                .unwrap()
                .package_fingerprint;
            assert_ne!(base, library);
            assert_ne!(base, wrapping);
        });
    }

    #[test]
    fn debug_info_mode_changes_compilation_fingerprint() {
        with_context(|context, source| {
            let without_debug_info = base_config(source.clone());
            let mut with_line_tables = base_config(source);
            with_line_tables.debug.debug_info = DebugInfo::LineTables;
            let known = FxHashMap::default();

            let without_debug_info =
                compute_package_fingerprint_input(context, &without_debug_info, &known)
                    .unwrap()
                    .package_fingerprint;
            let with_line_tables =
                compute_package_fingerprint_input(context, &with_line_tables, &known)
                    .unwrap()
                    .package_fingerprint;
            assert_ne!(without_debug_info, with_line_tables);
        });
    }

    #[test]
    fn optimization_mode_changes_compilation_fingerprint() {
        with_context(|context, source| {
            let baseline = base_config(source.clone());
            let mut optimized = base_config(source);
            optimized.codegen.optimization = OptimizationMode::Level(OptLevel::O2);
            let known = FxHashMap::default();

            let baseline = compute_package_fingerprint_input(context, &baseline, &known)
                .unwrap()
                .package_fingerprint;
            let optimized = compute_package_fingerprint_input(context, &optimized, &known)
                .unwrap()
                .package_fingerprint;
            assert_ne!(baseline, optimized);
        });
    }

    #[test]
    fn module_artifact_kind_changes_compilation_fingerprint() {
        with_context(|context, source| {
            let object = base_config(source.clone());
            let mut bitcode = base_config(source);
            bitcode.codegen.artifact = ModuleArtifactKind::LlvmBitcode;
            let known = FxHashMap::default();

            let object = compute_package_fingerprint_input(context, &object, &known)
                .unwrap()
                .package_fingerprint;
            let bitcode = compute_package_fingerprint_input(context, &bitcode, &known)
                .unwrap()
                .package_fingerprint;
            assert_ne!(object, bitcode);
        });
    }

    #[test]
    fn lto_mode_changes_compilation_fingerprint() {
        with_context(|context, source| {
            let mut off = base_config(source.clone());
            let mut full = base_config(source);
            off.codegen.artifact = ModuleArtifactKind::LlvmBitcode;
            full.codegen.artifact = ModuleArtifactKind::LlvmBitcode;
            full.codegen.lto = LtoMode::Full;
            let known = FxHashMap::default();

            let off = compute_package_fingerprint_input(context, &off, &known)
                .unwrap()
                .package_fingerprint;
            let full = compute_package_fingerprint_input(context, &full, &known)
                .unwrap()
                .package_fingerprint;
            assert_ne!(off, full);
        });
    }

    #[test]
    fn normalized_test_selection_changes_test_fingerprint() {
        with_context(|context, source| {
            let mut config = base_config(source);
            config.test_mode = true;
            let known = FxHashMap::default();
            let alpha = TestSelection::new(Some(" Alpha ".into()), vec!["SMOKE".into()]);
            let alpha_equivalent = TestSelection::new(Some("alpha".into()), vec!["smoke".into()]);
            let beta = TestSelection::new(Some("beta".into()), vec!["smoke".into()]);

            let alpha = compute_package_fingerprint_input_with_test_selection(
                context,
                &config,
                &known,
                Some(&alpha),
            )
            .unwrap()
            .package_fingerprint;
            let alpha_equivalent = compute_package_fingerprint_input_with_test_selection(
                context,
                &config,
                &known,
                Some(&alpha_equivalent),
            )
            .unwrap()
            .package_fingerprint;
            let beta = compute_package_fingerprint_input_with_test_selection(
                context,
                &config,
                &known,
                Some(&beta),
            )
            .unwrap()
            .package_fingerprint;

            assert_eq!(alpha, alpha_equivalent);
            assert_ne!(alpha, beta);
        });
    }

    #[test]
    fn source_contents_change_compilation_fingerprint() {
        with_context(|context, source| {
            let config = base_config(source.clone());
            let known = FxHashMap::default();
            let before = compute_package_fingerprint_input(context, &config, &known)
                .unwrap()
                .package_fingerprint;
            fs::write(source, "func main() { print(\"changed\") }\n").expect("source update");
            let after = compute_package_fingerprint_input(context, &config, &known)
                .unwrap()
                .package_fingerprint;
            assert_ne!(before, after);
        });
    }
}
