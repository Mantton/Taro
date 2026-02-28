use compiler::{
    compile::{
        config::{BuildProfile, Config},
        context::CompilerContext,
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
    hasher.update(b"taro.incremental.v0.package");

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

    hasher.update(profile_name(config.profile).as_bytes());
    hasher.update(&[
        config.overflow_checks as u8,
        config.no_std_prelude as u8,
        config.test_mode as u8,
    ]);

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
