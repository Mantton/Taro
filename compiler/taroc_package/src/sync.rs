use super::{
    git::{self, download_dependency},
    graph::{DependencyGraph, build_graph},
    identifier::PackageIdentifier,
    lockfile::{self, LockFile},
    manifest::{DependencyKind, Manifest},
};
use crate::LOCKFILE_VERSION;
use semver::Version;
use std::{
    collections::{HashMap, HashSet},
    fs,
    path::PathBuf,
};
use taroc_constants::{LOCK_FILE, MANIFEST_FILE};

// Maps Packages to a list of unique dependency usages
type DependencyMapping = HashMap<String, HashSet<DependencyKind>>;
type VersionSelectionMapping = HashMap<String, HashSet<DependencyKind>>;
type ManifestMapping = HashMap<String, HashMap<DependencyKind, (Manifest, PathBuf)>>;

pub fn sync_dependencies(
    root: &PathBuf,
) -> Result<(LockFile, DependencyGraph, HashMap<String, PathBuf>), String> {
    if root.join(LOCK_FILE).exists() {
        let _ = LockFile::parse(&root.join(LOCK_FILE))?;
        todo!("lockfile present");
    }

    // Download, Select, Install
    let (package, dependency_mapping, manifest_mapping, direct, local_mapping) =
        download_packages(&root)?;
    let version_selection = select_versions(dependency_mapping)?;
    install_dependencies(&version_selection)?;

    // Map, Generate, Write
    let dependencies = map_dependencies(version_selection, manifest_mapping, direct)?;
    let lockfile = generate_lockfile(dependencies, package.normalize());
    let graph = validate_lockfile(&lockfile)?;
    write_lockfile(&lockfile, &root)?;
    Ok((lockfile, graph, local_mapping))
}

fn download_packages(
    root: &PathBuf,
) -> Result<
    (
        PackageIdentifier,
        DependencyMapping,
        ManifestMapping,
        HashSet<String>,
        HashMap<String, PathBuf>,
    ),
    String,
> {
    let root_manifest = Manifest::parse(&root.join(MANIFEST_FILE))?;
    let package = root_manifest.identifier();
    let mut manifests = vec![(root.clone(), root_manifest)];
    let mut visited = HashMap::new();
    let mut manifest_mapping = ManifestMapping::default();
    let mut seen = HashSet::new();
    let mut direct = HashSet::new();
    let mut local_mapping = HashMap::new();
    while let Some((root_path, manifest)) = manifests.pop() {
        let dependencies = manifest.require.unwrap_or_default();
        for (package, metadata) in dependencies.iter() {
            let normalized = PackageIdentifier::normalized(package);
            let package_identifier = PackageIdentifier::from(package.clone());
            let kind = metadata.kind(&root_path)?;
            let qualified = kind.normalized(&package);

            if root.eq(&root_path) {
                direct.insert(normalized.clone());
            }

            // avoid cylic dependency loop, action cycle will be documented at later stage
            if seen.contains(&qualified) {
                continue;
            }
            seen.insert(qualified);

            let source = if let Some(path) = metadata.path() {
                let path = relative_path(&root_path, path)?;
                local_mapping.insert(kind.revision(), path.clone());
                path
            } else {
                download_dependency(&package_identifier, metadata)?
            };

            let dependency_manifest = Manifest::parse(&source.join(MANIFEST_FILE))?;
            manifests.push((source, dependency_manifest.clone()));

            visited
                .entry(normalized.clone())
                .or_insert_with(HashSet::new)
                .insert(kind.clone());

            manifest_mapping
                .entry(normalized.clone())
                .or_insert_with(HashMap::new)
                .insert(kind, (dependency_manifest, root_path.clone()));
        }
    }

    Ok((package, visited, manifest_mapping, direct, local_mapping))
}

fn relative_path(root: &PathBuf, target: PathBuf) -> Result<PathBuf, String> {
    let path = root.join(target);
    let path = path
        .canonicalize()
        .map_err(|err| format!("failed to resolve path {:?}, {}", path, err))?;

    Ok(path)
}

fn select_versions(dependencies: DependencyMapping) -> Result<VersionSelectionMapping, String> {
    let mut mapping: VersionSelectionMapping = HashMap::default();

    for (package, usages) in dependencies {
        let mut selections = HashSet::new();
        let mut seen_versions = HashSet::new();

        for usage in usages.into_iter() {
            match usage {
                DependencyKind::Commit(_) | DependencyKind::Local(_) => {
                    selections.insert(usage);
                }
                DependencyKind::Version(version) => {
                    seen_versions.insert(version);
                }
            }
        }

        let selected_versions = select_majors(seen_versions);
        selected_versions.into_iter().for_each(|version| {
            selections.insert(DependencyKind::Version(version));
        });

        mapping.insert(package, selections);
    }

    Ok(mapping)
}

fn select_majors(versions: HashSet<Version>) -> HashSet<Version> {
    let mut latest_by_major: HashMap<u64, Version> = HashMap::new();

    for version in versions {
        latest_by_major
            .entry(version.major)
            .and_modify(|current| {
                if &version > current {
                    *current = version.clone();
                }
            })
            .or_insert(version);
    }

    latest_by_major.into_values().collect()
}

fn install_dependencies(mapping: &VersionSelectionMapping) -> Result<(), String> {
    for (normalized_package, selections) in mapping.iter() {
        // iterate over selected revisions
        for selection in selections {
            if matches!(selection, DependencyKind::Local(_)) {
                continue;
            }

            let revision = selection.revision();
            git::install_revision(normalized_package.clone(), revision)?;
        }
    }

    Ok(())
}

fn map_dependencies(
    version_mapping: VersionSelectionMapping,
    manifest_mapping: ManifestMapping,
    direct_dependencies: HashSet<String>,
) -> Result<Vec<lockfile::LockfilePackage>, String> {
    let mut packages = Vec::new();
    // iterate over our packages and it's selected revisions
    for (normalized_package, selections) in version_mapping.iter() {
        // iterate over selected revisions
        for selection in selections {
            // fetch manifest for selection
            let (manifest, package_path) = manifest_mapping
                .get(normalized_package)
                .expect("package must be mapped")
                .get(&selection)
                .expect("revision must be mapped");

            // map dependencies to locked versions
            let mut package_dependencies = HashSet::new();
            if let Some(dependencies) = &manifest.require {
                // iterate over dependencies
                for (package, metadata) in dependencies.iter() {
                    // generate normalized package name
                    let normalized_package = PackageIdentifier::normalized(package);
                    // get selections for this package
                    let dependency_selections = version_mapping
                        .get(&normalized_package)
                        .expect("expected package selections");

                    let dependency = match metadata.kind(package_path)? {
                        DependencyKind::Version(version) => {
                            dependency_selections
                                .iter()
                                .find(|dep| matches!(dep, DependencyKind::Version(v) if v.major == version.major))
                                .expect("missing version in selections")
                                .clone()
                        }
                        value => {
                            if !dependency_selections.contains(&value) {
                                panic!("expected dependency to be found");
                            }
                            value
                        },
                    };

                    // we've got the dependency & it's locked revision, now tag to version if multiple
                    if dependency_selections.len() > 1 {
                        // <identifier>@<version>
                        package_dependencies.insert(dependency.normalized(package));
                    } else {
                        // <identifier>
                        package_dependencies.insert(PackageIdentifier::normalized(package));
                    }
                }
            };

            let entry = lockfile::LockfilePackage {
                name: normalized_package.clone(),
                require: if !package_dependencies.is_empty() {
                    Some(package_dependencies)
                } else {
                    None
                },
                source: if matches!(selection, DependencyKind::Local(_)) {
                    "local".into()
                } else {
                    "git".into()
                },
                revision: selection.revision(),
                direct: direct_dependencies.contains(normalized_package),
            };

            packages.push(entry);
        }
    }

    Ok(packages)
}

fn generate_lockfile(package: Vec<lockfile::LockfilePackage>, name: String) -> LockFile {
    LockFile {
        version: LOCKFILE_VERSION,
        package,
        name,
    }
}

fn write_lockfile(lockfile: &LockFile, root: &PathBuf) -> Result<PathBuf, String> {
    use std::io::Write;

    let path = root.join(LOCK_FILE);
    let contents = toml::to_string_pretty(lockfile)
        .map_err(|err| format!("failed to serialize lockfile: {}", err))?;
    let mut file =
        fs::File::create(&path).map_err(|err| format!("failed to create lockfile: {}", err))?;
    file.write_all(contents.as_bytes())
        .map_err(|err| format!("failed to write lockfile: {}", err))?;

    Ok(path)
}

fn validate_lockfile(lockfile: &LockFile) -> Result<DependencyGraph, String> {
    build_graph(lockfile)
}
