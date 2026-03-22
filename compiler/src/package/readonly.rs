use super::{
    lockfile::{self, LockFile},
    manifest::{Manifest, PackageIdentifier, SourceSpec},
    utils::{canonicalize_git_url, get_package_name, language_home},
};
use crate::{
    compile::config::PackageKind,
    constants::{LOCK_FILE, MANIFEST_FILE, PACKAGE_SOURCE},
};
use ecow::EcoString;
use rustc_hash::FxHashMap;
use std::{
    collections::HashSet,
    path::{Path, PathBuf},
};

#[derive(Debug, Clone)]
pub struct ReadonlyPackage {
    pub root: PathBuf,
    pub package_path: String,
    pub display_name: String,
    pub kind: PackageKind,
    pub no_std_prelude: bool,
    pub dependencies: FxHashMap<EcoString, String>,
    pub source: ReadonlyPackageSource,
}

impl ReadonlyPackage {
    pub fn unique_identifier(&self) -> Result<String, String> {
        let mut hasher = blake3::Hasher::new();
        match &self.source {
            ReadonlyPackageSource::Path => {
                hasher.update(self.root.to_string_lossy().as_bytes());
            }
            ReadonlyPackageSource::Git { url, revision } => {
                hasher.update(url.as_bytes());
                hasher.update(revision.as_bytes());
            }
        }

        let hash = hasher.finalize().to_string();
        let short = hash.get(0..8).unwrap_or(hash.as_str());
        Ok(format!("{}-{}", self.display_name, short))
    }
}

#[derive(Debug, Clone)]
pub enum ReadonlyPackageSource {
    Path,
    Git { url: String, revision: String },
}

pub fn load_package_graph(root: &Path) -> Result<Vec<ReadonlyPackage>, String> {
    load_package_graph_with_language_home(root, None)
}

fn load_package_graph_with_language_home(
    root: &Path,
    language_home_override: Option<&Path>,
) -> Result<Vec<ReadonlyPackage>, String> {
    let lockfile = lockfile::load(&root.join(LOCK_FILE))?;
    ReadonlyPackageLoader::new(lockfile, language_home_override.map(PathBuf::from))
        .load(root.to_path_buf())
}

struct ReadonlyPackageLoader {
    lockfile: Option<LockFile>,
    language_home_override: Option<PathBuf>,
    ordered: Vec<ReadonlyPackage>,
    loaded: FxHashMap<PathBuf, ReadonlyPackage>,
    visiting: HashSet<PathBuf>,
}

impl ReadonlyPackageLoader {
    fn new(lockfile: Option<LockFile>, language_home_override: Option<PathBuf>) -> Self {
        Self {
            lockfile,
            language_home_override,
            ordered: vec![],
            loaded: FxHashMap::default(),
            visiting: HashSet::default(),
        }
    }

    fn load(mut self, root: PathBuf) -> Result<Vec<ReadonlyPackage>, String> {
        self.visit_package(root, ReadonlyPackageSource::Path)?;
        Ok(self.ordered)
    }

    fn visit_package(
        &mut self,
        root: PathBuf,
        source: ReadonlyPackageSource,
    ) -> Result<ReadonlyPackage, String> {
        let root = root
            .canonicalize()
            .map_err(|e| format!("failed to resolve package root '{}': {}", root.display(), e))?;
        if let Some(existing) = self.loaded.get(&root) {
            return Ok(existing.clone());
        }
        if !self.visiting.insert(root.clone()) {
            return Err(format!(
                "dependency cycle detected involving '{}'",
                root.display()
            ));
        }

        let manifest = Manifest::parse(root.join(MANIFEST_FILE))?;
        let manifest = manifest.normalize(root.clone())?;
        let package_path = manifest.path.0.to_string();
        let display_name = get_package_name(&package_path)?.to_string();
        let mut dependencies = FxHashMap::default();

        for (alias, dependency) in manifest.dependencies {
            let (dep_root, dep_source) = match dependency.source {
                SourceSpec::Path { abs } => (abs, ReadonlyPackageSource::Path),
                SourceSpec::Git { url, refspec } => {
                    let requested = refspec.request_string();
                    let (dep_root, revision, url) = self.resolve_git_dependency(
                        &dependency.package,
                        url.as_ref(),
                        requested.as_ref(),
                    )?;
                    (dep_root, ReadonlyPackageSource::Git { url, revision })
                }
            };

            let dependency = self.visit_package(dep_root, dep_source)?;
            let identifier = dependency.unique_identifier()?;
            if dependencies.insert(alias.clone(), identifier).is_some() {
                return Err(format!(
                    "multiple dependencies with the same alias '{}' in '{}'",
                    alias,
                    root.display()
                ));
            }
        }

        self.visiting.remove(&root);
        let package = ReadonlyPackage {
            root: root.clone(),
            package_path,
            display_name,
            kind: manifest.kind,
            no_std_prelude: manifest.no_std_prelude,
            dependencies,
            source,
        };
        self.loaded.insert(root.clone(), package.clone());
        self.ordered.push(package.clone());
        Ok(package)
    }

    fn resolve_git_dependency(
        &self,
        package: &PackageIdentifier,
        url: &str,
        requested: &str,
    ) -> Result<(PathBuf, String, String), String> {
        let lockfile = self.lockfile.as_ref().ok_or_else(|| {
            format!(
                "dependency `{}` requires '{}' for read-only IDE analysis",
                package.0, LOCK_FILE
            )
        })?;
        let canonical_url = canonicalize_git_url(url)?;
        let entry = if let Some(entry) =
            lockfile.find_git_request(package.0.as_ref(), &canonical_url, requested)
        {
            entry
        } else {
            let matches = lockfile.find_git_candidates(package.0.as_ref(), &canonical_url);
            if matches.len() == 1 {
                matches[0]
            } else if matches.is_empty() {
                return Err(format!(
                    "failed to resolve locked dependency `{}` ({requested})",
                    package.0
                ));
            } else {
                return Err(format!(
                    "dependency `{}` is ambiguous in '{}' for request `{requested}`",
                    package.0, LOCK_FILE
                ));
            }
        };

        let revision = entry.revision.clone().ok_or_else(|| {
            format!("lockfile entry for `{}` is missing a revision", package.0)
        })?;
        let home = if let Some(home) = &self.language_home_override {
            home.clone()
        } else {
            language_home()?
        };
        let root = home
            .join(PACKAGE_SOURCE)
            .join(format!("{}-{}", package.0, revision));
        let root = root.canonicalize().map_err(|e| {
            format!(
                "cached source for `{}` is unavailable at '{}': {}",
                package.0,
                root.display(),
                e
            )
        })?;
        Ok((root, revision, canonical_url))
    }
}

#[cfg(test)]
mod tests {
    use super::{ReadonlyPackageSource, load_package_graph_with_language_home};
    use crate::package::lockfile::{LockFile, LockPackage, LockSourceType, write as write_lockfile};
    use std::fs::{create_dir_all, write};
    use std::path::{Path, PathBuf};

    fn temp_dir(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "taro-package-readonly-{}-{}-{}",
            name,
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        create_dir_all(&path).expect("temp dir");
        path
    }

    fn write_file(path: &Path, contents: &str) {
        if let Some(parent) = path.parent() {
            create_dir_all(parent).expect("parent dir");
        }
        write(path, contents).expect("write file");
    }

    fn write_manifest(path: &Path, contents: &str) {
        write_file(&path.join("package.toml"), contents);
    }

    #[test]
    fn reads_path_dependencies_without_lockfile() {
        let workspace = temp_dir("path-graph");
        let dep = workspace.join("dep");
        let root = workspace.join("root");

        write_manifest(
            &dep,
            "[package]\nname = \"github.com/example/dep\"\nkind = \"library\"\n",
        );
        write_manifest(
            &root,
            "[package]\nname = \"github.com/example/root\"\nkind = \"executable\"\n\n[require]\n\"github.com/example/dep\" = { path = \"../dep\" }\n",
        );

        let ordered = load_package_graph_with_language_home(&root, None).expect("graph");
        assert_eq!(ordered.len(), 2);
        assert_eq!(ordered[0].display_name, "dep");
        assert_eq!(ordered[1].display_name, "root");
        assert_eq!(
            ordered[1]
                .dependencies
                .get("dep")
                .expect("dep alias"),
            &ordered[0].unique_identifier().expect("dep id")
        );
        assert!(matches!(ordered[0].source, ReadonlyPackageSource::Path));
    }

    #[test]
    fn resolves_locked_git_dependencies_from_installed_sources_only() {
        let workspace = temp_dir("locked-git");
        let home = workspace.join("home");
        let root = workspace.join("root");
        let revision = "0123456789abcdef0123456789abcdef01234567";
        let package_name = "github.com/example/dep";
        let source_root = home.join("sources").join(format!("{package_name}-{revision}"));

        write_manifest(
            &root,
            "[package]\nname = \"github.com/example/root\"\nkind = \"executable\"\n\n[require]\n\"github.com/example/dep\" = \"^1.2\"\n",
        );
        write_manifest(
            &source_root,
            "[package]\nname = \"github.com/example/dep\"\nkind = \"library\"\n",
        );

        let mut lockfile = LockFile::new();
        lockfile.package.push(LockPackage {
            node: "dep-node".into(),
            name: package_name.into(),
            kind: crate::compile::config::PackageKind::Library,
            no_std_prelude: false,
            source_type: LockSourceType::Git,
            url: Some("https://github.com/example/dep.git".into()),
            path: None,
            requested: "version:^1.2".into(),
            revision: Some(revision.into()),
            tree_hash: Some("blake3:abc".into()),
            deps: Default::default(),
        });
        write_lockfile(&root.join("package.lock"), &lockfile).expect("write lockfile");

        let ordered = load_package_graph_with_language_home(&root, Some(home.as_path()))
            .expect("graph");
        assert_eq!(ordered.len(), 2);
        assert!(matches!(
            ordered[0].source,
            ReadonlyPackageSource::Git { .. }
        ));
    }

    #[test]
    fn missing_or_ambiguous_git_lock_entries_error() {
        let workspace = temp_dir("git-errors");
        let home = workspace.join("home");
        let root = workspace.join("root");
        let package_name = "github.com/example/dep";

        write_manifest(
            &root,
            "[package]\nname = \"github.com/example/root\"\nkind = \"executable\"\n\n[require]\n\"github.com/example/dep\" = \"^1.2\"\n",
        );

        let missing = load_package_graph_with_language_home(&root, Some(home.as_path()))
            .expect_err("missing lockfile should fail");
        assert!(missing.contains("requires 'package.lock'"));

        let mut lockfile = LockFile::new();
        lockfile.package.push(LockPackage {
            node: "dep-a".into(),
            name: package_name.into(),
            kind: crate::compile::config::PackageKind::Library,
            no_std_prelude: false,
            source_type: LockSourceType::Git,
            url: Some("https://github.com/example/dep.git".into()),
            path: None,
            requested: "tag:v1.2.0".into(),
            revision: Some("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".into()),
            tree_hash: Some("blake3:a".into()),
            deps: Default::default(),
        });
        lockfile.package.push(LockPackage {
            node: "dep-b".into(),
            name: package_name.into(),
            kind: crate::compile::config::PackageKind::Library,
            no_std_prelude: false,
            source_type: LockSourceType::Git,
            url: Some("https://github.com/example/dep.git".into()),
            path: None,
            requested: "tag:v1.2.1".into(),
            revision: Some("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".into()),
            tree_hash: Some("blake3:b".into()),
            deps: Default::default(),
        });
        write_lockfile(&root.join("package.lock"), &lockfile).expect("write lockfile");

        let ambiguous = load_package_graph_with_language_home(&root, Some(home.as_path()))
            .expect_err("ambiguous lockfile should fail");
        assert!(ambiguous.contains("ambiguous"));
    }
}
