use super::utils::{canonicalize_rel, derive_git_url, get_package_name, normalize_module_path};
use crate::compile::config::PackageKind;
use ecow::EcoString;
use rustc_hash::FxHashMap;
use serde::Deserialize;
use std::hash::Hash;
use std::path::PathBuf;

#[derive(Deserialize, Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct PackageIdentifier(pub EcoString);

impl PackageIdentifier {
    pub fn hashed_name(&self) -> String {
        blake3::hash(self.0.as_bytes()).to_string()
    }
}

#[derive(Deserialize, Debug, Clone)]
pub struct Manifest {
    pub package: Metadata,
    pub require: Option<DependencyMap>,
}

impl Manifest {
    pub fn parse(path: PathBuf) -> Result<Manifest, String> {
        let content = std::fs::read_to_string(&path)
            .map_err(|e| format!("failed to read manifest file {:?}, {}", path, e))?;
        let manifest = toml::from_str::<Manifest>(&content)
            .map_err(|e| format!("failed to parse manifest file {:?}, {}", path, e))?;
        Ok(manifest)
    }
}

#[derive(Deserialize, Debug, Clone)]
pub struct Metadata {
    pub name: EcoString,
    #[serde(default)]
    pub kind: PackageKind,
    #[serde(default)]
    pub no_std_prelude: bool,
}

pub type DependencyMap = FxHashMap<String, ManifestDependency>;

#[derive(Deserialize, Debug, Clone)]
#[serde(untagged)]
pub enum ManifestDependency {
    Simple(semver::VersionReq),
    Detailed {
        version: Option<semver::VersionReq>,
        tag: Option<EcoString>,
        branch: Option<EcoString>,
        commit: Option<EcoString>,
        path: Option<PathBuf>,
        alias: Option<EcoString>,
        git: Option<EcoString>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RefSpec {
    Commit(EcoString),
    Tag(EcoString),
    Branch(EcoString),
    Version(semver::VersionReq),
    DefaultBranch,
}

impl RefSpec {
    pub fn request_string(&self) -> EcoString {
        match self {
            RefSpec::Commit(revision) => format!("commit:{}", revision).into(),
            RefSpec::Tag(tag) => format!("tag:{}", tag).into(),
            RefSpec::Branch(branch) => format!("branch:{}", branch).into(),
            RefSpec::Version(version_req) => format!("version:{}", version_req).into(),
            RefSpec::DefaultBranch => "default-branch".into(),
        }
    }

    pub fn is_mutable(&self) -> bool {
        matches!(
            self,
            RefSpec::Branch(_) | RefSpec::DefaultBranch | RefSpec::Version(_)
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SourceSpec {
    Path { abs: PathBuf },
    Git { url: EcoString, refspec: RefSpec },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnresolvedDependency {
    pub package: PackageIdentifier,
    pub source: SourceSpec,
}

impl ManifestDependency {
    pub fn spec_with_base(
        &self,
        package: &str,
        base_url: &std::path::Path,
    ) -> Result<(EcoString, UnresolvedDependency), String> {
        let package = EcoString::from(normalize_module_path(package)?);
        let (source, alias) = match self {
            ManifestDependency::Simple(version_req) => {
                let url = derive_git_url(&package).ok_or_else(|| {
                    format!("cannot derive git URL for `{package}`; add `git = \"...\"`")
                })?;
                (
                    SourceSpec::Git {
                        url,
                        refspec: RefSpec::Version(version_req.clone()),
                    },
                    None,
                )
            }
            ManifestDependency::Detailed {
                version,
                tag,
                branch,
                commit,
                path,
                alias,
                git,
            } => {
                let has_gitish = git.is_some()
                    || tag.is_some()
                    || branch.is_some()
                    || commit.is_some()
                    || version.is_some();
                if path.is_some() && has_gitish {
                    return Err(format!(
                        "`path` cannot be combined with git fields for `{package}`"
                    ));
                }
                if commit.is_some() && (tag.is_some() || branch.is_some()) {
                    return Err(format!(
                        "`commit` cannot be combined with `tag` or `branch` for `{package}`"
                    ));
                }
                if tag.is_some() && branch.is_some() {
                    return Err(format!(
                        "`tag` cannot be combined with `branch` for `{package}`"
                    ));
                }
                let selector_count = version.is_some() as usize
                    + tag.is_some() as usize
                    + branch.is_some() as usize
                    + commit.is_some() as usize;
                if selector_count > 1 {
                    return Err(format!(
                        "`version`, `tag`, `branch`, and `commit` are mutually exclusive for `{package}`"
                    ));
                }

                if let Some(p) = path.clone() {
                    let abs = canonicalize_rel(base_url, p)?;
                    (SourceSpec::Path { abs }, alias.clone())
                } else {
                    let url = if let Some(u) = git.clone() {
                        u
                    } else {
                        derive_git_url(&package).ok_or_else(|| {
                            format!("cannot derive git URL for `{package}`; add `git = \"...\"`")
                        })?
                    };
                    let refspec = if let Some(c) = commit.clone() {
                        RefSpec::Commit(c)
                    } else if let Some(t) = tag.clone() {
                        RefSpec::Tag(t)
                    } else if let Some(b) = branch.clone() {
                        RefSpec::Branch(b)
                    } else if let Some(version) = version {
                        RefSpec::Version(version.clone())
                    } else {
                        RefSpec::DefaultBranch
                    };
                    (SourceSpec::Git { url, refspec }, alias.clone())
                }
            }
        };

        let dep = UnresolvedDependency {
            package: PackageIdentifier(package.clone()),
            source,
        };

        let name = if let Some(alias) = alias {
            alias
        } else {
            get_package_name(&package)?
        };

        Ok((name, dep))
    }
}

#[derive(Debug, Clone)]
pub struct NormalizedManifest {
    pub path: PackageIdentifier,
    pub dependencies: FxHashMap<EcoString, UnresolvedDependency>,
    pub kind: PackageKind,
    pub no_std_prelude: bool,
}

impl Manifest {
    pub fn normalize(&self, base_url: PathBuf) -> Result<NormalizedManifest, String> {
        let name = normalize_module_path(&self.package.name)?;
        let root_package_name = get_package_name(&name)?;
        let mut errs: Vec<String> = Vec::new();
        let mut out = FxHashMap::default();

        for (key, dep) in self.require.iter().flatten() {
            let key = match normalize_module_path(key) {
                Ok(k) => PackageIdentifier(EcoString::from(k)),
                Err(e) => {
                    errs.push(format!("dependency `{key}`: {e}"));
                    continue;
                }
            };

            match dep.spec_with_base(&key.0, &base_url) {
                Ok((alias, mut spec)) => {
                    spec.package = key.clone();
                    if out.contains_key(&alias) {
                        return Err(format!("multiple dependencies with name/alias '{}'", alias));
                    } else if alias == root_package_name {
                        errs.push(format!(
                            "dependency `{}`: cannot have alias/name matching that of package",
                            spec.package.0,
                        ));
                    }
                    out.insert(alias, spec);
                }
                Err(e) => errs.push(format!("`{key:?}`: {e}")),
            }
        }

        if errs.is_empty() {
            Ok(NormalizedManifest {
                path: PackageIdentifier(name.into()),
                dependencies: out,
                kind: self.package.kind,
                no_std_prelude: self.package.no_std_prelude,
            })
        } else {
            Err(errs.join("\n"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Manifest;
    use std::{fs::create_dir_all, path::PathBuf};

    fn temp_dir(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "taro-manifest-test-{}-{}-{}",
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

    fn normalize_manifest(source: &str) -> Result<super::NormalizedManifest, String> {
        let manifest = toml::from_str::<Manifest>(source).expect("manifest");
        manifest.normalize(temp_dir("base"))
    }

    #[test]
    fn rejects_package_ids_with_extra_path_segments() {
        let err = normalize_manifest(
            "[package]\nname = \"github.com/example/root/subpkg\"\nkind = \"library\"\n",
        )
        .expect_err("extra package path should fail");

        assert!(err.contains("host/owner/repo"));
    }

    #[test]
    fn rejects_conflicting_git_selectors() {
        let err = normalize_manifest(
            "[package]\nname = \"github.com/example/root\"\nkind = \"library\"\n\n[require]\n\"github.com/example/dep\" = { version = \"^1.0\", tag = \"v1.2.0\" }\n",
        )
        .expect_err("conflicting selectors should fail");

        assert!(err.contains("mutually exclusive"));
    }

    #[test]
    fn rejects_path_combined_with_git_fields() {
        let err = normalize_manifest(
            "[package]\nname = \"github.com/example/root\"\nkind = \"library\"\n\n[require]\n\"github.com/example/dep\" = { path = \"../dep\", git = \"https://github.com/example/dep.git\" }\n",
        )
        .expect_err("path plus git should fail");

        assert!(err.contains("`path` cannot be combined"));
    }

    #[test]
    fn rejects_duplicate_aliases() {
        let err = normalize_manifest(
            "[package]\nname = \"github.com/example/root\"\nkind = \"library\"\n\n[require]\n\"github.com/example/a\" = { version = \"^1.0\", alias = \"dep\" }\n\"github.com/example/b\" = { version = \"^1.0\", alias = \"dep\" }\n",
        )
        .expect_err("duplicate alias should fail");

        assert!(err.contains("multiple dependencies with name/alias 'dep'"));
    }

    #[test]
    fn rejects_dependency_alias_matching_root_package() {
        let err = normalize_manifest(
            "[package]\nname = \"github.com/example/root\"\nkind = \"library\"\n\n[require]\n\"github.com/example/dep\" = { version = \"^1.0\", alias = \"root\" }\n",
        )
        .expect_err("root alias should fail");

        assert!(err.contains("cannot have alias/name matching"));
    }
}
