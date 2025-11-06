use crate::package::utils::{
    canonicalize_rel, derive_git_url, get_package_name, language_home, normalize_module_path,
};
use compiler::constants::{PACKAGE_SOURCE, PACKAGE_STORE};
use ecow::EcoString;
use rustc_hash::FxHashMap;
use serde::Deserialize;
use std::{
    hash::Hash,
    os::unix::ffi::OsStrExt,
    path::{Path, PathBuf},
};

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
}

pub type DependencyMap = FxHashMap<String, ManifestDependency>;

#[derive(Deserialize, Debug, Clone)]
#[serde(untagged)]
pub enum ManifestDependency {
    // github.com/acme/foo = "1.2" or "^1.2.3"
    Simple(semver::VersionReq),
    // e.g.  { version="^1.2", tag="v1.2.3" | commit="deadbeef" | branch="main", path="../foo", alias="foo" }
    Detailed {
        version: Option<semver::VersionReq>, // semver constraint applied to tags
        tag: Option<EcoString>,              // exact tag to use (e.g., "v1.2.3" or "subdir/v1.2.3")
        branch: Option<EcoString>,           // optional selector
        commit: Option<EcoString>,           // exact commit wins if present
        path: Option<std::path::PathBuf>,    // local override
        alias: Option<EcoString>,
        git: Option<EcoString>, // optional explicit URL; can be derived from module path
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SourceSpec {
    Path { abs: std::path::PathBuf },
    Git { url: EcoString, refspec: RefSpec },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnresolvedDependency {
    pub package: PackageIdentifier,
    pub source: SourceSpec, // where/how to fetch
}

impl ManifestDependency {
    pub fn spec_with_base(
        &self,
        package: &str,
        base_url: &Path,
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

#[derive(Debug)]
pub struct NormalizedManifest {
    pub path: PackageIdentifier,
    pub dependencies: FxHashMap<EcoString, UnresolvedDependency>,
}

impl Manifest {
    pub fn normalize(&self, base_url: PathBuf) -> Result<NormalizedManifest, String> {
        let name = normalize_module_path(&self.package.name)?;
        let root_package_name = get_package_name(&name)?;
        let mut errs: Vec<String> = Vec::new();
        let mut out = FxHashMap::default();

        for (key, dep) in self.require.iter().flatten() {
            // normalize key first
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
                            "dependnecy `{}`: Cannot have alias/name matching that of package",
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
            })
        } else {
            Err(errs.join("\n"))
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ResolvedPackage {
    pub package: PackageIdentifier,
    pub source: ResolvedSource,
}

impl ResolvedPackage {
    pub fn path(&self) -> Result<PathBuf, String> {
        match &self.source {
            ResolvedSource::Path { abs } => Ok(abs.clone()),
            ResolvedSource::Git { revision, .. } => {
                let name = self.package.0.clone();
                let path = format!("{name}-{revision}");
                let package_source = language_home()?.join(PACKAGE_SOURCE).join(&path);
                let package_source = package_source
                    .canonicalize()
                    .map_err(|e| format!("failed to resolve path – {}", e))?;
                Ok(package_source)
            }
        }
    }

    pub fn unique_identifier(&self) -> Result<String, String> {
        let name = get_package_name(&self.package.0)?;
        let mut hasher = blake3::Hasher::new();
        match &self.source {
            ResolvedSource::Path { abs } => {
                hasher.update(abs.as_os_str().as_bytes());
            }
            ResolvedSource::Git { url, revision, .. } => {
                hasher.update(url.as_bytes());
                hasher.update(revision.as_bytes());
            }
        };

        Ok(format!("{}-{}", name, hasher.finalize().to_string()))
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ResolvedSource {
    Path {
        abs: PathBuf,
    },
    Git {
        url: EcoString,
        revision: git2::Oid,
        selector: Selector,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Selector {
    Tag(EcoString),    // e.g. "v1.2.3" or "subdir/v1.2.3"
    Branch(EcoString), // e.g. "main"
    Commit(git2::Oid), // explicit pin from the manifest
}

pub type DependencyGraph =
    petgraph::stable_graph::StableDiGraph<ResolvedPackage, DependencyGraphEdge>;
pub struct ValidatedDependencyGraph {
    pub graph: DependencyGraph,
    pub ordered: Vec<ResolvedPackage>,
}
pub struct DependencyGraphEdge {
    pub dependency: ResolvedPackage,
    pub name: EcoString,
}

impl ValidatedDependencyGraph {
    pub fn dependencies_for(
        &self,
        package: &ResolvedPackage,
    ) -> Result<FxHashMap<EcoString, String>, String> {
        let Some(node_idx) = self
            .graph
            .node_indices()
            .find(|&i| &self.graph[i] == package)
        else {
            return Ok(Default::default());
        };

        self.graph
            .edges_directed(node_idx, petgraph::Direction::Incoming)
            .map(|e| {
                let name = e.weight().name.clone(); // can't move out of &edge
                let id = e
                    .weight()
                    .dependency
                    .unique_identifier()
                    .map_err(|err| err.to_string())?; // ensure error is String
                Ok((name, id))
            })
            .collect::<Result<FxHashMap<_, _>, String>>() // try-collect
    }
}
