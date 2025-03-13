use super::identifier::PackageIdentifier;
use rustc_hash::FxHashMap;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::{collections::hash_map::Entry, path::PathBuf};
use taroc_constants::STD_PREFIX;
use taroc_error::{CompileError, CompileResult};

#[derive(Deserialize, Debug, Clone)]
pub struct Manifest {
    pub package: Metadata,
    pub require: Option<DependencyMap>,
}

impl Manifest {
    pub fn parse(path: &PathBuf) -> Result<Manifest, String> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| format!("failed to read {:?}, {}", path, e))?;
        let manifest = toml::from_str::<Manifest>(&content)
            .map_err(|e| format!("failed to parse {:?}, {}", path, e))?;
        Ok(manifest)
    }

    pub fn identifier(&self) -> PackageIdentifier {
        PackageIdentifier::from(self.package.name.clone())
    }
}

impl Manifest {
    pub fn mappings(&self) -> CompileResult<FxHashMap<String, String>> {
        let Some(require) = &self.require else {
            return Ok(FxHashMap::default());
        };

        let mut table = FxHashMap::default();
        for (id, data) in require {
            let alias = data.alias(id);

            if alias == STD_PREFIX {
                return Err(CompileError::Message(
                    "dependency with 'std' alias is not permitted".into(),
                ));
            }

            if &alias == self.identifier().segments().last().unwrap() {
                return Err(CompileError::Message(
                    "dependency with alias matching package is not permitted".into(),
                ));
            }

            match table.entry(alias) {
                Entry::Vacant(e) => {
                    e.insert(id.clone());
                }
                Entry::Occupied(..) => {
                    return Err(CompileError::Message(
                        "dependency alias '{}' is already defined".into(),
                    ));
                }
            }
        }

        return Ok(table);
    }
}

#[derive(Deserialize, Debug, Clone)]
pub struct Metadata {
    pub name: String,
}

pub type DependencyMap = FxHashMap<String, Dependency>;

#[derive(Deserialize, Debug, Clone)]
#[serde(untagged)]
pub enum Dependency {
    Simple(semver::Version), // For "com.taro/bar" = "1.0.0"
    Detailed {
        version: Option<semver::Version>,
        path: Option<PathBuf>,
        commit: Option<String>,
        alias: Option<String>,
    }, // For table format like { path = "../foo", version = "1.0.0" }
}

impl Dependency {
    pub fn version(&self) -> Option<semver::Version> {
        match self {
            Dependency::Simple(version) => Some(version.clone()),
            Dependency::Detailed { version, .. } => version.clone(),
        }
    }

    pub fn path(&self) -> Option<PathBuf> {
        match self {
            Dependency::Simple(_) => None,
            Dependency::Detailed { path, .. } => path.clone(),
        }
    }

    pub fn commit(&self) -> Option<String> {
        match self {
            Dependency::Simple(_) => None,
            Dependency::Detailed { commit, .. } => commit.clone(),
        }
    }

    pub fn kind(&self, root: &PathBuf) -> Result<DependencyKind, String> {
        match self {
            Dependency::Simple(version) => Ok(DependencyKind::Version(version.clone())),
            Dependency::Detailed {
                version,
                commit,
                path,
                ..
            } => {
                if let Some(version) = version {
                    Ok(DependencyKind::Version(version.clone()))
                } else if let Some(commit) = commit {
                    Ok(DependencyKind::Commit(commit.clone()))
                } else if let Some(path) = path {
                    let path = root
                        .join(path)
                        .canonicalize()
                        .map_err(|err| format!("failed to resolve path {:?}, {}", path, err))?;
                    Ok(DependencyKind::Local(path))
                } else {
                    Err("invalid dependency entry".into())
                }
            }
        }
    }

    fn alias(&self, id: &String) -> String {
        let alias = match self {
            Dependency::Detailed { alias, .. } => alias.clone(),
            Dependency::Simple(..) => None,
        };

        if let Some(alias) = alias {
            return alias;
        }

        return id.split("/").last().unwrap().to_string();
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DependencyKind {
    Commit(String),
    Version(semver::Version),
    Local(PathBuf),
}

impl DependencyKind {
    pub fn normalized(&self, package: &String) -> String {
        format!(
            "{}@{}",
            PackageIdentifier::normalized(package),
            self.revision()
        )
    }
    pub fn revision(&self) -> String {
        match self {
            DependencyKind::Commit(commit) => format!("commit-{}", commit),
            DependencyKind::Version(version) => format!("v{}", version),
            DependencyKind::Local(path) => {
                let mut hasher = Sha256::new();
                hasher.update(path.to_string_lossy().as_bytes());
                let hash = hasher.finalize();
                format!("local-{:x}", hash)
            }
        }
    }
}
