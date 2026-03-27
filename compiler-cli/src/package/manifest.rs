pub use compiler::package::manifest::{
    Manifest, NormalizedManifest, PackageIdentifier, RefSpec, SourceSpec, UnresolvedDependency,
};

use crate::package::utils::{get_package_name, language_home};
use compiler::{compile::config::PackageKind, constants::PACKAGE_SOURCE};
use ecow::EcoString;
use rustc_hash::FxHashMap;
use std::{hash::Hash, os::unix::ffi::OsStrExt, path::PathBuf};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct ResolvedPackage {
    pub package: PackageIdentifier,
    pub source: ResolvedSource,
    pub kind: PackageKind,
    pub no_std_prelude: bool,
}

impl ResolvedPackage {
    pub fn path(&self) -> Result<PathBuf, String> {
        match &self.source {
            ResolvedSource::Path { abs } => Ok(abs.clone()),
            ResolvedSource::Git { revision, .. } => {
                let name = self.package.0.clone();
                let path = format!("{name}-{revision}");
                Ok(language_home()?.join(PACKAGE_SOURCE).join(&path))
            }
        }
    }

    pub fn unique_identifier(&self) -> Result<EcoString, String> {
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

        let hash = hasher.finalize().to_string();
        let short = hash.get(0..8).unwrap_or(hash.as_str());
        Ok(format!("{}-{}", name, short).into())
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
        requested: EcoString,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Selector {
    Tag(EcoString),
    Branch(EcoString),
    Commit(git2::Oid),
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
                let name = e.weight().name.clone();
                let id = e
                    .weight()
                    .dependency
                    .unique_identifier()
                    .map_err(|err| err.to_string())?;
                Ok((name, id.into()))
            })
            .collect::<Result<FxHashMap<_, _>, String>>()
    }
}
