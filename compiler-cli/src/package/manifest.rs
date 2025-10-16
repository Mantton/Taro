use ecow::EcoString;
use rustc_hash::FxHashMap;
use serde::Deserialize;
use std::path::PathBuf;

#[derive(Deserialize, Debug, Clone)]
pub struct Manifest {
    pub package: Metadata,
    pub require: Option<DependencyMap>,
}

#[derive(Deserialize, Debug, Clone)]
pub struct Metadata {
    pub name: EcoString,
}

pub type DependencyMap = FxHashMap<String, Dependency>;

#[derive(Deserialize, Debug, Clone)]
#[serde(untagged)]
pub enum Dependency {
    Simple(semver::Version), // For "com.taro/bar" = "1.0.0"
    Detailed {
        version: Option<semver::Version>,
        path: Option<PathBuf>,
        commit: Option<EcoString>,
        alias: Option<EcoString>,
    }, // For table format like { path = "../foo", version = "1.0.0" }
}

impl Manifest {
    pub fn parse(path: &PathBuf) -> Result<Manifest, EcoString> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| format!("failed to read manifest file {:?}, {}", path, e))?;
        let manifest = toml::from_str::<Manifest>(&content)
            .map_err(|e| format!("failed to parse manifest file {:?}, {}", path, e))?;
        Ok(manifest)
    }

    pub fn package_name(&self) -> EcoString {
        self.package.name.clone()
    }
}
