use crate::package::{
    manifest::{ResolvedPackage, ResolvedSource},
    utils::canonicalize_git_url,
};
use compiler::compile::config::PackageKind;
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, os::unix::ffi::OsStrExt, path::Path};

pub const LOCKFILE_VERSION: u32 = 1;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LockFile {
    pub version: u32,
    pub generated_by: String,
    #[serde(default)]
    pub package: Vec<LockPackage>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LockPackage {
    pub node: String,
    pub name: String,
    pub kind: PackageKind,
    pub no_std_prelude: bool,
    pub source_type: LockSourceType,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub url: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub path: Option<String>,
    pub requested: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub revision: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tree_hash: Option<String>,
    #[serde(default)]
    pub deps: BTreeMap<String, String>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum LockSourceType {
    Git,
    Path,
}

impl LockFile {
    pub fn new() -> Self {
        Self {
            version: LOCKFILE_VERSION,
            generated_by: format!("taro {}", env!("CARGO_PKG_VERSION")),
            package: Vec::new(),
        }
    }

    pub fn normalized(mut self) -> Self {
        self.package.sort_by(|a, b| a.node.cmp(&b.node));
        for package in &mut self.package {
            package.deps = package
                .deps
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
        }
        self
    }

    pub fn find_git_request(
        &self,
        name: &str,
        canonical_url: &str,
        requested: &str,
    ) -> Option<&LockPackage> {
        self.package.iter().find(|entry| {
            entry.source_type == LockSourceType::Git
                && entry.name == name
                && entry.url.as_deref() == Some(canonical_url)
                && entry.requested == requested
        })
    }
}

pub fn load(path: &Path) -> Result<Option<LockFile>, String> {
    if !path.exists() {
        return Ok(None);
    }

    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("failed to read lockfile '{}': {}", path.display(), e))?;
    let lock = toml::from_str::<LockFile>(&text)
        .map_err(|e| format!("failed to parse lockfile '{}': {}", path.display(), e))?;

    if lock.version != LOCKFILE_VERSION {
        return Err(format!(
            "unsupported lockfile version {} (expected {})",
            lock.version, LOCKFILE_VERSION
        ));
    }

    Ok(Some(lock.normalized()))
}

pub fn write(path: &Path, lock: &LockFile) -> Result<(), String> {
    let normalized = lock.clone().normalized();
    let text = toml::to_string_pretty(&normalized)
        .map_err(|e| format!("failed to encode lockfile '{}': {}", path.display(), e))?;
    std::fs::write(path, text)
        .map_err(|e| format!("failed to write lockfile '{}': {}", path.display(), e))
}

pub fn equivalent(a: &LockFile, b: &LockFile) -> bool {
    a.clone().normalized() == b.clone().normalized()
}

pub fn node_from_resolved(package: &ResolvedPackage) -> Result<String, String> {
    match &package.source {
        ResolvedSource::Path { abs } => Ok(node_from_path(&package.package.0, abs)),
        ResolvedSource::Git { url, revision, .. } => {
            let canonical = canonicalize_git_url(url)?;
            Ok(node_from_git(&package.package.0, &canonical, *revision))
        }
    }
}

pub fn node_from_path(name: &str, abs_path: &Path) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"path\0");
    hasher.update(name.as_bytes());
    hasher.update(b"\0");
    hasher.update(abs_path.as_os_str().as_bytes());
    short_hash(&hasher.finalize())
}

pub fn node_from_git(name: &str, canonical_url: &str, revision: git2::Oid) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"git\0");
    hasher.update(name.as_bytes());
    hasher.update(b"\0");
    hasher.update(canonical_url.as_bytes());
    hasher.update(b"\0");
    hasher.update(revision.as_bytes());
    short_hash(&hasher.finalize())
}

pub fn canonical_git_cache_key(package_name: &str, canonical_url: &str) -> String {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"repo\0");
    hasher.update(package_name.as_bytes());
    hasher.update(b"\0");
    hasher.update(canonical_url.as_bytes());
    short_hash(&hasher.finalize())
}

fn short_hash(value: &blake3::Hash) -> String {
    value.to_hex().to_string().chars().take(16).collect()
}

#[cfg(test)]
mod tests {
    use super::{LockFile, LockPackage, LockSourceType, equivalent, write};
    use compiler::compile::config::PackageKind;
    use std::{collections::BTreeMap, path::PathBuf};

    #[test]
    fn lockfile_round_trip_preserves_semantics() {
        let mut file = LockFile::new();
        file.package.push(LockPackage {
            node: "b".into(),
            name: "github.com/example/b".into(),
            kind: PackageKind::Library,
            no_std_prelude: false,
            source_type: LockSourceType::Git,
            url: Some("https://github.com/example/b.git".into()),
            path: None,
            requested: "tag:v1.0.0".into(),
            revision: Some("0123456789abcdef0123456789abcdef01234567".into()),
            tree_hash: Some("blake3:abc".into()),
            deps: BTreeMap::new(),
        });
        file.package.push(LockPackage {
            node: "a".into(),
            name: "github.com/example/a".into(),
            kind: PackageKind::Library,
            no_std_prelude: false,
            source_type: LockSourceType::Path,
            url: None,
            path: Some("/tmp/a".into()),
            requested: "path".into(),
            revision: None,
            tree_hash: None,
            deps: [("b".to_string(), "b".to_string())].into_iter().collect(),
        });

        let path = std::env::temp_dir().join(format!(
            "taro-lockfile-test-{}-{}.toml",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));

        write(&path, &file).expect("write");
        let loaded = super::load(&path).expect("load").expect("exists");
        assert!(equivalent(&file, &loaded));

        std::fs::remove_file(PathBuf::from(path)).expect("cleanup");
    }
}
