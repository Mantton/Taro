//! The source and target descriptors distributed with the language server.

use std::{
    collections::BTreeMap,
    fs::{self, File},
    io::{self, Read},
    path::{Path, PathBuf},
};

use compiler::{
    compile::{
        frozen_dependencies::{FrozenDependency, SEMANTIC_BUILD_ID},
        target_facts::TargetFacts,
    },
    constants::{MANIFEST_FILE, SOURCE_DIRECTORY},
};
use serde::{Deserialize, Serialize};

use crate::standard_library::{MAX_FROZEN_STD_BYTES, freeze, std_config};

const SCHEMA: u32 = 2;
const BUNDLE_FILE: &str = "bundle.toml";
const STD_PATH: &str = "std";
const TARGETS_PATH: &str = "targets";

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Manifest {
    schema: u32,
    frontend: String,
    std_digest: String,
    default_target: String,
    targets: BTreeMap<String, BundledTarget>,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct BundledTarget {
    descriptor: String,
    std_snapshot: String,
}

pub struct Bundle {
    root: PathBuf,
    manifest: Manifest,
}

impl Bundle {
    pub fn load(path: &Path) -> io::Result<Self> {
        let root = path.canonicalize()?;
        let manifest: Manifest = toml::from_str(&fs::read_to_string(root.join(BUNDLE_FILE))?)
            .map_err(io::Error::other)?;
        if manifest.schema != SCHEMA || manifest.frontend != SEMANTIC_BUILD_ID {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "language server bundle does not match this frontend",
            ));
        }
        let installed = Self { root, manifest };
        installed.target(None)?;
        Ok(installed)
    }

    pub fn target(&self, triple: Option<&str>) -> io::Result<TargetFacts> {
        let triple = triple.unwrap_or(&self.manifest.default_target);
        let expected = self.manifest.targets.get(triple).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                format!("no analysis descriptor for target '{triple}'"),
            )
        })?;
        let descriptor = self.target_path(triple, "toml")?;
        let text = fs::read_to_string(descriptor)?;
        if blake3::hash(text.as_bytes()).to_hex().as_str() != expected.descriptor {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "analysis target descriptor has changed",
            ));
        }
        let target: TargetFacts = toml::from_str(&text).map_err(io::Error::other)?;
        if target.triple() != triple {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "analysis descriptor has the wrong target",
            ));
        }
        Ok(target)
    }

    pub fn std_digest(&self) -> &str {
        &self.manifest.std_digest
    }

    pub fn verify_std_sources(&self) -> io::Result<PathBuf> {
        let root = std_path(&self.root);
        if std_digest(&root)?.as_str() != self.std_digest() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "installed standard-library sources do not match the bundle",
            ));
        }
        Ok(root)
    }

    pub(crate) fn frozen_std(&self, target: &TargetFacts) -> io::Result<FrozenDependency> {
        let triple = target.triple();
        let expected = self.manifest.targets.get(triple).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::NotFound,
                "target has no bundled std snapshot",
            )
        })?;
        let path = self.target_path(triple, "std")?;
        let max_file_size = MAX_FROZEN_STD_BYTES + 32;
        let mut bytes = Vec::new();
        File::open(path)?
            .take((max_file_size + 1) as u64)
            .read_to_end(&mut bytes)?;
        if bytes.len() > max_file_size
            || blake3::hash(&bytes).to_hex().as_str() != expected.std_snapshot
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "bad standard-library snapshot",
            ));
        }
        FrozenDependency::from_relocatable_bytes(bytes)
    }

    fn target_path(&self, triple: &str, extension: &str) -> io::Result<PathBuf> {
        Ok(self
            .root
            .join(TARGETS_PATH)
            .join(target_file_name(triple, extension)?))
    }
}

pub(crate) fn std_path(bundle_root: &Path) -> PathBuf {
    bundle_root.join(STD_PATH)
}

/// Create a fresh bundle with browseable sources and prechecked std metadata
/// for each descriptor produced by the native target tool.
pub fn create(output: &Path, std_source: &Path, descriptors: &[PathBuf]) -> io::Result<()> {
    let mut targets = BTreeMap::new();
    let mut files = BTreeMap::new();
    let mut default_target = None;
    for path in descriptors {
        let source = fs::read_to_string(path)?;
        let target: TargetFacts = toml::from_str(&source).map_err(io::Error::other)?;
        let triple = target.triple().to_owned();
        target_file_name(&triple, "toml")?;
        default_target.get_or_insert_with(|| triple.clone());
        if files.insert(triple, (target, source)).is_some() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "duplicate bundled target",
            ));
        }
    }
    let default_target = default_target.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "include at least one target descriptor",
        )
    })?;
    let std_hash = std_digest(std_source)?;

    fs::create_dir(output)?;
    // A failed assembly stays unpublished. The manifest is always written
    // last, after all source and descriptor files have arrived.
    let lib = std_path(output);
    fs::create_dir(&lib)?;
    fs::copy(std_source.join(MANIFEST_FILE), lib.join(MANIFEST_FILE))?;
    copy_tree(
        &std_source.join(SOURCE_DIRECTORY),
        &lib.join(SOURCE_DIRECTORY),
    )?;
    let targets_root = output.join(TARGETS_PATH);
    fs::create_dir(&targets_root)?;
    let config = std_config(lib.canonicalize()?);
    for (triple, (target, text)) in files {
        let descriptor = blake3::hash(text.as_bytes()).to_hex().to_string();
        let snapshot = freeze(&config, &target, || false)?;
        let mut bytes = Vec::new();
        snapshot.write_relocatable(&mut bytes)?;
        let std_snapshot = blake3::hash(&bytes).to_hex().to_string();
        fs::write(targets_root.join(target_file_name(&triple, "toml")?), text)?;
        fs::write(targets_root.join(target_file_name(&triple, "std")?), bytes)?;
        targets.insert(
            triple,
            BundledTarget {
                descriptor,
                std_snapshot,
            },
        );
    }
    if std_digest(&lib)? != std_hash {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "standard-library sources changed during packaging",
        ));
    }
    let manifest = Manifest {
        schema: SCHEMA,
        frontend: SEMANTIC_BUILD_ID.to_owned(),
        std_digest: std_hash,
        default_target,
        targets,
    };
    let text = toml::to_string(&manifest).map_err(io::Error::other)?;
    fs::write(output.join(BUNDLE_FILE), text)
}

fn target_file_name(triple: &str, extension: &str) -> io::Result<String> {
    if triple.is_empty()
        || !triple
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "invalid bundled target name",
        ));
    }
    Ok(format!("{triple}.{extension}"))
}

pub(crate) fn std_digest(root: &Path) -> io::Result<String> {
    fn digest(root: &Path, path: &Path, hasher: &mut blake3::Hasher) -> io::Result<()> {
        let relative = path.strip_prefix(root).expect("path under bundle root");
        let name = relative.as_os_str().as_encoded_bytes();
        hasher.update(&(name.len() as u64).to_le_bytes());
        hasher.update(name);
        let metadata = fs::symlink_metadata(path)?;
        if metadata.is_dir() {
            hasher.update(b"directory");
            for child in children(path)? {
                digest(root, &child, hasher)?;
            }
        } else if metadata.is_file() {
            hasher.update(b"file");
            hasher.update(&metadata.len().to_le_bytes());
            if io::copy(&mut File::open(path)?, hasher)? != metadata.len() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "standard-library input changed",
                ));
            }
        } else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "expected regular standard-library sources",
            ));
        }
        Ok(())
    }
    let mut hash = blake3::Hasher::new();
    hash.update(b"taro-lsp-std-v1");
    digest(root, &root.join(MANIFEST_FILE), &mut hash)?;
    digest(root, &root.join(SOURCE_DIRECTORY), &mut hash)?;
    Ok(hash.finalize().to_hex().to_string())
}

fn children(path: &Path) -> io::Result<Vec<PathBuf>> {
    let mut entries = fs::read_dir(path)?
        .map(|entry| entry.map(|entry| entry.path()))
        .collect::<io::Result<Vec<_>>>()?;
    entries.sort_unstable();
    Ok(entries)
}

fn copy_tree(source: &Path, destination: &Path) -> io::Result<()> {
    let metadata = fs::symlink_metadata(source)?;
    if metadata.is_dir() {
        fs::create_dir(destination)?;
        for child in children(source)? {
            copy_tree(
                &child,
                &destination.join(child.file_name().expect("directory entry name")),
            )?;
        }
    } else if metadata.is_file() {
        fs::copy(source, destination)?;
    } else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "expected regular standard-library sources",
        ));
    }
    Ok(())
}
