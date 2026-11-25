//! Find the same sources and target descriptors used by the installed SDK.

use std::{
    env,
    fs::{self, File, OpenOptions},
    io::{self, Read, Write},
    path::{Path, PathBuf},
};

use compiler::{
    compile::{
        frozen_dependencies::{FrozenDependency, SEMANTIC_BUILD_ID},
        target_facts::TargetFacts,
    },
    constants::{LANGUAGE_HOME, STD_PREFIX},
    package::utils::{infer_language_home_from_executable, language_home},
};

use crate::standard_library::MAX_FROZEN_STD_BYTES;

const TARGET_FACTS: &str = "target-facts.toml";
const SNAPSHOT_FILE: &str = "std.snapshot";
const HASH_BYTES: usize = 32;

pub fn discover() -> io::Result<PathBuf> {
    if env::var_os(LANGUAGE_HOME).is_some() {
        return language_home().map_err(io::Error::other);
    }
    if let Ok(home) = language_home() {
        return Ok(home);
    }
    let name = format!("taro{}", env::consts::EXE_SUFFIX);
    for directory in env::split_paths(&env::var_os("PATH").unwrap_or_default()) {
        let Ok(executable) = directory.join(&name).canonicalize() else {
            continue;
        };
        let Ok(metadata) = executable.metadata() else {
            continue;
        };
        if !metadata.is_file() {
            continue;
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if metadata.permissions().mode() & 0o111 == 0 {
                continue;
            }
        }
        // The first runnable taro on PATH selects the toolchain.
        return infer_language_home_from_executable(&executable).ok_or_else(missing_sdk);
    }
    Err(missing_sdk())
}

fn missing_sdk() -> io::Error {
    io::Error::new(
        io::ErrorKind::NotFound,
        "Taro SDK not found. Set TARO_HOME, pass --sdk <directory>, or pass --bundle for a portable install",
    )
}

pub fn std_root(home: &Path) -> io::Result<PathBuf> {
    let source = home.join(STD_PREFIX);
    source.canonicalize().map_err(|error| {
        io::Error::new(
            error.kind(),
            format!(
                "cannot locate SDK std sources at {}: {error}",
                source.display()
            ),
        )
    })
}

pub struct Sdk {
    pub std: PathBuf,
    runtime: PathBuf,
    cache: Option<PathBuf>,
}

impl Sdk {
    pub fn load(home: &Path) -> io::Result<Self> {
        Ok(Self {
            std: std_root(home)?,
            runtime: home.join("lib/taro/runtime"),
            cache: cache_directory(),
        })
    }

    pub fn target(&self, requested: Option<&str>) -> io::Result<TargetFacts> {
        let host = self.runtime.join(TARGET_FACTS);
        if let Some(triple) = requested {
            if matches!(triple, "" | "." | "..")
                || !triple
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'-' | b'_' | b'.'))
            {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "invalid SDK target name",
                ));
            }
            let descriptor = self.runtime.join(triple).join(TARGET_FACTS);
            let facts = match read_target(&descriptor) {
                Ok(facts) => Some(facts),
                Err(error) if error.kind() == io::ErrorKind::NotFound => match read_target(&host) {
                    Ok(facts) => Some(facts),
                    Err(error) if error.kind() == io::ErrorKind::NotFound => None,
                    Err(error) => return Err(error),
                },
                Err(error) => return Err(error),
            };
            return facts
                .filter(|facts| facts.triple() == triple)
                .ok_or_else(|| {
                    io::Error::new(
                        io::ErrorKind::NotFound,
                        format!("SDK has no matching descriptor for target '{triple}'"),
                    )
                });
        }
        if host.try_exists()? {
            return read_target(&host);
        }
        let mut descriptors = Vec::new();
        for entry in fs::read_dir(&self.runtime)? {
            let entry = entry?;
            if entry.file_type()?.is_dir() && entry.path().join(TARGET_FACTS).try_exists()? {
                descriptors.push(entry.path().join(TARGET_FACTS));
            }
        }
        match descriptors.as_slice() {
            [descriptor] => read_target(descriptor),
            [] => Err(io::Error::new(
                io::ErrorKind::NotFound,
                format!("SDK has no target facts under {}", self.runtime.display()),
            )),
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "SDK has multiple targets. Set [language_server].target in package.toml",
            )),
        }
    }
}

fn read_target(path: &Path) -> io::Result<TargetFacts> {
    let text = fs::read_to_string(path)
        .map_err(|error| io::Error::new(error.kind(), format!("{}: {error}", path.display())))?;
    toml::from_str(&text).map_err(|error| io::Error::other(format!("{}: {error}", path.display())))
}

fn snapshot_key(digest: &str, target: &TargetFacts) -> blake3::Hash {
    let mut key = blake3::Hasher::new();
    key.update(b"taro-lsp-sdk-std-cache-v1");
    for input in [SEMANTIC_BUILD_ID, digest, target.triple()] {
        key.update(&(input.len() as u64).to_le_bytes());
        key.update(input.as_bytes());
    }
    key.update(&target.pointer_bits().to_le_bytes());
    key.finalize()
}

impl Sdk {
    pub fn cached_std(&self, digest: &str, target: &TargetFacts) -> Option<FrozenDependency> {
        let path = self.cache.as_ref()?.join(SNAPSHOT_FILE);
        if !path.metadata().ok()?.is_file() {
            return None;
        }
        let mut file = File::open(path).ok()?;
        let mut header = [0; HASH_BYTES * 2];
        file.read_exact(&mut header).ok()?;
        if &header[..HASH_BYTES] != snapshot_key(digest, target).as_bytes() {
            return None;
        }
        let max = MAX_FROZEN_STD_BYTES + HASH_BYTES;
        let mut bytes = Vec::new();
        file.take((max + 1) as u64).read_to_end(&mut bytes).ok()?;
        if bytes.len() > max || blake3::hash(&bytes).as_bytes() != &header[HASH_BYTES..] {
            return None;
        }
        FrozenDependency::from_relocatable_bytes(bytes).ok()
    }

    /// Publish one persistent slot. A stable, locked staging file bounds
    /// abandoned writes after a worker crash and prevents concurrent writers
    /// from truncating one another. Readers see only complete snapshots.
    pub fn store_std(
        &self,
        digest: &str,
        target: &TargetFacts,
        snapshot: &FrozenDependency,
    ) -> io::Result<()> {
        let Some(directory) = &self.cache else {
            return Ok(());
        };
        fs::create_dir_all(directory)?;
        let lock = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(false)
            .open(directory.join("std.lock"))?;
        if lock.try_lock().is_err() {
            return Ok(());
        }
        let mut bytes = Vec::with_capacity(snapshot.retained_bytes() + HASH_BYTES);
        snapshot.write_relocatable(&mut bytes)?;
        let staging = directory.join("std.snapshot.tmp");
        match fs::remove_file(&staging) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
        let result = (|| {
            let mut file = File::create_new(&staging)?;
            file.write_all(snapshot_key(digest, target).as_bytes())?;
            file.write_all(blake3::hash(&bytes).as_bytes())?;
            file.write_all(&bytes)?;
            file.sync_all()?;
            drop(file);
            fs::rename(&staging, directory.join(SNAPSHOT_FILE))
        })();
        if result.is_err() {
            let _ = fs::remove_file(staging);
        }
        result
    }
}

fn cache_directory() -> Option<PathBuf> {
    if let Some(path) = env::var_os("TARO_LSP_CACHE_DIR") {
        return (!path.is_empty()).then(|| PathBuf::from(path));
    }
    if let Some(path) = env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .filter(|path| path.is_absolute())
    {
        return Some(path.join("taro-lsp"));
    }
    let (variable, relative) = match env::consts::OS {
        "macos" => ("HOME", "Library/Caches/taro-lsp"),
        "windows" => ("LOCALAPPDATA", "taro-lsp/cache"),
        _ => ("HOME", ".cache/taro-lsp"),
    };
    env::var_os(variable)
        .map(PathBuf::from)
        .filter(|path| path.is_absolute())
        .map(|path| path.join(relative))
}
