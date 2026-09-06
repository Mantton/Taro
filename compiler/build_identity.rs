use std::{
    fs, io,
    path::{Path, PathBuf},
};

pub struct BuildIdentity {
    pub stamp: String,
    pub watched_paths: Vec<PathBuf>,
}

/// Identify compiler behavior by build inputs, independently of checkout location
/// and Rust debug/release profiles. Compute this once at build time, not at startup.
pub fn compute(manifest_dir: &Path, settings: &[(String, String)]) -> io::Result<BuildIdentity> {
    let mut inputs = Vec::new();
    let mut watched_paths = Vec::new();
    for name in [
        "Cargo.toml",
        "build.rs",
        "build_identity.rs",
        "src",
        "native",
    ] {
        let path = manifest_dir.join(name);
        collect_files(&path, &format!("compiler/{name}"), &mut inputs)?;
        watched_paths.push(path);
    }

    // These inputs exist in a workspace checkout, but may be absent in a
    // packaged compiler crate. Never watch absent paths: Cargo treats them as dirty.
    let workspace = manifest_dir
        .parent()
        .ok_or_else(|| io::Error::other("compiler has no parent directory"))?;
    for name in [
        "Cargo.toml",
        "Cargo.lock",
        "rust-toolchain.toml",
        "compiler-cli/Cargo.toml",
        "compiler-cli/build.rs",
        "compiler-cli/src",
        "taro-bin/Cargo.toml",
        "taro-bin/build.rs",
        "taro-bin/src",
    ] {
        let path = workspace.join(name);
        if path.try_exists()? {
            collect_files(&path, name, &mut inputs)?;
            watched_paths.push(path);
        }
    }

    inputs.sort_by(|a, b| a.0.cmp(&b.0));
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"taro-compiler-build-v1");
    for (name, path) in inputs {
        frame(&mut hasher, b"file");
        frame(&mut hasher, name.as_bytes());
        frame(&mut hasher, &fs::read(path)?);
    }
    let mut settings: Vec<_> = settings.iter().collect();
    settings.sort();
    for (name, value) in settings {
        frame(&mut hasher, b"setting");
        frame(&mut hasher, name.as_bytes());
        frame(&mut hasher, value.as_bytes());
    }
    Ok(BuildIdentity {
        stamp: format!("build-v1:{}", hasher.finalize().to_hex()),
        watched_paths,
    })
}

fn frame(hasher: &mut blake3::Hasher, bytes: &[u8]) {
    hasher.update(&(bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
}

fn collect_files(path: &Path, name: &str, inputs: &mut Vec<(String, PathBuf)>) -> io::Result<()> {
    if fs::metadata(path)?.is_dir() {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let filename = entry
                .file_name()
                .into_string()
                .map_err(|_| io::Error::other("compiler input path is not UTF-8"))?;
            collect_files(&entry.path(), &format!("{name}/{filename}"), inputs)?;
        }
    } else {
        inputs.push((name.to_owned(), path.to_owned()));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    struct Fixture(PathBuf);
    impl Fixture {
        fn new() -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let root = std::env::temp_dir().join(format!(
                "taro-build-identity-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let fixture = Self(root);
            for path in [
                "compiler/Cargo.toml",
                "compiler/build.rs",
                "compiler/build_identity.rs",
                "compiler/src/lib.rs",
                "compiler/native/shim.cpp",
                "Cargo.toml",
                "Cargo.lock",
                "rust-toolchain.toml",
                "compiler-cli/Cargo.toml",
                "compiler-cli/src/lib.rs",
                "taro-bin/Cargo.toml",
                "taro-bin/src/main.rs",
            ] {
                fixture.write(path, path);
            }
            fixture
        }
        fn write(&self, path: &str, contents: &str) {
            let path = self.0.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, contents).unwrap();
        }
        fn identity(&self) -> BuildIdentity {
            compute(&self.0.join("compiler"), &[]).unwrap()
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn source_native_driver_and_dependency_changes_invalidate_identity() {
        let fixture = Fixture::new();
        let original = fixture.identity().stamp;
        for path in [
            "compiler/src/lib.rs",
            "compiler/native/shim.cpp",
            "compiler/build.rs",
            "compiler/build_identity.rs",
            "compiler/Cargo.toml",
            "Cargo.toml",
            "Cargo.lock",
            "rust-toolchain.toml",
            "compiler-cli/src/lib.rs",
            "taro-bin/src/main.rs",
        ] {
            fixture.write(path, "changed");
            assert_ne!(fixture.identity().stamp, original, "{path}");
            fixture.write(path, path);
            assert_eq!(fixture.identity().stamp, original);
        }
    }

    #[test]
    fn added_removed_and_renamed_sources_change_identity() {
        let fixture = Fixture::new();
        let original = fixture.identity().stamp;
        fixture.write("compiler/src/nested/new.rs", "new");
        let added = fixture.identity().stamp;
        assert_ne!(added, original);
        fs::rename(
            fixture.0.join("compiler/src/nested/new.rs"),
            fixture.0.join("compiler/src/nested/renamed.rs"),
        )
        .unwrap();
        assert_ne!(fixture.identity().stamp, added);
        fs::remove_file(fixture.0.join("compiler/src/nested/renamed.rs")).unwrap();
        assert_eq!(fixture.identity().stamp, original);
        assert!(
            fixture
                .identity()
                .watched_paths
                .contains(&fixture.0.join("compiler/src"))
        );
    }

    #[test]
    fn relocation_timestamps_and_unrelated_files_preserve_identity() {
        let first = Fixture::new();
        let second = Fixture::new();
        let original = first.identity().stamp;
        assert_eq!(second.identity().stamp, original);
        // Rewriting identical bytes updates filesystem metadata only.
        first.write("compiler/src/lib.rs", "compiler/src/lib.rs");
        first.write("README.md", "documentation");
        first.write("target/debug/compiler", "build output");
        assert_eq!(first.identity().stamp, original);
    }

    #[test]
    fn settings_are_order_independent_and_framed() {
        let fixture = Fixture::new();
        let identity = |values: &[(&str, &str)]| {
            compute(
                &fixture.0.join("compiler"),
                &values
                    .iter()
                    .map(|(key, value)| (key.to_string(), value.to_string()))
                    .collect::<Vec<_>>(),
            )
            .unwrap()
            .stamp
        };
        assert_eq!(
            identity(&[("target", "a"), ("rustc", "b")]),
            identity(&[("rustc", "b"), ("target", "a")])
        );
        for key in ["rustc", "llvm", "target", "CARGO_FEATURE_NIGHTLY"] {
            assert_ne!(identity(&[(key, "old")]), identity(&[(key, "new")]));
        }
        assert_ne!(identity(&[("ab", "c")]), identity(&[("a", "bc")]));
    }
}
