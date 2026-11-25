use super::{config::Config, context::Gcx, source::SourceProvider};
use crate::{hir::Literal, span::FileID};
use std::{
    collections::BTreeMap,
    io,
    path::{Path, PathBuf},
};

/// Sorted logical paths (including symlink components) and the content digests
/// of the files actually embedded in this package.
pub(crate) type AssetInputs = BTreeMap<PathBuf, [u8; 32]>;

fn source_root(config: &Config, sources: &dyn SourceProvider) -> io::Result<PathBuf> {
    let mut root = sources.resolve(&config.src)?;
    if config.is_script {
        root.pop();
    }
    Ok(root)
}

fn is_relative_asset(path: &Path) -> bool {
    !path.as_os_str().is_empty()
        && !matches!(
            path.components().next(),
            Some(std::path::Component::Prefix(_) | std::path::Component::RootDir)
        )
}

impl Gcx<'_> {
    /// Resolve relative to the source containing the directive. Fingerprint
    /// the exact bytes used to produce the literal, including for text files.
    pub(crate) fn read_embedded(
        self,
        file: FileID,
        name: &str,
        bytes: bool,
    ) -> Result<Literal, String> {
        let path = Path::new(name);
        if name.contains('\0') {
            return Err("embedded asset path contains a NUL byte".into());
        }
        if !is_relative_asset(path) {
            return Err("embedded asset path must be a nonempty relative path".into());
        }
        let sources = self.dcx.sources();
        let root = source_root(self.config, sources)
            .map_err(|e| format!("could not resolve embedded asset source: {e}"))?;
        let source = self
            .dcx
            .file_path(file)
            .ok_or("embedded asset has no source file")?;
        let dir = source
            .parent()
            .and_then(|dir| dir.strip_prefix(&root).ok())
            .ok_or("embedded asset source is outside the package")?;
        let relative = dir.join(path);
        let failed = |error: io::Error| match error.kind() {
            io::ErrorKind::NotFound => format!("embedded asset '{name}' does not exist"),
            io::ErrorKind::InvalidInput => format!("embedded asset '{name}' is not a regular file"),
            _ => format!("could not read embedded asset '{name}': {error}"),
        };
        let data = sources.read_file(&root.join(&relative)).map_err(failed)?;
        let data = data.as_bytes();
        let literal = if bytes {
            Literal::Bytes(self.interner().intern_bytes(data))
        } else {
            let text = std::str::from_utf8(data)
                .map_err(|_| format!("embedded asset '{name}' is not valid UTF-8"))?;
            Literal::String(self.intern_symbol(text))
        };
        let hash = *blake3::hash(data).as_bytes();
        let mut packages = self.store.embedded_inputs.borrow_mut();
        if let Some(previous) = packages
            .entry(self.package_index())
            .or_default()
            .insert(relative, hash)
            && previous != hash
        {
            return Err(format!(
                "embedded asset '{name}' changed during compilation"
            ));
        }
        Ok(literal)
    }

    /// Callers must rebuild when an imported asset changes, even when every
    /// source file and the importer's own assets stay unchanged.
    pub fn fingerprint_with_embedded_inputs(self, source_fingerprint: String) -> String {
        let packages = self.store.embedded_inputs.borrow();
        let Some(inputs) = packages
            .get(&self.package_index())
            .filter(|inputs| !inputs.is_empty())
        else {
            return source_fingerprint;
        };
        let mut digest = blake3::Hasher::new();
        digest.update(b"taro.embedded-inputs.v1");
        digest.update(source_fingerprint.as_bytes());
        for (path, hash) in inputs {
            let key = path.as_os_str().as_encoded_bytes();
            digest.update(&(key.len() as u64).to_le_bytes());
            digest.update(key);
            digest.update(hash);
        }
        digest.finalize().to_hex().to_string()
    }
}

/// Attached SDKs are self-contained. Recheck external files only for normal
/// incremental cache hits, when the source package is present.
pub(crate) fn validate_inputs(
    config: &Config,
    sources: &dyn SourceProvider,
    inputs: &AssetInputs,
) -> Result<(), String> {
    if inputs.is_empty() {
        return Ok(());
    }
    let root = source_root(config, sources).map_err(|e| e.to_string())?;
    for (path, expected) in inputs {
        if !is_relative_asset(path) {
            return Err("invalid cached embedded asset path".into());
        }
        let changed = || format!("embedded asset '{}' changed", path.display());
        let digest = sources
            .digest_file(&root.join(path))
            .map_err(|_| changed())?;
        if digest.as_bytes() != expected {
            return Err(changed());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{TempDir, with_test_gcx_config};
    use std::fs;

    #[test]
    fn validate_cached_asset_contents_and_dependency_fingerprint() {
        let dir = TempDir::new("embedded-assets");
        let source = dir.join("script.tr");
        let asset = dir.join("data.bin");
        fs::write(&source, "").unwrap();
        fs::write(&asset, [0, 255]).unwrap();
        with_test_gcx_config(
            |config| config.src = source.clone(),
            |gcx| {
                let file = gcx.dcx.add_file_mapping(source.canonicalize().unwrap());
                assert_eq!(
                    gcx.fingerprint_with_embedded_inputs("original".into()),
                    "original"
                );
                gcx.read_embedded(file, "data.bin", true).unwrap();
                let inputs = gcx.store.embedded_inputs.borrow()[&gcx.package_index()].clone();
                let before = gcx.fingerprint_with_embedded_inputs("original".into());
                validate_inputs(gcx.config, gcx.dcx.sources(), &inputs).unwrap();
                fs::write(&asset, [1, 255]).unwrap();
                assert!(validate_inputs(gcx.config, gcx.dcx.sources(), &inputs).is_err());
                gcx.store.embedded_inputs.borrow_mut().clear();
                gcx.read_embedded(file, "data.bin", true).unwrap();
                assert_ne!(
                    gcx.fingerprint_with_embedded_inputs("original".into()),
                    before
                );
                fs::remove_file(&asset).unwrap();
                assert!(validate_inputs(gcx.config, gcx.dcx.sources(), &inputs).is_err());
                fs::write(&asset, [0, 255]).unwrap();
                validate_inputs(gcx.config, gcx.dcx.sources(), &inputs).unwrap();
            },
        );
    }
}
