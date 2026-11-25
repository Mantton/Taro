//! Immutable dependency data that can be reused by independent checks.

use std::{
    io::{self, Write},
    path::{Component, Path},
};

use crate::metadata::{
    self, LoadedMetadata, ReuseMode,
    wire::{FilePathWire, MetadataPayloadWire},
};

use super::{Compiler, context::Gcx};

/// Build identity for language-server bundles and semantic products.
pub const SEMANTIC_BUILD_ID: &str = env!("TARO_COMPILER_ID");

/// An in-memory semantic dependency in the compiler's metadata representation.
///
/// The snapshot contains only owned bytes. A check materializes a fresh copy
/// in its scratch interner and arenas using the same decoder as `taro check`.
/// Callers bind the snapshot to the dependency inputs for their workspace
/// revision and hydrate dependencies in topological order.
pub struct FrozenDependency {
    relocatable: bool,
    configuration: blake3::Hash,
    fingerprint: blake3::Hash,
    payload: Box<[u8]>,
}

impl Compiler<'_> {
    /// Check a dependency and freeze its semantic data, including the MIR
    /// needed to evaluate calls to imported constant functions.
    pub fn freeze_dependency(&mut self) -> io::Result<FrozenDependency> {
        self.freeze_dependency_with_paths(false)
    }

    /// Freeze a standalone source library for a trusted, matching frontend
    /// installation. The caller must bind the file to the exact source tree
    /// and target descriptor before hydrating it.
    pub fn freeze_relocatable_dependency(&mut self) -> io::Result<FrozenDependency> {
        let config = self.context.config;
        if config.is_script || !config.dependencies.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "relocatable snapshots require a standalone source package",
            ));
        }
        self.freeze_dependency_with_paths(true)
    }

    fn freeze_dependency_with_paths(&mut self, relocatable: bool) -> io::Result<FrozenDependency> {
        self.check()
            .map_err(|_| io::Error::other("dependency check failed"))?;
        let configuration = configuration_key(self.context, relocatable)?;
        let payload = metadata::build_payload_wire(self.context, ReuseMode::SemanticDependency)?;
        if relocatable {
            validate_relocatable_paths(&payload)?;
        }
        let payload = bincode::serialize(&payload).map_err(io::Error::other)?;
        Ok(FrozenDependency::new(
            relocatable,
            configuration,
            payload.into_boxed_slice(),
        ))
    }
}

impl FrozenDependency {
    fn new(relocatable: bool, configuration: blake3::Hash, payload: Box<[u8]>) -> Self {
        let mut fingerprint = blake3::Hasher::new();
        fingerprint.update(configuration.as_bytes());
        fingerprint.update(&payload);
        Self {
            relocatable,
            configuration,
            fingerprint: fingerprint.finalize(),
            payload,
        }
    }

    /// Write a relocatable snapshot for this exact semantic frontend build.
    pub fn write_relocatable(&self, mut output: impl Write) -> io::Result<()> {
        if !self.relocatable {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "snapshot is tied to its original source path",
            ));
        }
        output.write_all(self.configuration.as_bytes())?;
        output.write_all(&self.payload)
    }

    /// Load bytes verified by a trusted same-build bundle manifest.
    pub fn from_relocatable_bytes(mut bytes: Vec<u8>) -> io::Result<Self> {
        let (header, _) = bytes
            .split_at_checked(32)
            .filter(|(_, payload)| !payload.is_empty())
            .ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, "truncated dependency snapshot")
            })?;
        let configuration = blake3::Hash::from_bytes(header.try_into().unwrap());
        bytes.drain(..32);
        Ok(Self::new(true, configuration, bytes.into_boxed_slice()))
    }

    /// Heap bytes retained for this snapshot's payload.
    pub fn retained_bytes(&self) -> usize {
        self.payload.len()
    }

    /// Load this dependency into the context for its package in a fresh check.
    pub fn hydrate(&self, gcx: Gcx<'_>) -> io::Result<()> {
        if self.configuration != configuration_key(gcx, self.relocatable)? {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "frozen dependency configuration mismatch",
            ));
        }
        if gcx.try_resolution_output(gcx.package_index()).is_some() {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "a package with this index is already loaded",
            ));
        }
        let loaded = LoadedMetadata {
            package_identifier: gcx.config.identifier.to_string(),
            package_index: gcx.package_index(),
            artifact: None,
            payload: bincode::deserialize(&self.payload).map_err(io::Error::other)?,
        };
        if self.relocatable {
            gcx.dcx().sources().resolve(&gcx.config.src)?;
            validate_relocatable_paths(&loaded.payload)?;
        }
        super::assets::validate_inputs(
            gcx.config,
            gcx.dcx().sources(),
            &loaded.payload.embedded_inputs,
        )
        .map_err(io::Error::other)?;
        metadata::hydrate_loaded_metadata(gcx, &loaded, ReuseMode::SemanticDependency)
            .map_err(io::Error::other)?;
        gcx.store
            .frozen_dependency_keys
            .borrow_mut()
            .insert(gcx.package_index(), self.fingerprint);
        Ok(())
    }
}

fn package_relative(path: &Path) -> bool {
    !path.as_os_str().is_empty()
        && path
            .components()
            .all(|part| matches!(part, Component::Normal(_)))
}

fn validate_relocatable_paths(payload: &MetadataPayloadWire) -> io::Result<()> {
    if payload.file_table.iter().all(|entry| {
        matches!(&entry.path, FilePathWire::PackageRelative(path) if package_relative(Path::new(path)))
    }) && payload.embedded_inputs.keys().all(|path| package_relative(path))
    {
        return Ok(());
    }
    Err(io::Error::new(
        io::ErrorKind::InvalidData,
        "snapshot path is outside the package",
    ))
}

fn configuration_key(gcx: Gcx<'_>, relocatable: bool) -> io::Result<blake3::Hash> {
    let config = gcx.config;
    let mut dependencies = config
        .dependencies
        .iter()
        .map(|(alias, package)| (alias.as_str(), package.as_str()))
        .collect::<Vec<_>>();
    dependencies.sort_unstable();

    // Metadata references imported packages by numeric index. Replaying a
    // snapshot under different package indices could bind a different type.
    let loaded_packages = gcx.store.package_mapping.borrow();
    let mut package_indices = loaded_packages
        .iter()
        .filter(|(package, _)| *package != &config.identifier)
        .map(|(package, index)| (package.as_str(), index.raw()))
        .collect::<Vec<_>>();
    package_indices.sort_unstable();
    let inputs = (
        &gcx.store.target_facts,
        config.identifier.as_str(),
        (!relocatable).then(|| config.src.as_os_str().as_encoded_bytes()),
        config.index.raw(),
        dependencies,
        package_indices,
        config.kind,
        config.profile,
        config.std_mode,
        config.harness_mode as u8,
        (
            config.is_script,
            config.is_std_provider,
            config.overflow_checks,
            config.no_std_prelude,
            config.lint_warnings,
        ),
    );
    let encoded = bincode::serialize(&inputs).map_err(io::Error::other)?;
    Ok(blake3::hash(&encoded))
}

#[cfg(test)]
mod tests {
    use super::{Compiler, Gcx};
    use crate::{
        PackageIndex,
        compile::config::{BuildProfile, HarnessMode},
        test_support::with_source_compiler,
    };
    use std::{io, rc::Rc};

    #[test]
    fn reuses_const_function_metadata_after_the_producer_drops() {
        let (snapshot, dependency, producer) = with_source_compiler(
            &[("lib.tr", "public const func width() -> usize { 3 }")],
            false,
            HarnessMode::None,
            |compiler| {
                let gcx = compiler.context;
                let mut config = gcx.config.clone();
                config.identifier = "test/dep".into();
                config.index = PackageIndex::new(2);
                let config = gcx.store.arenas.configs.alloc(config);
                let mut compiler = Compiler::new(*gcx, config);
                let snapshot = compiler.freeze_dependency().unwrap_or_else(|error| {
                    panic!("{error}: {:?}", gcx.dcx().take_recorded_diagnostics())
                });
                (snapshot, config.clone(), Rc::downgrade(&gcx.dcx().symbols))
            },
        );
        assert!(producer.upgrade().is_none());
        assert!(snapshot.retained_bytes() > 0);

        let mut previous = None;
        for revision in [17, 18] {
            let (reply, scratch) = with_source_compiler(
                &[(
                    "app.tr",
                    "import dep::width\n\
                     func data() -> [int32; width()] { [1, 2, 3] }\n\
                     func useWidth() -> usize { width() }",
                )],
                false,
                HarnessMode::None,
                |compiler| {
                    let gcx = compiler.context;
                    let arenas = gcx.store.arenas;
                    let mut incompatible = dependency.clone();
                    incompatible.profile = BuildProfile::Release;
                    let incompatible = arenas.configs.alloc(incompatible);
                    assert_eq!(
                        snapshot
                            .hydrate(Gcx::new(*gcx, incompatible))
                            .unwrap_err()
                            .kind(),
                        io::ErrorKind::InvalidInput,
                    );
                    let dependency_gcx = Gcx::new(*gcx, arenas.configs.alloc(dependency.clone()));
                    snapshot.hydrate(dependency_gcx).unwrap();
                    assert_eq!(
                        snapshot.hydrate(dependency_gcx).unwrap_err().kind(),
                        io::ErrorKind::AlreadyExists,
                    );
                    let mut config = gcx.config.clone();
                    config
                        .dependencies
                        .insert("dep".into(), dependency.identifier.to_string());
                    let mut compiler = Compiler::new(*gcx, arenas.configs.alloc(config));
                    (
                        compiler.analyze_owned(revision),
                        Rc::downgrade(&gcx.dcx().symbols),
                    )
                },
            );
            assert!(scratch.upgrade().is_none());
            assert!(reply.complete, "{:?}", reply.diagnostics);
            let declaration = reply
                .occurrences
                .into_iter()
                .filter_map(|occurrence| occurrence.declaration)
                .find(|declaration| declaration.name == "width")
                .expect("resolved call into the frozen dependency");
            assert_eq!(declaration.package, "test/dep");
            assert!(declaration.source.path.ends_with("src/lib.tr"));
            if let Some(previous) = &previous {
                assert_eq!(&declaration, previous);
            }
            previous = Some(declaration);
        }
    }
}
