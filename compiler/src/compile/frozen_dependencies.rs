//! Immutable dependency data that can be reused by independent checks.

use std::io;

use crate::metadata::{self, LoadedMetadata, ReuseMode};

use super::{Compiler, context::Gcx};

/// An in-memory semantic dependency in the compiler's metadata representation.
///
/// The snapshot contains only owned bytes. A check materializes a fresh copy
/// in its scratch interner and arenas using the same decoder as `taro check`.
/// Callers bind the snapshot to the dependency inputs for their workspace
/// revision and hydrate dependencies in topological order.
pub struct FrozenDependency {
    configuration: blake3::Hash,
    payload: Box<[u8]>,
}

impl Compiler<'_> {
    /// Check a dependency and freeze its semantic data, including the MIR
    /// needed to evaluate calls to imported constant functions.
    pub fn freeze_dependency(&mut self) -> io::Result<FrozenDependency> {
        self.check()
            .map_err(|_| io::Error::other("dependency check failed"))?;
        let configuration = configuration_key(self.context)?;
        let payload = metadata::build_payload_wire(self.context, ReuseMode::SemanticDependency)?;
        let payload = bincode::serialize(&payload).map_err(io::Error::other)?;
        Ok(FrozenDependency {
            configuration,
            payload: payload.into_boxed_slice(),
        })
    }
}

impl FrozenDependency {
    /// Heap bytes retained for this snapshot's payload.
    pub fn retained_bytes(&self) -> usize {
        self.payload.len()
    }

    /// Load this dependency into the context for its package in a fresh check.
    pub fn hydrate(&self, gcx: Gcx<'_>) -> io::Result<()> {
        if self.configuration != configuration_key(gcx)? {
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
        metadata::hydrate_loaded_metadata(gcx, &loaded, ReuseMode::SemanticDependency)
            .map_err(io::Error::other)
    }
}

fn configuration_key(gcx: Gcx<'_>) -> io::Result<blake3::Hash> {
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
        config.src.as_os_str().as_encoded_bytes(),
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
