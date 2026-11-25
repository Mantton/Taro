//! Prepare matching standard-library metadata in a disposable session.

use std::{io, path::PathBuf, rc::Rc};

use compiler::{
    PackageIndex,
    compile::{
        Compiler,
        config::{Config, PackageKind, StdMode},
        context::{CompilerArenas, CompilerContext, CompilerStore, Gcx},
        frozen_dependencies::FrozenDependency,
        target_facts::TargetFacts,
    },
    diagnostics::DiagCtx,
};

use crate::bundle::Bundle;

pub(crate) const MAX_FROZEN_STD_BYTES: usize = 128 * 1024 * 1024;

#[derive(Default)]
pub struct StdCache {
    prepared: Option<Prepared>,
    verify_sources: bool,
}

pub struct Prepared {
    target: TargetFacts,
    digest: String,
    config: Config,
    snapshot: FrozenDependency,
}

impl StdCache {
    pub fn invalidate_sources(&mut self) {
        self.verify_sources = true;
    }

    pub fn prepare(
        &mut self,
        bundle: &Bundle,
        target: &TargetFacts,
        expected_digest: Option<&str>,
        cancelled: impl Fn() -> bool + 'static,
    ) -> io::Result<&Prepared> {
        let digest = bundle.std_digest();
        if expected_digest.is_some_and(|expected| expected != digest) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "project requests a different standard-library source identity",
            ));
        }
        if !self
            .prepared
            .as_ref()
            .is_some_and(|current| current.target == *target && current.digest == digest)
        {
            self.prepared = None;
            let root = bundle.verify_std_sources()?;
            let config = std_config(root);
            let snapshot = match bundle.frozen_std(target) {
                Ok(snapshot) => snapshot,
                Err(_) => {
                    let snapshot = freeze(&config, target, cancelled)?;
                    bundle.verify_std_sources()?;
                    snapshot
                }
            };
            self.prepared = Some(Prepared {
                target: target.clone(),
                digest: digest.to_owned(),
                config,
                snapshot,
            });
        } else if self.verify_sources {
            bundle.verify_std_sources()?;
        }
        self.verify_sources = false;
        Ok(self.prepared.as_ref().expect("prepared std cache"))
    }
}

impl Prepared {
    pub fn hydrate<'ctx>(&self, context: &'ctx CompilerContext<'ctx>) -> io::Result<()> {
        let config = context.store.arenas.configs.alloc(self.config.clone());
        self.snapshot.hydrate(Gcx::new(context, config))
    }
}

pub(crate) fn freeze(
    config: &Config,
    target: &TargetFacts,
    cancelled: impl Fn() -> bool + 'static,
) -> io::Result<FrozenDependency> {
    let arenas = CompilerArenas::new();
    let diagnostics = Rc::new(DiagCtx::new(config.src.clone()).with_cancellation(cancelled));
    diagnostics.enable_recording();
    let store = CompilerStore::new_for_analysis(&arenas, config.src.join("target"), target.clone());
    let context = CompilerContext::new(diagnostics.clone(), store);
    let snapshot = Compiler::new(&context, config)
        .freeze_relocatable_dependency()
        .map_err(|error| {
            let first = diagnostics.take_recorded_diagnostics().into_iter().next();
            if let Some(diagnostic) = first {
                io::Error::new(error.kind(), format!("{error}: {}", diagnostic.message))
            } else {
                error
            }
        })?;
    if snapshot.retained_bytes() > MAX_FROZEN_STD_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "standard-library snapshot exceeds its byte budget",
        ));
    }
    Ok(snapshot)
}

pub(crate) fn std_config(root: PathBuf) -> Config {
    Config {
        name: "std".into(),
        identifier: "std".into(),
        src: root,
        dependencies: Default::default(),
        index: PackageIndex::new(0),
        kind: PackageKind::Library,
        executable_out: None,
        no_std_prelude: true,
        is_script: false,
        profile: Default::default(),
        codegen: Default::default(),
        overflow_checks: true,
        debug: Default::default(),
        harness_mode: Default::default(),
        std_mode: StdMode::BootstrapStd,
        is_std_provider: true,
        lint_warnings: false,
    }
}
