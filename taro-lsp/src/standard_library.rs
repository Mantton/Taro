//! Prepare matching standard-library metadata in a disposable session.

use std::{io, path::PathBuf, rc::Rc};

use compiler::{
    PackageIndex,
    compile::{
        Compiler,
        config::{Config, PackageKind, StdMode},
        context::{CompilerArenas, CompilerContext, CompilerStore, Gcx},
        frozen_dependencies::FrozenDependency,
        source::WorkspaceSources,
        target_facts::TargetFacts,
    },
    diagnostics::DiagCtx,
};

use crate::bundle::Bundle;

const MAX_FROZEN_STD_BYTES: usize = 128 * 1024 * 1024;

#[derive(Default)]
pub struct StdCache(Option<Prepared>);

pub struct Prepared {
    target: TargetFacts,
    digest: String,
    config: Config,
    snapshot: FrozenDependency,
}

impl StdCache {
    pub fn prepare(
        &mut self,
        bundle: &Bundle,
        target: &TargetFacts,
        expected_digest: Option<&str>,
        sources: Rc<WorkspaceSources>,
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
            .0
            .as_ref()
            .is_some_and(|current| current.target == *target && current.digest == digest)
        {
            self.0 = None;
            let root = bundle.verify_std_sources()?;
            let config = std_config(root);
            let snapshot = freeze(&config, target, sources, cancelled)?;
            bundle.verify_std_sources()?;
            if snapshot.retained_bytes() > MAX_FROZEN_STD_BYTES {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "standard-library snapshot exceeds its byte budget",
                ));
            }
            self.0 = Some(Prepared {
                target: target.clone(),
                digest: digest.to_owned(),
                config,
                snapshot,
            });
        }
        Ok(self.0.as_ref().expect("prepared std cache"))
    }
}

impl Prepared {
    pub fn hydrate<'ctx>(&self, context: &'ctx CompilerContext<'ctx>) -> io::Result<()> {
        let config = context.store.arenas.configs.alloc(self.config.clone());
        self.snapshot.hydrate(Gcx::new(context, config))
    }
}

fn freeze(
    config: &Config,
    target: &TargetFacts,
    sources: Rc<WorkspaceSources>,
    cancelled: impl Fn() -> bool + 'static,
) -> io::Result<FrozenDependency> {
    let arenas = CompilerArenas::new();
    let diagnostics =
        Rc::new(DiagCtx::with_sources(config.src.clone(), sources).with_cancellation(cancelled));
    diagnostics.enable_recording();
    let store = CompilerStore::new_for_analysis(&arenas, config.src.join("target"), target.clone());
    let context = CompilerContext::new(diagnostics.clone(), store);
    Compiler::new(&context, config)
        .freeze_dependency()
        .map_err(|error| {
            let first = diagnostics.take_recorded_diagnostics().into_iter().next();
            if let Some(diagnostic) = first {
                io::Error::new(error.kind(), format!("{error}: {}", diagnostic.message))
            } else {
                error
            }
        })
}

fn std_config(root: PathBuf) -> Config {
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
