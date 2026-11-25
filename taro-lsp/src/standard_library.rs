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

use crate::{
    bundle::{self, Bundle},
    sdk::Sdk,
};

pub(crate) const MAX_FROZEN_STD_BYTES: usize = 128 * 1024 * 1024;

pub enum Installation {
    Sdk(Sdk),
    Portable(Bundle),
}

impl Installation {
    pub fn target(&self, target: Option<&str>) -> io::Result<TargetFacts> {
        match self {
            Self::Sdk(sdk) => sdk.target(target),
            Self::Portable(bundle) => bundle.target(target),
        }
    }
}

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
        installation: &Installation,
        target: &TargetFacts,
        expected_digest: Option<&str>,
        cancelled: impl Fn() -> bool + 'static,
    ) -> io::Result<&Prepared> {
        let digest = match installation {
            Installation::Portable(bundle) => bundle.std_digest().to_owned(),
            Installation::Sdk(sdk) => match &self.prepared {
                Some(current) if !self.verify_sources => current.digest.clone(),
                _ => bundle::std_digest(&sdk.std)?,
            },
        };
        if expected_digest.is_some_and(|expected| expected != digest.as_str()) {
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
            let (config, cached) = match installation {
                Installation::Portable(bundle) => (
                    std_config(bundle.verify_std_sources()?),
                    bundle.frozen_std(target).ok(),
                ),
                Installation::Sdk(sdk) => {
                    (std_config(sdk.std.clone()), sdk.cached_std(&digest, target))
                }
            };
            let snapshot = match cached {
                Some(snapshot) => snapshot,
                None => {
                    let snapshot = freeze(&config, target, cancelled)?;
                    match installation {
                        Installation::Portable(bundle) => {
                            bundle.verify_std_sources()?;
                        }
                        Installation::Sdk(sdk) => {
                            if bundle::std_digest(&sdk.std)? != digest {
                                return Err(io::Error::other(
                                    "SDK std sources changed during analysis",
                                ));
                            }
                            // Read-only or unavailable cache locations still support analysis.
                            let _ = sdk.store_std(&digest, target, &snapshot);
                        }
                    }
                    snapshot
                }
            };
            self.prepared = Some(Prepared {
                target: target.clone(),
                digest,
                config,
                snapshot,
            });
        } else if self.verify_sources
            && let Installation::Portable(bundle) = installation
        {
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
