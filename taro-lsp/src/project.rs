//! Resolve settings for the active source package.

use std::{io, path::Path};

use compiler::{
    PackageIndex,
    compile::{
        config::{Config, PackageKind, StdMode},
        source::SourceProvider,
    },
    constants::{MANIFEST_FILE, STD_PACKAGE_PATH, STD_PREFIX},
    package::{
        manifest::{Manifest, SourceSpec},
        utils::get_package_name,
    },
};
use serde::Deserialize;

#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Preferences {
    pub target: Option<String>,
    pub std_digest: Option<String>,
}

#[derive(Deserialize)]
struct PackagePreferences {
    #[serde(default)]
    language_server: Preferences,
}

pub struct Project {
    pub config: Config,
    pub prefs: Preferences,
}

impl Project {
    pub fn read(root: &Path, sources: &dyn SourceProvider, attach_std: bool) -> io::Result<Self> {
        let name = root
            .file_stem()
            .and_then(|name| name.to_str())
            .unwrap_or("workspace");
        let is_script = root.extension().is_some_and(|extension| extension == "tr");
        let mut config = Config {
            name: name.into(),
            identifier: name.into(),
            src: root.to_path_buf(),
            dependencies: Default::default(),
            index: PackageIndex::new(1),
            kind: PackageKind::Library,
            executable_out: None,
            no_std_prelude: !attach_std,
            is_script,
            profile: Default::default(),
            codegen: Default::default(),
            overflow_checks: true,
            debug: Default::default(),
            harness_mode: Default::default(),
            std_mode: StdMode::BootstrapStd,
            is_std_provider: false,
            lint_warnings: true,
        };
        let mut prefs = Preferences::default();
        if !is_script {
            match sources.read_text(&root.join(MANIFEST_FILE)) {
                Ok(source) => {
                    let manifest: Manifest =
                        toml::from_str(source.text()).map_err(io::Error::other)?;
                    let normalized = manifest
                        .normalize(root, sources)
                        .map_err(io::Error::other)?;
                    config.name = get_package_name(&normalized.path.0).map_err(io::Error::other)?;
                    config.identifier = normalized.path.0;
                    config.kind = normalized.kind;
                    config.no_std_prelude = normalized.no_std_prelude || !attach_std;
                    prefs = toml::from_str::<PackagePreferences>(source.text())
                        .map_err(io::Error::other)?
                        .language_server;
                    for (alias, dependency) in normalized.dependencies {
                        if dependency.package.0.as_str() != STD_PACKAGE_PATH || !attach_std {
                            return Err(io::Error::other(format!(
                                "typed analysis cannot resolve dependency '{}'",
                                dependency.package.0
                            )));
                        }
                        let SourceSpec::Path { abs } = dependency.source else {
                            return Err(io::Error::other(
                                "a requested standard-library version needs locally matching sources",
                            ));
                        };
                        let actual = crate::bundle::std_digest(&abs)?;
                        if prefs
                            .std_digest
                            .as_ref()
                            .is_some_and(|expected| expected != &actual)
                        {
                            return Err(io::Error::other(
                                "project standard-library source identities disagree",
                            ));
                        }
                        prefs.std_digest = Some(actual);
                        config.dependencies.insert(alias, STD_PREFIX.into());
                    }
                }
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(error),
            }
        }
        if attach_std {
            config.std_mode = StdMode::FullStd;
            config
                .dependencies
                .insert(STD_PREFIX.into(), STD_PREFIX.into());
        } else if prefs.std_digest.is_some() {
            return Err(io::Error::other(
                "the project requests a standard library, but this analysis has no SDK or bundle",
            ));
        }
        Ok(Self { config, prefs })
    }
}
