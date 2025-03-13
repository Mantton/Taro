use crate::arguments::CommandLineArguments;
use std::{
    env::{self, current_dir},
    path::PathBuf,
};
use taroc_constants::{LANGUAGE_HOME, MANIFEST_FILE, STD_PREFIX};
use taroc_context::with_global_context;
use taroc_error::{CompileError, CompileResult};
use taroc_lexer::tokenize_package;
use taroc_package::{CompilerConfig, Manifest, PackageIdentifier, sync_dependencies};
use taroc_parse::parse_package;
use taroc_span::create_session_globals_then;

pub fn run(arguments: CommandLineArguments) -> CompileResult<()> {
    let project_path = arguments.path;
    let builder = Builder::new(project_path);
    builder.build()
}

pub struct Builder {
    project_path: PathBuf,
}

impl Builder {
    pub fn new(project_path: PathBuf) -> Self {
        Builder { project_path }
    }
}

impl Builder {
    fn build(self) -> CompileResult<()> {
        // run `taro get` to install package dependencies
        let (lockfile, dependency_graph, local_mapping) =
            sync_dependencies(&self.project_path).map_err(CompileError::Message)?;

        // read `package.toml` & `package.lock` files to prepare dependency
        let manifest = Manifest::parse(&self.project_path.join(MANIFEST_FILE))
            .map_err(CompileError::Message)?;

        let ordered_packages = dependency_graph.compilation_order();
        println!("Compilation Order {:?}", ordered_packages);

        for (_, package) in ordered_packages.into_iter().enumerate() {
            let mut is_std = false;
            let path = if package == manifest.identifier().normalize() {
                self.project_path.clone()
            } else if package == STD_PREFIX {
                is_std = true;
                env::var(LANGUAGE_HOME)
                    .map(|home| PathBuf::from(home).join(STD_PREFIX))
                    .map_err(|err| format!("{} `{}`", err, LANGUAGE_HOME))
                    .map_err(CompileError::Message)?
            } else {
                let target = lockfile
                    .package
                    .iter()
                    .find(|dependency| {
                        package == dependency.name || dependency.qualified() == package
                    })
                    .expect("target should be in lockfile");

                if target.source == "local" {
                    local_mapping
                        .get(&target.revision)
                        .expect("local package to be mapped")
                        .clone()
                } else {
                    PackageIdentifier::from(target.name.clone())
                        .install_path(target.revision.clone())
                        .map_err(CompileError::Message)?
                }
            };

            let cwd = current_dir().map_err(|err| {
                CompileError::Message(format!(
                    "failed to resolve current working directory, {}",
                    err
                ))
            })?;

            println!("Compiling {}", package);
            let config = CompilerConfig::new(package, path, cwd, is_std, &lockfile)?;
            self.compile(config)?;
            break;
        }

        Ok(())
    }

    fn compile(&self, config: CompilerConfig) -> CompileResult<()> {
        create_session_globals_then(|| {
            with_global_context(config, |gcx| {
                let package = tokenize_package(&gcx.config.source_path, gcx)?;
                let package = parse_package(package, gcx)?;
                let package = taroc_ast_passes::run(package, gcx)?;
                taroc_hir_passes::run(package, gcx)
            })
        })?;
        Ok(())
    }
}
