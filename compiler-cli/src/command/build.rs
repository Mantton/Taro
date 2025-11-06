use crate::{
    CommandLineArguments,
    package::{sync::sync_dependencies, utils::get_package_name},
};
use compiler::{
    compile::{Compiler, config::Config},
    error::ReportedError,
};

pub fn run(arguments: CommandLineArguments) -> Result<(), ReportedError> {
    let cwd = std::env::current_dir().map_err(|_| ReportedError)?;
    let graph = sync_dependencies(arguments.path)?;

    for package in &graph.ordered {
        println!("Compile {}", package.package.0);
        let name = get_package_name(&package.package.0).map_err(|_| ReportedError)?;
        let _ = package.unique_identifier().map_err(|_| ReportedError)?;
        let dependencies = graph.dependencies_for(package).map_err(|_| ReportedError)?;
        let src = package
            .path()
            .and_then(|p| {
                p.canonicalize()
                    .map_err(|e| format!("failed to resolve path – {}", e))
            })
            .map_err(|e| format!("failed to resolve path – {}", e))
            .map_err(|_| ReportedError)?;
        let config = Config {
            name,
            src,
            cwd: cwd.clone(),
            dependencies,
        };
        let mut compiler = Compiler::new(config);
        let _ = compiler.build()?;
    }
    Ok(())
}
