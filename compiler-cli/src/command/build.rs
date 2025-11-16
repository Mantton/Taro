use std::rc::Rc;

use crate::{
    CommandLineArguments,
    package::{
        sync::sync_dependencies,
        utils::{get_package_name, language_home},
    },
};
use compiler::{
    PackageIndex,
    compile::{Compiler, config::Config},
    constants::STD_PREFIX,
    diagnostics::DiagCtx,
    error::ReportedError,
};

pub fn run(arguments: CommandLineArguments) -> Result<(), ReportedError> {
    let cwd = std::env::current_dir().map_err(|_| ReportedError)?;
    let dcx = Rc::new(DiagCtx::new(cwd));
    let graph = sync_dependencies(arguments.path)?;

    let _ = compile_std(dcx.clone())?;

    for (index, package) in graph.ordered.iter().enumerate() {
        let package_index = PackageIndex::new(index + 1);
        println!("Compiling – {}", package.package.0);
        let name = get_package_name(&package.package.0).map_err(|_| ReportedError)?;
        let _ = package.unique_identifier().map_err(|_| ReportedError)?;
        let dependencies = graph.dependencies_for(package).map_err(|_| ReportedError)?;
        let src = package
            .path()
            .and_then(|p| {
                p.canonicalize()
                    .map_err(|e| format!("failed to resolve path – {}", e))
            })
            .map_err(|e| format!("failed to resolve path – {}", e))
            .map_err(|_| ReportedError)?;
        let config = Config {
            name,
            src,
            dependencies,
            index: package_index,
        };
        let mut compiler = Compiler::new(config, dcx.clone());
        let _ = compiler.build()?;
    }
    Ok(())
}

fn compile_std(dcx: Rc<DiagCtx>) -> Result<(), ReportedError> {
    println!("Compiling – std");

    let src = language_home()
        .map_err(|e| {
            let message = format!("failed to resolve language home – {}", e);
            dcx.emit_error(message, None);
            ReportedError
        })?
        .join(STD_PREFIX)
        .canonicalize()
        .map_err(|e| {
            let message = format!("failed to resolve standard library location – {}", e);
            dcx.emit_error(message, None);
            ReportedError
        })?;
    let config = Config {
        name: "std".into(),
        src,
        dependencies: Default::default(),
        index: PackageIndex::new(0),
    };
    let mut compiler = Compiler::new(config, dcx);
    let _ = compiler.build()?;
    Ok(())
}
