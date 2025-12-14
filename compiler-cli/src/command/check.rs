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
    compile::{
        Compiler,
        config::Config,
        context::{CompilerArenas, CompilerContext, CompilerStore},
    },
    constants::STD_PREFIX,
    diagnostics::DiagCtx,
    error::ReportedError,
};

pub fn run(arguments: CommandLineArguments) -> Result<(), ReportedError> {
    let cwd = std::env::current_dir().map_err(|_| ReportedError)?;
    let dcx = Rc::new(DiagCtx::new(cwd));
    let arenas = CompilerArenas::new();
    let project_root = arguments.path.canonicalize().map_err(|_| ReportedError)?;
    let target_root = project_root.join("target").join("objects");
    let store = CompilerStore::new(&arenas, target_root);
    let icx = CompilerContext::new(dcx, store);

    let graph = sync_dependencies(arguments.path)?;

    compile_std(&icx)?;

    let total = graph.ordered.len();
    for (index, package) in graph.ordered.iter().enumerate() {
        let is_root = index + 1 == total;
        if !is_root && package.kind != compiler::compile::config::PackageKind::Library {
            icx.dcx.emit_error(
                format!(
                    "dependency `{}` must be a library (found {:?})",
                    package.package.0, package.kind
                ),
                None,
            );
            return Err(ReportedError);
        }

        let package_index = PackageIndex::new(index + 1);
        println!("Checking – {}", package.package.0);
        let name = get_package_name(&package.package.0).map_err(|_| ReportedError)?;
        let identifier = package.unique_identifier().map_err(|_| ReportedError)?;
        let mut dependencies = graph.dependencies_for(package).map_err(|_| ReportedError)?;
        dependencies.insert("std".into(), "std".into());

        let src = package
            .path()
            .and_then(|p| {
                p.canonicalize()
                    .map_err(|e| format!("failed to resolve path – {}", e))
            })
            .map_err(|e| format!("failed to resolve path – {}", e))
            .map_err(|_| ReportedError)?;

        let config = icx.store.arenas.configs.alloc(Config {
            name,
            identifier,
            src,
            dependencies,
            index: package_index,
            kind: package.kind,
            executable_out: arguments.output.clone(),
        });

        let mut compiler = Compiler::new(&icx, config);
        let _ = compiler.check()?;
    }

    Ok(())
}

fn compile_std<'a>(ctx: &'a CompilerContext<'a>) -> Result<(), ReportedError> {
    println!("Checking – std");

    let src = language_home()
        .map_err(|e| {
            let message = format!("failed to resolve language home – {}", e);
            ctx.dcx.emit_error(message, None);
            ReportedError
        })?
        .join(STD_PREFIX)
        .canonicalize()
        .map_err(|e| {
            let message = format!("failed to resolve standard library location – {}", e);
            ctx.dcx.emit_error(message, None);
            ReportedError
        })?;

    let index = PackageIndex::new(0);

    let config = ctx.store.arenas.configs.alloc(Config {
        index,
        name: "std".into(),
        identifier: "std".into(),
        src,
        dependencies: Default::default(),
        kind: compiler::compile::config::PackageKind::Library,
        executable_out: None,
    });

    let mut compiler = Compiler::new(ctx, config);
    let _ = compiler.check()?;
    Ok(())
}
