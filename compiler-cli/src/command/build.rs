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
use std::{path::PathBuf, process::Command, rc::Rc};

pub fn run(
    arguments: CommandLineArguments,
    require_executable: bool,
) -> Result<Option<std::path::PathBuf>, ReportedError> {
    let cwd = std::env::current_dir().map_err(|_| ReportedError)?;
    let dcx = Rc::new(DiagCtx::new(cwd));
    let arenas = CompilerArenas::new();
    let project_root = arguments.path.canonicalize().map_err(|_| ReportedError)?;
    let target_root = project_root.join("target").join("objects");
    let store = CompilerStore::new(&arenas, target_root);
    let icx = CompilerContext::new(dcx, store);

    let graph = sync_dependencies(arguments.path)?;

    let _ = compile_std(&icx)?;
    build_runtime(&icx, &project_root)?;

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

        if is_root && require_executable {
            if package.kind == compiler::compile::config::PackageKind::Library {
                icx.dcx.emit_error(
                    "`run` requires the root package to be executable".into(),
                    None,
                );
                return Err(ReportedError);
            }
        }

        let package_index = PackageIndex::new(index + 1);
        println!("Compiling – {}", package.package.0);
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
        let exe_path = compiler.build()?;
        if exe_path.is_some() {
            return Ok(exe_path);
        }
    }
    Ok(None)
}

fn build_runtime(ctx: &CompilerContext<'_>, project_root: &PathBuf) -> Result<(), ReportedError> {
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .ok_or(ReportedError)?
        .to_path_buf();
    let target_dir = project_root.join("target").join("runtime");

    let status = Command::new("cargo")
        .arg("build")
        .arg("-p")
        .arg("taro-runtime")
        .arg("--manifest-path")
        .arg(workspace_root.join("Cargo.toml"))
        .arg("--target-dir")
        .arg(&target_dir)
        .status()
        .map_err(|e| {
            ctx.dcx.emit_error(
                format!("failed to invoke cargo to build runtime: {e}"),
                None,
            );
            ReportedError
        })?;

    if !status.success() {
        ctx.dcx
            .emit_error("failed to build runtime crate".into(), None);
        return Err(ReportedError);
    }

    let lib_path = target_dir.join("debug").join("libtaro_runtime.a");
    if !lib_path.exists() {
        ctx.dcx.emit_error(
            format!("runtime archive not found at {}", lib_path.display()),
            None,
        );
        return Err(ReportedError);
    }

    // Make the runtime archive available to the existing link step by treating it like another
    // "object file" input.
    ctx.store.add_link_input(lib_path);
    Ok(())
}

fn compile_std<'a>(ctx: &'a CompilerContext<'a>) -> Result<(), ReportedError> {
    println!("Compiling – std");

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
    let _ = compiler.build()?;
    Ok(())
}
