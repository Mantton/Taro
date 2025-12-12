use crate::{
    compile::{config::PackageKind, context::GlobalContext},
    constants::ROOT_MODULE_NAME,
    error::{CompileResult, ReportedError},
    hir::{self, DeclarationKind},
};

pub fn validate_entry_point(package: &hir::Package, gcx: GlobalContext) -> CompileResult<()> {
    match gcx.config.kind {
        PackageKind::Library => return Ok(()),
        PackageKind::Executable => {
            let id = find_main_in_module(&package.root, gcx, false)?;
            gcx.cache_entry_point(id);
        }
        PackageKind::Both => {
            let main_mod = package
                .root
                .submodules
                .iter()
                .find(|m| m.name.as_str() == ROOT_MODULE_NAME);
            let Some(main_mod) = main_mod else {
                gcx.dcx().emit_error(
                    "expected a `main` module containing an entry-point function".into(),
                    None,
                );
                return Err(ReportedError);
            };
            let id = find_main_in_module(main_mod, gcx, true)?;
            gcx.cache_entry_point(id);
        }
    }

    Ok(())
}

fn find_main_in_module(
    module: &hir::Module,
    gcx: GlobalContext,
    is_submodule: bool,
) -> CompileResult<hir::DefinitionID> {
    let mut found: Option<hir::DefinitionID> = None;

    for decl in &module.declarations {
        if let DeclarationKind::Function(_) = &decl.kind {
            let ident = gcx.definition_ident(decl.id);
            if ident.symbol.as_str() == ROOT_MODULE_NAME {
                if found.is_some() {
                    gcx.dcx().emit_error(
                        "multiple `main` entry-point functions found".into(),
                        Some(ident.span),
                    );
                    return Err(ReportedError);
                }
                found = Some(decl.id);
            }
        }
    }

    match found {
        Some(id) => Ok(id),
        None => {
            let msg = if is_submodule {
                "expected a function named `main` inside the `main` module"
            } else {
                "expected a function named `main` in the root module"
            };
            gcx.dcx().emit_error(msg.into(), None);
            Err(ReportedError)
        }
    }
}
