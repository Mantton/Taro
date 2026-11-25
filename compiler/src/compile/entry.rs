use crate::{
    compile::{config::PackageKind, context::GlobalContext},
    constants::ROOT_MODULE_NAME,
    error::{CompileResult, ReportedError},
    hir::{self, DeclarationKind, StdItem},
    sema::models::{GenericArgument, InterfaceReference, Ty, TyKind},
};

/// The entry-point forms, as stated in diagnostics.
const ACCEPTED_ENTRY_FORMS: &str =
    "`func main()` or `func main() -> Result[(), E]`, either of which may be `async`";

pub fn validate_entry_point(
    package: &hir::Package,
    gcx: GlobalContext,
) -> CompileResult<Option<hir::DefinitionID>> {
    match gcx.config.kind {
        PackageKind::Library => return Ok(None),
        PackageKind::Executable => {
            let id = find_main_in_module(&package.root, gcx, false)?;
            validate_entry_signature(id, gcx)?;
            return Ok(Some(id));
        }
        PackageKind::Both => {
            let main_mod = package
                .root
                .submodules
                .iter()
                .find(|m| gcx.symbol_eq(m.name, ROOT_MODULE_NAME));
            let Some(main_mod) = main_mod else {
                gcx.dcx().emit_error(
                    "expected a `main` module containing an entry-point function".into(),
                    None,
                );
                return Err(ReportedError);
            };
            let id = find_main_in_module(main_mod, gcx, true)?;
            validate_entry_signature(id, gcx)?;
            return Ok(Some(id));
        }
    }
}

/// How the error of a `Result`-returning `main` reaches the reporter's
/// `any std::fmt::Display` parameter.
#[derive(Debug, Clone, Copy)]
pub enum MainErrorConversion<'ctx> {
    /// The error type already is the reporter's parameter type.
    Identity,
    /// Box a concrete error that conforms to the reporter's interfaces.
    BoxExistential {
        interfaces: &'ctx [InterfaceReference<'ctx>],
    },
    /// Upcast an existential whose interfaces refine the reporter's.
    ExistentialUpcast,
}

/// A validated `func main() -> Result[(), E]`.
#[derive(Debug, Clone, Copy)]
pub struct ResultEntry<'ctx> {
    /// `Result[(), E]` as `main` returns it.
    pub result_ty: Ty<'ctx>,
    /// The `@lang("MainErrorReport")` function.
    pub reporter: hir::DefinitionID,
    /// The reporter's parameter type, `any std::fmt::Display`.
    pub display_ty: Ty<'ctx>,
    pub conversion: MainErrorConversion<'ctx>,
}

/// The `Result` form of an entry point already accepted by
/// `validate_entry_point`, or `None` for a unit entry point.
pub fn result_entry<'ctx>(
    gcx: GlobalContext<'ctx>,
    id: hir::DefinitionID,
) -> Option<ResultEntry<'ctx>> {
    match classify_entry_output(gcx, id) {
        Ok(EntryOutput::Result(entry)) => Some(entry),
        _ => None,
    }
}

enum EntryOutput<'ctx> {
    Unit,
    Result(ResultEntry<'ctx>),
}

fn validate_entry_signature(id: hir::DefinitionID, gcx: GlobalContext) -> CompileResult<()> {
    let ident = gcx.definition_ident(id);
    let sig = gcx.get_signature(id);

    if !sig.inputs.is_empty() {
        gcx.dcx().emit_error(
            format!(
                "entry point `main` must not take parameters; expected {ACCEPTED_ENTRY_FORMS}"
            )
            .into(),
            Some(ident.span),
        );
        return Err(ReportedError);
    }

    match classify_entry_output(gcx, id) {
        Ok(_) => Ok(()),
        Err(Some(message)) => {
            gcx.dcx().emit_error(message.into(), Some(ident.span));
            Err(ReportedError)
        }
        // The return type is already erroneous and was reported elsewhere.
        Err(None) => Err(ReportedError),
    }
}

fn classify_entry_output<'ctx>(
    gcx: GlobalContext<'ctx>,
    id: hir::DefinitionID,
) -> Result<EntryOutput<'ctx>, Option<String>> {
    let output = gcx.function_body_output(id);
    if output == gcx.types.void {
        return Ok(EntryOutput::Unit);
    }
    if output.is_error() {
        return Err(None);
    }

    let Some((ok_ty, err_ty)) = result_arguments(gcx, output) else {
        return Err(Some(format!(
            "entry point `main` must return `()` or `Result[(), E]`, found '{}'; expected {ACCEPTED_ENTRY_FORMS}",
            output.format(gcx)
        )));
    };
    if ok_ty.is_error() || err_ty.is_error() {
        return Err(None);
    }
    if ok_ty != gcx.types.void {
        return Err(Some(format!(
            "entry point `main` returning a `Result` must use `()` as its success type, found '{}'",
            ok_ty.format(gcx)
        )));
    }

    let Some(reporter) = gcx.std_item_def(StdItem::MainErrorReport) else {
        return Err(Some(
            "entry point `main` returns a `Result`, but the standard library does not provide `@lang(\"MainErrorReport\")`".into(),
        ));
    };
    let display_ty = gcx
        .get_signature(reporter)
        .inputs
        .first()
        .map(|input| input.ty)
        .expect("MainErrorReport takes the error to report");
    let Some(conversion) = printable_conversion(gcx, err_ty, display_ty) else {
        return Err(Some(format!(
            "error type '{}' of entry point `main` must be printable: it must conform to `std::fmt::Display`",
            err_ty.format(gcx)
        )));
    };

    Ok(EntryOutput::Result(ResultEntry {
        result_ty: output,
        reporter,
        display_ty,
        conversion,
    }))
}

fn result_arguments<'ctx>(gcx: GlobalContext<'ctx>, ty: Ty<'ctx>) -> Option<(Ty<'ctx>, Ty<'ctx>)> {
    let TyKind::Adt(def, args) = ty.kind() else {
        return None;
    };
    if Some(def.id) != gcx.std_item_def(StdItem::Result) {
        return None;
    }
    let ok = args.get(0).copied().and_then(GenericArgument::ty)?;
    let err = args.get(1).copied().and_then(GenericArgument::ty)?;
    Some((ok, err))
}

/// The value conversion string interpolation applies to an argument: the
/// error must coerce to `any std::fmt::Display`.
fn printable_conversion<'ctx>(
    gcx: GlobalContext<'ctx>,
    error_ty: Ty<'ctx>,
    display_ty: Ty<'ctx>,
) -> Option<MainErrorConversion<'ctx>> {
    if error_ty == display_ty {
        return Some(MainErrorConversion::Identity);
    }
    let TyKind::BoxedExistential {
        interfaces: required,
    } = display_ty.kind()
    else {
        return None;
    };

    if let TyKind::BoxedExistential { interfaces } = error_ty.kind() {
        let provided: Vec<_> = interfaces
            .iter()
            .flat_map(|interface| {
                crate::sema::impl_engine::ref_ops::collect_interface_with_superfaces(
                    gcx, *interface,
                )
            })
            .collect();
        // Both sides name the erased Self as their first argument; compare
        // the interface and its remaining arguments.
        let refines = required.iter().all(|wanted| {
            provided.iter().any(|have| {
                have.id == wanted.id
                    && have.arguments.iter().skip(1).eq(wanted.arguments.iter().skip(1))
            })
        });
        return refines.then_some(MainErrorConversion::ExistentialUpcast);
    }

    if matches!(
        error_ty.kind(),
        TyKind::Infer(_) | TyKind::Parameter(_) | TyKind::Never | TyKind::Error
    ) {
        return None;
    }
    let conforms = required.iter().all(|interface| {
        let interface =
            crate::sema::impl_engine::ref_ops::interface_ref_with_self(gcx, error_ty, *interface);
        crate::sema::tycheck::resolve_conformance_witness(gcx, interface).is_some()
    });
    conforms.then_some(MainErrorConversion::BoxExistential {
        interfaces: required,
    })
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
            if gcx.symbol_eq(ident.symbol, ROOT_MODULE_NAME) {
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
