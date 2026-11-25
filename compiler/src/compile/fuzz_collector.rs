use crate::{
    compile::context::GlobalContext,
    hir::{self, DeclarationKind, KnownAttribute, StdItem},
    sema::models::{GenericArgument, TyKind, UIntTy},
};

/// Metadata for one `@fuzz` function discovered in the root package.
#[derive(Debug, Clone)]
pub struct FuzzTarget {
    pub id: hir::DefinitionID,
    pub display_name: String,
    pub short_name: String,
}

/// Discover and validate every `@fuzz` target in the analyzed root package.
pub fn collect_fuzz_targets(
    package: &hir::Package,
    gcx: GlobalContext<'_>,
) -> crate::error::CompileResult<Vec<FuzzTarget>> {
    let mut targets = Vec::new();
    let mut path = Vec::new();
    collect_from_module(&package.root, gcx, &mut path, &mut targets)?;
    Ok(targets)
}

/// Select a single `@fuzz` target by exact qualified name (treating `.` and `::`
/// equivalently, case-insensitively) or unique unqualified short name.
pub fn select_fuzz_target(
    targets: Vec<FuzzTarget>,
    requested: &str,
    gcx: GlobalContext<'_>,
) -> crate::error::CompileResult<FuzzTarget> {
    let needle = normalize_name(requested);
    if needle.is_empty() {
        gcx.dcx()
            .emit_error("--fuzz target name must not be empty".into(), None);
        return Err(crate::error::ReportedError);
    }

    // 1. Exact qualified match.
    let exact: Vec<&FuzzTarget> = targets
        .iter()
        .filter(|t| normalize_name(&t.display_name) == needle)
        .collect();
    if exact.len() == 1 {
        return Ok(exact[0].clone());
    }

    // 2. Exact short-name match or suffix segment match (`ns::name` / `name`).
    let suffix = format!(".{needle}");
    let matched: Vec<&FuzzTarget> = targets
        .iter()
        .filter(|t| {
            let norm = normalize_name(&t.display_name);
            normalize_name(&t.short_name) == needle || norm.ends_with(&suffix)
        })
        .collect();

    match matched.len() {
        1 => Ok(matched[0].clone()),
        0 => {
            let available = if targets.is_empty() {
                "no @fuzz targets were found in this package".to_string()
            } else {
                let names: Vec<&str> = targets.iter().map(|t| t.display_name.as_str()).collect();
                format!("available @fuzz targets: {}", names.join(", "))
            };
            gcx.dcx().emit_error(
                format!("unknown @fuzz target '{requested}'; {available}"),
                None,
            );
            Err(crate::error::ReportedError)
        }
        _ => {
            let names: Vec<&str> = matched.iter().map(|t| t.display_name.as_str()).collect();
            gcx.dcx().emit_error(
                format!(
                    "ambiguous @fuzz target '{requested}'; matches: {}",
                    names.join(", ")
                ),
                None,
            );
            Err(crate::error::ReportedError)
        }
    }
}

fn normalize_name(value: &str) -> String {
    value.trim().replace("::", ".").to_ascii_lowercase()
}

fn collect_from_module(
    module: &hir::Module,
    gcx: GlobalContext<'_>,
    path: &mut Vec<String>,
    targets: &mut Vec<FuzzTarget>,
) -> crate::error::CompileResult<()> {
    for decl in &module.declarations {
        collect_from_declaration(decl, gcx, path, targets)?;
    }
    for submodule in &module.submodules {
        path.push(gcx.symbol_text(submodule.name).to_string());
        collect_from_module(submodule, gcx, path, targets)?;
        path.pop();
    }
    Ok(())
}

fn collect_from_declaration(
    decl: &hir::Declaration,
    gcx: GlobalContext<'_>,
    path: &mut Vec<String>,
    targets: &mut Vec<FuzzTarget>,
) -> crate::error::CompileResult<()> {
    let has_fuzz = decl
        .attributes
        .iter()
        .any(|attr| attr.as_known(gcx) == Some(KnownAttribute::Fuzz));

    match &decl.kind {
        DeclarationKind::Function(function) if has_fuzz => {
            if decl
                .attributes
                .iter()
                .any(|attr| attr.as_known(gcx) == Some(KnownAttribute::ExpectPanic))
            {
                gcx.dcx().emit_error(
                    "@expectPanic is only supported by @test functions, not @fuzz targets".into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }
            if function.is_async {
                gcx.dcx().emit_error(
                    "@fuzz functions must be synchronous".into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }
            if function.generics.type_parameters.is_some() {
                gcx.dcx().emit_error(
                    "@fuzz functions must not be generic".into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }
            if crate::sema::tycheck::utils::normalize_aliases(
                gcx,
                gcx.get_signature(decl.id).output,
            ) != gcx.types.void
            {
                gcx.dcx().emit_error(
                    "@fuzz functions must return unit (`()`)".into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }
            if function.signature.prototype.inputs.len() != 1 {
                gcx.dcx().emit_error(
                    "@fuzz functions must take exactly one `std::mem::Span[uint8]` parameter"
                        .into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }
            let parameter = &function.signature.prototype.inputs[0];
            if parameter.default_value.is_some() || parameter.is_variadic {
                gcx.dcx().emit_error(
                    "the @fuzz input parameter cannot be defaulted or variadic".into(),
                    Some(parameter.span),
                );
                return Err(crate::error::ReportedError);
            }

            let signature = gcx.get_signature(decl.id);
            let span_id = gcx.std_item_def(StdItem::Span);
            let correct_parameter = signature.inputs.first().is_some_and(|param| {
                let ty = crate::sema::tycheck::utils::normalize_aliases(gcx, param.ty);
                matches!(
                    ty.kind(),
                    TyKind::Adt(def, args)
                        if Some(def.id) == span_id
                            && args.len() == 1
                            && matches!(
                                args[0],
                                GenericArgument::Type(elem)
                                    if matches!(
                                        crate::sema::tycheck::utils::normalize_aliases(gcx, elem).kind(),
                                        TyKind::UInt(UIntTy::U8)
                                    )
                            )
                )
            });
            if !correct_parameter {
                gcx.dcx().emit_error(
                    "@fuzz functions must take a `std::mem::Span[uint8]` parameter".into(),
                    Some(parameter.span),
                );
                return Err(crate::error::ReportedError);
            }

            let short_name = gcx.symbol_text(decl.identifier.symbol).to_string();
            let display_name = if path.is_empty() {
                short_name.clone()
            } else {
                format!("{}::{short_name}", path.join("::"))
            };

            targets.push(FuzzTarget {
                id: decl.id,
                display_name,
                short_name,
            });
        }
        DeclarationKind::Namespace(namespace) => {
            if has_fuzz {
                gcx.dcx().emit_error(
                    "@fuzz can only be applied to functions".into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }
            path.push(gcx.symbol_text(decl.identifier.symbol).to_string());
            for inner in &namespace.declarations {
                collect_from_declaration(inner, gcx, path, targets)?;
            }
            path.pop();
        }
        _ if has_fuzz => {
            gcx.dcx().emit_error(
                "@fuzz can only be applied to functions".into(),
                Some(decl.span),
            );
            return Err(crate::error::ReportedError);
        }
        _ => {}
    }

    Ok(())
}
