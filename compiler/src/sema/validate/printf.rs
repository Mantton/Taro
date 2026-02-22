use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor},
    sema::{models::TyKind, tycheck::results::TypeCheckResults},
};

pub fn run<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
    results: &TypeCheckResults<'ctx>,
) -> CompileResult<()> {
    let targets = FormatTargets {
        printf_def: find_std_format_function(gcx, "printf"),
        sprintf_def: find_std_format_function(gcx, "sprintf"),
    };
    if targets.printf_def.is_none() && targets.sprintf_def.is_none() {
        return Ok(());
    }

    let mut actor = Actor {
        gcx,
        results,
        targets,
    };
    hir::walk_package(&mut actor, package);
    Ok(())
}

fn find_std_format_function(gcx: GlobalContext<'_>, name: &str) -> Option<DefinitionID> {
    let std_pkg = gcx.std_package_index()?;
    let output = gcx.resolution_output(std_pkg);
    output.definition_to_ident.iter().find_map(|(id, ident)| {
        let kind = output.definition_to_kind.get(id)?;
        if *kind == DefinitionKind::Function && gcx.symbol_eq(ident.symbol, name) {
            Some(*id)
        } else {
            None
        }
    })
}

#[derive(Clone, Copy)]
struct FormatTargets {
    printf_def: Option<DefinitionID>,
    sprintf_def: Option<DefinitionID>,
}

struct Actor<'ctx, 'results> {
    gcx: GlobalContext<'ctx>,
    results: &'results TypeCheckResults<'ctx>,
    targets: FormatTargets,
}

impl<'ctx> HirVisitor for Actor<'ctx, '_> {
    fn visit_expression(&mut self, node: &hir::Expression) -> Self::Result {
        if let hir::ExpressionKind::Call { callee, arguments } = &node.kind {
            self.validate_printf_call(node, callee, arguments);
        }
        hir::walk_expression(self, node);
    }
}

#[derive(Clone, Copy)]
enum FormatSpec {
    Decimal,
    String,
    Value,
}

enum FormatParseError {
    DanglingPercent,
    UnknownSpecifier(u8),
}

impl<'ctx> Actor<'ctx, '_> {
    fn validate_printf_call(
        &self,
        call: &hir::Expression,
        callee: &hir::Expression,
        arguments: &[hir::ExpressionArgument],
    ) {
        let Some(format_fn_name) = self.format_function_name(callee) else {
            return;
        };

        let Some(format_arg) = arguments.first() else {
            return;
        };

        // If type-check already errored on format arg, skip to avoid cascades.
        let Some(format_ty) = self.results.try_node_type(format_arg.expression.id) else {
            return;
        };
        if format_ty.is_error() {
            return;
        }

        let hir::ExpressionKind::Literal(hir::Literal::String(format_literal)) =
            &format_arg.expression.kind
        else {
            // Dynamic format strings are validated at runtime.
            return;
        };

        let format_text = self.gcx.symbol_text(*format_literal);
        let format_text = format_text.as_ref();
        let specs = match parse_specs(format_text) {
            Ok(specs) => specs,
            Err(FormatParseError::DanglingPercent) => {
                let message = format!("{format_fn_name} format string ends with dangling '%'");
                self.gcx
                    .dcx()
                    .emit_error(message.into(), Some(format_arg.expression.span));
                return;
            }
            Err(FormatParseError::UnknownSpecifier(spec)) => {
                let message = format!(
                    "{} format string contains unknown specifier '{}'",
                    format_fn_name,
                    describe_specifier(spec)
                );
                self.gcx
                    .dcx()
                    .emit_error(message.into(), Some(format_arg.expression.span));
                return;
            }
        };

        let provided = arguments.len().saturating_sub(1);
        if specs.len() != provided {
            let message = format!(
                "{} format expects {} argument(s), but {} provided",
                format_fn_name,
                specs.len(),
                provided
            );
            self.gcx.dcx().emit_error(message.into(), Some(call.span));
            return;
        }

        for (idx, spec) in specs.iter().enumerate() {
            let arg = &arguments[idx + 1];
            let Some(arg_ty) = self.results.try_node_type(arg.expression.id) else {
                continue;
            };

            if arg_ty.is_error() {
                continue;
            }

            match spec {
                FormatSpec::Decimal if !is_integer(arg_ty.kind()) => {
                    let message = format!(
                        "{} specifier '%d' expects an integer argument, found '{}'",
                        format_fn_name,
                        arg_ty.format(self.gcx)
                    );
                    self.gcx
                        .dcx()
                        .emit_error(message.into(), Some(arg.expression.span));
                }
                FormatSpec::String if !matches!(arg_ty.kind(), TyKind::String) => {
                    let message = format!(
                        "{} specifier '%s' expects a string argument, found '{}'",
                        format_fn_name,
                        arg_ty.format(self.gcx)
                    );
                    self.gcx
                        .dcx()
                        .emit_error(message.into(), Some(arg.expression.span));
                }
                _ => {}
            }
        }
    }

    fn format_function_name(&self, callee: &hir::Expression) -> Option<&'static str> {
        let target = self.resolve_call_target(callee)?;
        if Some(target) == self.targets.printf_def {
            return Some("printf");
        }
        if Some(target) == self.targets.sprintf_def {
            return Some("sprintf");
        }
        None
    }

    fn resolve_call_target(&self, callee: &hir::Expression) -> Option<DefinitionID> {
        if let Some(def_id) = self.results.overload_source(callee.id) {
            return Some(def_id);
        }

        let resolution = self.results.value_resolution(callee.id)?;
        match resolution {
            hir::Resolution::Definition(
                id,
                DefinitionKind::Function
                | DefinitionKind::AssociatedFunction
                | DefinitionKind::VariantConstructor(..),
            ) => Some(id),
            _ => None,
        }
    }
}

fn parse_specs(input: &str) -> Result<Vec<FormatSpec>, FormatParseError> {
    let bytes = input.as_bytes();
    let mut idx = 0;
    let mut specs = Vec::new();

    while idx < bytes.len() {
        if bytes[idx] != b'%' {
            idx += 1;
            continue;
        }

        idx += 1;
        if idx >= bytes.len() {
            return Err(FormatParseError::DanglingPercent);
        }

        match bytes[idx] {
            b'%' => {}
            b'd' => specs.push(FormatSpec::Decimal),
            b's' => specs.push(FormatSpec::String),
            b'v' => specs.push(FormatSpec::Value),
            unknown => return Err(FormatParseError::UnknownSpecifier(unknown)),
        }
        idx += 1;
    }

    Ok(specs)
}

fn is_integer(ty: TyKind<'_>) -> bool {
    matches!(ty, TyKind::Int(_) | TyKind::UInt(_))
}

fn describe_specifier(spec: u8) -> String {
    if spec.is_ascii_graphic() {
        format!("%{}", spec as char)
    } else {
        format!("%\\x{spec:02x}")
    }
}
