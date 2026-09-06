use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir,
    sema::{
        models::{StructDefinition, StructField, StructRepr},
        tycheck::lower::{DefTyLoweringCtx, TypeLowerer},
    },
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor { context };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl hir::HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::Struct(s) = &node.kind {
            self.collect_struct_fields(node.id, s);
        }
        hir::walk_declaration(self, node)
    }
}

impl<'ctx> Actor<'ctx> {
    fn parse_struct_repr(&self, id: hir::DefinitionID) -> StructRepr {
        let attrs = self.context.attributes_of(id);
        let mut repr = StructRepr::Taro;
        let mut seen_repr = false;

        for attr in attrs.iter() {
            if attr.as_known(self.context) != Some(hir::KnownAttribute::Repr) {
                continue;
            }

            if seen_repr {
                self.context.dcx().emit_error(
                    "duplicate @repr attribute on struct".into(),
                    Some(attr.span),
                );
                continue;
            }
            seen_repr = true;

            let Some(args) = &attr.args else {
                self.context.dcx().emit_error(
                    "@repr expects exactly one string literal argument (\"Taro\" or \"C\")".into(),
                    Some(attr.span),
                );
                continue;
            };

            if args.items.len() != 1 {
                self.context.dcx().emit_error(
                    "@repr expects exactly one string literal argument (\"Taro\" or \"C\")".into(),
                    Some(attr.span),
                );
                continue;
            }

            let hir::AttributeArg::Literal {
                value: hir::Literal::String(sym),
                ..
            } = &args.items[0]
            else {
                self.context.dcx().emit_error(
                    "@repr expects a string literal argument (\"Taro\" or \"C\")".into(),
                    Some(attr.span),
                );
                continue;
            };

            let value = self.context.symbol_text(*sym);
            if value.eq_ignore_ascii_case("taro") {
                repr = StructRepr::Taro;
            } else if value.eq_ignore_ascii_case("c") {
                repr = StructRepr::C;
            } else {
                self.context.dcx().emit_error(
                    format!(
                        "unknown @repr value \"{}\" (expected \"Taro\" or \"C\")",
                        value
                    )
                    .into(),
                    Some(attr.span),
                );
            }
        }

        repr
    }

    fn collect_struct_fields(&self, id: hir::DefinitionID, node: &hir::Struct) {
        let adt_ty = self.context.get_type(id);
        let crate::sema::models::TyKind::Adt(adt_def, _) = adt_ty.kind() else {
            unreachable!(
                "ICE: expected cached ADT type for struct {id:?}, got {:?}",
                adt_ty.kind()
            )
        };

        let ctx = DefTyLoweringCtx::new(id, self.context);
        let mut fields: Vec<StructField<'ctx>> = Vec::with_capacity(node.fields.len());
        for field in &node.fields {
            let ty = ctx.lowerer().lower_type(&field.ty);
            let visibility = self.context.definition_visibility(field.def_id);
            fields.push(StructField {
                name: field.identifier.symbol,
                ty,
                mutability: field.mutability,
                def_id: field.def_id,
                visibility,
            });
        }

        let repr = self.parse_struct_repr(id);
        let fields = self.context.store.arenas.global.alloc_slice_clone(&fields);
        let def = StructDefinition {
            adt_def,
            repr,
            fields,
        };
        self.context.cache_struct_definition(id, def);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        diagnostics::DiagnosticRecord,
        hir::DeclarationKind,
        test_support::{analyze_script, analyze_script_diagnostics},
    };

    fn has_error_message(diagnostics: &[DiagnosticRecord], needle: &str) -> bool {
        diagnostics.iter().any(|diag| diag.message.contains(needle))
    }

    #[test]
    fn struct_repr_defaults_to_taro() {
        analyze_script(
            "struct Boxed { value: int32; }\nfunc main() {}\n",
            |package, gcx| {
                let decl = package
                    .root
                    .declarations
                    .iter()
                    .find(|decl| decl.identifier.symbol.as_str() == "Boxed")
                    .expect("struct declaration");
                assert!(matches!(decl.kind, DeclarationKind::Struct(_)));
                assert_eq!(gcx.get_struct_definition(decl.id).repr, StructRepr::Taro);
            },
        );
    }

    #[test]
    fn struct_repr_accepts_case_insensitive_values() {
        analyze_script(
            "@repr(\"c\") struct CStyle { value: int32; }\n@repr(\"TaRo\") struct Packed { value: int32; }\nfunc main() {}\n",
            |package, gcx| {
                let c_decl = package
                    .root
                    .declarations
                    .iter()
                    .find(|decl| decl.identifier.symbol.as_str() == "CStyle")
                    .expect("CStyle declaration");
                let t_decl = package
                    .root
                    .declarations
                    .iter()
                    .find(|decl| decl.identifier.symbol.as_str() == "Packed")
                    .expect("Packed declaration");

                assert_eq!(gcx.get_struct_definition(c_decl.id).repr, StructRepr::C);
                assert_eq!(gcx.get_struct_definition(t_decl.id).repr, StructRepr::Taro);
            },
        );
    }

    #[test]
    fn repr_attribute_rejected_on_non_struct_declarations() {
        let diagnostics =
            analyze_script_diagnostics("@repr(\"C\")\nfunc not_a_struct() {}\nfunc main() {}\n");
        assert!(has_error_message(
            &diagnostics,
            "@repr is only allowed on struct declarations"
        ));
    }

    #[test]
    fn repr_attribute_rejects_missing_argument() {
        let diagnostics =
            analyze_script_diagnostics("@repr\nstruct MissingArg { value: int32; }\n");
        assert!(has_error_message(
            &diagnostics,
            "@repr expects exactly one string literal argument"
        ));
    }

    #[test]
    fn repr_attribute_rejects_non_string_argument() {
        let diagnostics = analyze_script_diagnostics("@repr(1)\nstruct BadArg { value: int32; }\n");
        assert!(has_error_message(
            &diagnostics,
            "@repr expects a string literal argument"
        ));
    }

    #[test]
    fn repr_attribute_rejects_multiple_arguments() {
        let diagnostics = analyze_script_diagnostics(
            "@repr(\"C\", \"Taro\")\nstruct TooMany { value: int32; }\n",
        );
        assert!(has_error_message(
            &diagnostics,
            "@repr expects exactly one string literal argument"
        ));
    }

    #[test]
    fn repr_attribute_rejects_unknown_value() {
        let diagnostics =
            analyze_script_diagnostics("@repr(\"Rust\")\nstruct BadRepr { value: int32; }\n");
        assert!(has_error_message(
            &diagnostics,
            "unknown @repr value \"Rust\""
        ));
    }
}
