use crate::{
    compile::context::GlobalContext,
    error::CompileResult,
    hir,
    sema::models::{StructDefinition, StructField, StructRepr},
};

pub fn run(package: &hir::Package, context: GlobalContext) -> CompileResult<()> {
    let mut actor = Actor {
        context,
        classes: vec![],
    };
    hir::walk_package(&mut actor, package);
    context.dcx().ok()?;
    super::class_hierarchy::flatten_fields(&actor.classes, context)?;
    for class in actor.classes {
        context.ensure_class_payload(context.get_type(class));
    }
    context.dcx().ok()
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    classes: Vec<hir::DefinitionID>,
}

impl hir::HirVisitor for Actor<'_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        if let hir::DeclarationKind::Struct(s) = &node.kind {
            if s.class_header.is_some() {
                self.classes.push(node.id);
            }
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

    fn parse_field_coding_metadata(
        &self,
        field: &hir::FieldDefinition,
    ) -> (Option<crate::span::Symbol>, bool) {
        let gcx = self.context;
        let field_name = gcx.symbol_text(field.identifier.symbol);
        let mut coding_key: Option<crate::span::Symbol> = None;
        let mut coding_skip = false;
        let mut key_span = None;
        let mut skip_span = None;

        for attr in &field.attributes {
            match attr.as_known(gcx) {
                Some(hir::KnownAttribute::Key) => {
                    if coding_key.is_some() {
                        gcx.dcx().emit_error(
                            format!("duplicate `@key` attribute on field `{field_name}`"),
                            Some(attr.span),
                        );
                        continue;
                    }
                    let Some(args) = &attr.args else {
                        gcx.dcx().emit_error(
                            "`@key` expects a single string literal argument".into(),
                            Some(attr.span),
                        );
                        continue;
                    };
                    if args.items.len() != 1 {
                        gcx.dcx().emit_error(
                            "`@key` expects a single string literal argument".into(),
                            Some(attr.span),
                        );
                        continue;
                    }
                    let hir::AttributeArg::Literal {
                        value: hir::Literal::String(sym),
                        ..
                    } = &args.items[0]
                    else {
                        gcx.dcx().emit_error(
                            "`@key` expects a single string literal argument".into(),
                            Some(attr.span),
                        );
                        continue;
                    };
                    coding_key = Some(*sym);
                    key_span = Some(attr.span);
                }
                Some(hir::KnownAttribute::Skip) => {
                    if coding_skip {
                        gcx.dcx().emit_error(
                            format!("duplicate `@skip` attribute on field `{field_name}`"),
                            Some(attr.span),
                        );
                        continue;
                    }
                    if attr.args.as_ref().is_some_and(|args| !args.items.is_empty()) {
                        gcx.dcx().emit_error(
                            "`@skip` on a field does not take arguments".into(),
                            Some(attr.span),
                        );
                        continue;
                    }
                    coding_skip = true;
                    skip_span = Some(attr.span);
                }
                _ => {
                    let attr_name = gcx.symbol_text(attr.identifier.symbol);
                    gcx.dcx().emit_error(
                        format!("attribute `@{attr_name}` is not allowed on a field"),
                        Some(attr.span),
                    );
                }
            }
        }

        if coding_key.is_some() && coding_skip {
            gcx.dcx().emit_error(
                format!("`@key` and `@skip` cannot be combined on field `{field_name}`"),
                key_span.or(skip_span),
            );
        }

        (coding_key, coding_skip)
    }

    fn collect_struct_fields(&self, id: hir::DefinitionID, node: &hir::Struct) {
        let adt_ty = self.context.get_type(id);
        let crate::sema::models::TyKind::Adt(adt_def, _) = adt_ty.kind() else {
            unreachable!(
                "ICE: expected cached ADT type for struct {id:?}, got {:?}",
                adt_ty.kind()
            )
        };

        let mut fields: Vec<StructField<'ctx>> = Vec::with_capacity(node.fields.len());
        for field in &node.fields {
            let ty = super::adt::lower_field(self.context, id, &field.ty);
            let visibility = self.context.definition_visibility(
                if node.positional { id } else { field.def_id },
            );
            let default_provider = field.default_value.as_ref().map(|expression| {
                let gcx = self.context;
                let provider = gcx.allocate_synthetic_id(gcx.package_index());
                // HIR is arena-owned for the compilation; the visitor borrow
                // is shorter than that allocation, as for parameter defaults.
                let expression: &'ctx hir::Expression =
                    unsafe { std::mem::transmute(&**expression) };
                gcx.register_default_value_expr(provider, expression, None);
                let signature = gcx.store.arenas.function_signatures.alloc(
                    crate::sema::models::LabeledFunctionSignature {
                        inputs: vec![],
                        output: ty,
                        is_variadic: false,
                        abi: None,
                    },
                );
                gcx.register_synthetic_definition(
                    provider,
                    crate::sema::models::SyntheticDefinition {
                        kind: crate::sema::models::SyntheticDefinitionKind::Ordinary,
                        name: gcx.intern_symbol(&format!(
                            "{}$field_default",
                            gcx.symbol_text(field.identifier.symbol)
                        )),
                        generics: gcx.generics_of(id),
                        signature,
                        span: field.span,
                    },
                );
                provider
            });
            let (coding_key, coding_skip) = self.parse_field_coding_metadata(field);
            fields.push(StructField {
                default_provider,
                name: field.identifier.symbol,
                ty,
                mutability: field.mutability,
                def_id: field.def_id,
                visibility,
                coding_key,
                coding_skip,
            });
        }

        if self.context.std_item_def(hir::StdItem::ClassHandle) == Some(id) {
            // NativeOwner extraction and implicit Copy lowering use this exact
            // private one-word ABI. Reject a malformed std before MIR exists.
            let valid = class_handle_layout_is_valid(self.context, id, &fields);
            if !valid {
                self.context.dcx().emit_error(
                    "ClassHandle requires one const uint8 pointer field and no generics or defaults".into(),
                    Some(self.context.definition_ident(id).span),
                );
            }
        }
        let repr = self.parse_struct_repr(id);
        let fields = self.context.store.arenas.global.alloc_slice_copy(&fields);
        let def = StructDefinition {
            // Class headers can be seeded before their fields are collected.
            class_info: self
                .context
                .try_get_struct_definition(id)
                .and_then(|definition| definition.class_info),
            adt_def,
            positional: node.positional,
            has_initializer: false,
            repr,
            fields,
        };
        self.context.cache_struct_definition(id, def);
    }
}

fn class_handle_layout_is_valid(
    gcx: GlobalContext<'_>,
    id: hir::DefinitionID,
    fields: &[StructField<'_>],
) -> bool {
    gcx.generics_of(id).total_count() == 0
        && fields.len() == 1
        && fields[0].default_provider.is_none()
        && fields[0].ty
            == crate::sema::models::Ty::new(
                crate::sema::models::TyKind::Pointer(gcx.types.uint8, hir::Mutability::Immutable),
                gcx,
            )
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
    fn class_handle_requires_its_exact_native_accounting_header() {
        analyze_script(
            "struct Good { owner: *const uint8 }\nstruct Mutable { owner: *mut uint8 }\nstruct WrongElement { owner: *const int32 }\nstruct Extra { owner: *const uint8; extra: usize }\nstruct Empty {}\nstruct Generic[T] { owner: *const uint8 }\nstruct Defaulted { owner: *const uint8 = unsafe { 0 as *const uint8 } }\nfunc main() {}",
            |package, gcx| {
                for declaration in &package.root.declarations {
                    if !matches!(declaration.kind, DeclarationKind::Struct(_)) {
                        continue;
                    }
                    let definition = gcx.get_struct_definition(declaration.id);
                    assert_eq!(
                        class_handle_layout_is_valid(gcx, declaration.id, definition.fields),
                        gcx.symbol_text(declaration.identifier.symbol).as_str() == "Good"
                    );
                }
            },
        );
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
                    .find(|decl| gcx.symbol_text(decl.identifier.symbol).as_str() == "Boxed")
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
                    .find(|decl| gcx.symbol_text(decl.identifier.symbol).as_str() == "CStyle")
                    .expect("CStyle declaration");
                let t_decl = package
                    .root
                    .declarations
                    .iter()
                    .find(|decl| gcx.symbol_text(decl.identifier.symbol).as_str() == "Packed")
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
