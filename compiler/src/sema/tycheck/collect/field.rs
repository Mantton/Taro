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
        PackageIndex,
        compile::{
            Compiler, IdeAnalysisMode,
            config::{BuildProfile, Config, DebugOptions, PackageKind, StdMode},
            context::{CompilerArenas, CompilerContext, CompilerStore, Gcx},
        },
        diagnostics::{DiagCtx, DiagnosticRecord},
        hir::DeclarationKind,
        interner,
    };
    use rustc_hash::FxHashMap;
    use std::{
        fs::{create_dir_all, write},
        path::{Path, PathBuf},
        rc::Rc,
    };

    fn temp_dir(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "taro-repr-{name}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("time")
                .as_nanos()
        ));
        create_dir_all(&path).expect("temp dir");
        path
    }

    fn write_file(path: &Path, contents: &str) {
        if let Some(parent) = path.parent() {
            create_dir_all(parent).expect("parent dir");
        }
        write(path, contents).expect("write file");
    }

    fn make_script_config<'a>(
        icx: &'a CompilerContext<'a>,
        src: PathBuf,
        identifier: &str,
    ) -> &'a Config {
        icx.store.arenas.configs.alloc(Config {
            name: "script".into(),
            identifier: identifier.into(),
            src,
            dependencies: FxHashMap::default(),
            index: PackageIndex::new(1),
            kind: PackageKind::Executable,
            executable_out: None,
            no_std_prelude: true,
            is_script: true,
            profile: BuildProfile::Debug,
            overflow_checks: false,
            debug: DebugOptions {
                dump_mir: false,
                dump_llvm: false,
                timings: false,
            },
            test_mode: true,
            std_mode: StdMode::BootstrapStd,
            is_std_provider: false,
        })
    }

    fn analyze_script_diagnostics(source: &str) -> Vec<DiagnosticRecord> {
        interner::reset_session();

        let root = temp_dir("diagnostics");
        let output_root = root.join("target");
        create_dir_all(&output_root).expect("output root");
        let file = root.join("main.tr");
        write_file(&file, source);

        let dcx = Rc::new(DiagCtx::new(PathBuf::from(".")));
        dcx.enable_recording();
        let arenas = CompilerArenas::new();
        let store = CompilerStore::new(&arenas, output_root, &dcx, None, BuildProfile::Debug)
            .unwrap_or_else(|_| panic!("store"));
        let icx = CompilerContext::new(dcx.clone(), store);
        let config = make_script_config(&icx, file, "script-repr-diagnostics");

        let mut compiler = Compiler::new(&icx, config);
        let _ = compiler.analyze_for_ide(IdeAnalysisMode::OnType);
        dcx.take_recorded_diagnostics()
    }

    fn has_error_message(diagnostics: &[DiagnosticRecord], needle: &str) -> bool {
        diagnostics.iter().any(|diag| diag.message.contains(needle))
    }

    #[test]
    fn struct_repr_defaults_to_taro() {
        interner::reset_session();

        let root = temp_dir("default-repr");
        let output_root = root.join("target");
        create_dir_all(&output_root).expect("output root");
        let file = root.join("main.tr");
        write_file(&file, "struct Boxed { value: int32; }\nfunc main() {}\n");

        let dcx = Rc::new(DiagCtx::new(PathBuf::from(".")));
        let arenas = CompilerArenas::new();
        let store = CompilerStore::new(&arenas, output_root, &dcx, None, BuildProfile::Debug)
            .unwrap_or_else(|_| panic!("store"));
        let icx = CompilerContext::new(dcx, store);
        let config = make_script_config(&icx, file, "script-repr-default");
        let gcx = Gcx::new(&icx, config);

        let mut compiler = Compiler::new(&icx, config);
        let (package, _) = compiler
            .analyze()
            .unwrap_or_else(|_| panic!("analysis should succeed"));
        let decl = package
            .root
            .declarations
            .iter()
            .find(|decl| decl.identifier.symbol.as_str() == "Boxed")
            .expect("struct declaration");
        assert!(matches!(decl.kind, DeclarationKind::Struct(_)));
        assert_eq!(gcx.get_struct_definition(decl.id).repr, StructRepr::Taro);
    }

    #[test]
    fn struct_repr_accepts_case_insensitive_values() {
        interner::reset_session();

        let root = temp_dir("case-insensitive-repr");
        let output_root = root.join("target");
        create_dir_all(&output_root).expect("output root");
        let file = root.join("main.tr");
        write_file(
            &file,
            "@repr(\"c\") struct CStyle { value: int32; }\n\
             @repr(\"TaRo\") struct Packed { value: int32; }\n\
             func main() {}\n",
        );

        let dcx = Rc::new(DiagCtx::new(PathBuf::from(".")));
        let arenas = CompilerArenas::new();
        let store = CompilerStore::new(&arenas, output_root, &dcx, None, BuildProfile::Debug)
            .unwrap_or_else(|_| panic!("store"));
        let icx = CompilerContext::new(dcx, store);
        let config = make_script_config(&icx, file, "script-repr-case-insensitive");
        let gcx = Gcx::new(&icx, config);

        let mut compiler = Compiler::new(&icx, config);
        let (package, _) = compiler
            .analyze()
            .unwrap_or_else(|_| panic!("analysis should succeed"));

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
