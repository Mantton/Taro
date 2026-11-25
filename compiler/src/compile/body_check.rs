//! Isolated body checking with the package solver environment.

use std::{collections::BTreeMap, ops::ControlFlow, path::Path};

use crate::{
    hir::{self, HirVisitor},
    sema::{tycheck, validate},
    span::{Position, Span},
};

use super::{
    Compiler, TimingReport,
    analysis_products::{self, AnalysisDiagnostic, SourceRange, TypedOccurrence},
    context::Gcx,
    declarations::{BodyRecord, DeclarationRecord},
    semantic_revision::{self, PackageSemanticSummary},
};

/// Owned IDE facts for one checked declaration, including its lexical closures.
/// Package diagnostics and build state require a separate package analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BodyProduct {
    pub package_fingerprint: blake3::Hash,
    pub declaration: DeclarationRecord,
    pub body: BodyRecord,
    pub scope: SourceRange,
    pub occurrences: Vec<TypedOccurrence>,
    pub diagnostics: Vec<AnalysisDiagnostic>,
}

/// Conditions requiring the caller to check the package in a fresh scratch
/// session. A failed body check does not produce a reusable product.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RequiresFullCheck {
    UnsupportedContext,
    UnsupportedDeclaration,
    UnavailablePackageInputs,
    PackageChanged,
    PackagePreparationFailed,
    DeferredPackageValidation,
    BodyCheckFailed,
}

impl Compiler<'_> {
    /// Check the ordinary root function containing `position`, with scalar
    /// columns in the current source view. Use a fresh compiler with any
    /// dependencies already hydrated. The first implementation prepares all
    /// package headers, then invokes the same solver on the selected body.
    ///
    /// When rechecking an established revision, pass its fingerprint so a
    /// changed header, target, asset or dependency cannot produce a product.
    pub fn check_body_owned(
        &mut self,
        path: &Path,
        position: Position,
        expected_fingerprint: Option<blake3::Hash>,
    ) -> Result<BodyProduct, RequiresFullCheck> {
        let gcx = self.context;
        let dcx = gcx.dcx();
        dcx.enable_recording();
        let selected = self.check_body(path, position, expected_fingerprint);
        let diagnostics = dcx.take_recorded_diagnostics();
        let (mut product, span) = selected?;
        product.diagnostics = diagnostics
            .into_iter()
            .filter(|diagnostic| {
                diagnostic
                    .span
                    .is_some_and(|location| within(location, span))
            })
            .map(|diagnostic| {
                AnalysisDiagnostic::capture(gcx, diagnostic, std::slice::from_ref(&product.body))
            })
            .collect();
        Ok(product)
    }

    fn check_body(
        &mut self,
        path: &Path,
        position: Position,
        expected_fingerprint: Option<blake3::Hash>,
    ) -> Result<(BodyProduct, Span), RequiresFullCheck> {
        use RequiresFullCheck::*;
        let gcx = self.context;
        if gcx.config.is_std_provider
            || gcx.config.harness_mode.is_enabled()
            || gcx.try_resolution_output(gcx.package_index()).is_some()
        {
            return Err(UnsupportedContext);
        }
        let path = gcx
            .dcx()
            .sources()
            .resolve(path)
            .map_err(|_| UnsupportedDeclaration)?;
        let mut timings = TimingReport::default();
        let mut ast = self
            .parse_source_package(&mut timings, crate::parse::SyntaxMode::Strict)
            .map_err(|_| PackagePreparationFailed)?;
        self.filter_parsed_package(&mut ast, &mut timings);
        gcx.dcx().ok().map_err(|_| PackagePreparationFailed)?;
        let span = ast
            .root
            .files
            .iter()
            .find(|file| gcx.dcx().file_path(file.id).as_deref() == Some(&path))
            .and_then(|file| {
                file.declarations.iter().find(|declaration| {
                    declaration.span.start <= position && position < declaration.span.end
                })
            })
            .filter(|declaration| semantic_revision::ordinary_body(declaration).is_some())
            .map(|declaration| declaration.span)
            .ok_or(UnsupportedDeclaration)?;

        let summary =
            semantic_revision::summarize(gcx, &ast).map_err(|_| UnavailablePackageInputs)?;
        let fingerprint = fingerprint_with_loaded_dependencies(gcx, summary)?;
        if expected_fingerprint.is_some_and(|expected| expected != fingerprint) {
            return Err(PackageChanged);
        }
        let mut package = self
            .lower_configured_package(ast, &mut timings, false)
            .map_err(|_| PackagePreparationFailed)?;
        gcx.dcx().ok().map_err(|_| PackagePreparationFailed)?;
        let index = package
            .root
            .declarations
            .iter()
            .position(|declaration| declaration.span == span)
            .ok_or(UnsupportedDeclaration)?;
        if hir::walk_package(&mut DeferredValidation, &package).is_break() {
            return Err(DeferredPackageValidation);
        }
        tycheck::prepare_declarations(&package, gcx, &mut None)
            .map_err(|_| PackagePreparationFailed)?;
        if !gcx.store.constant_member_uses.borrow().is_empty()
            || gcx
                .store
                .lint_facts
                .borrow()
                .get(&gcx.package_index())
                .is_some_and(|facts| {
                    facts
                        .imports
                        .iter()
                        .any(|import| !import.interfaces.is_empty())
                })
        {
            return Err(DeferredPackageValidation);
        }
        super::entry::validate_entry_point(&package, gcx).map_err(|_| PackagePreparationFailed)?;

        let declaration = package.root.declarations.swap_remove(index);
        let selected_package = hir::Package {
            root: hir::Module {
                id: package.root.id,
                name: package.root.name,
                files: vec![span.file],
                declarations: vec![declaration],
                submodules: Vec::new(),
            },
        };
        let results =
            tycheck::check_prepared_bodies(&selected_package, gcx).map_err(|_| BodyCheckFailed)?;
        validate::validate_selected_body(&selected_package, gcx, &results, span)
            .map_err(|_| BodyCheckFailed)?;
        let (declaration, body, occurrences) = analysis_products::capture_function(
            gcx,
            &selected_package.root.declarations[0],
            &results,
        )
        .ok_or(UnsupportedDeclaration)?;
        let scope = SourceRange::capture(gcx, span).ok_or(UnsupportedDeclaration)?;
        Ok((
            BodyProduct {
                package_fingerprint: fingerprint,
                declaration,
                body,
                scope,
                occurrences,
                diagnostics: Vec::new(),
            },
            span,
        ))
    }
}

fn fingerprint_with_loaded_dependencies(
    gcx: Gcx<'_>,
    mut summary: PackageSemanticSummary,
) -> Result<blake3::Hash, RequiresFullCheck> {
    let packages = gcx.store.package_mapping.borrow();
    let identities = gcx.store.frozen_dependency_keys.borrow();
    let mut frozen = BTreeMap::new();
    for (name, index) in packages.iter() {
        if *name == gcx.config.identifier {
            continue;
        }
        let identity = identities
            .get(index)
            .ok_or(RequiresFullCheck::UnavailablePackageInputs)?;
        frozen.insert(name.to_string(), *identity);
    }

    // Type and conformance lookups can search loaded packages transitively.
    // Include every hydrated identity, including std and indirect imports.
    summary.dependencies.extend(frozen.keys().cloned());
    summary.dependencies.sort_unstable();
    summary.dependencies.dedup();
    let name = gcx.config.identifier.to_string();
    semantic_revision::resolve_package_fingerprints(
        &BTreeMap::from([(name.clone(), summary)]),
        &frozen,
    )
    .remove(&name)
    .ok_or(RequiresFullCheck::UnavailablePackageInputs)
}

fn within(inner: Span, outer: Span) -> bool {
    inner.file == outer.file && outer.start <= inner.start && inner.end <= outer.end
}

struct DeferredValidation;

impl HirVisitor for DeferredValidation {
    type Result = ControlFlow<()>;

    fn visit_function(
        &mut self,
        _id: hir::DefinitionID,
        function: &hir::Function,
        _context: hir::FunctionContext,
    ) -> Self::Result {
        // Other opaque bodies might publish hidden return types that this
        // solver normalizes. They are not available after header collection.
        if tycheck::opaque::opaque_return_bounds(function).is_some() {
            return ControlFlow::Break(());
        }
        ControlFlow::Continue(())
    }

    fn visit_constant(&mut self, constant: &hir::Constant) -> Self::Result {
        // These values are cached after checking the package's bodies.
        if constant
            .expr
            .as_ref()
            .is_some_and(|expr| crate::mir::const_eval::hir_expr_needs_mir_const_eval(expr))
        {
            return ControlFlow::Break(());
        }
        ControlFlow::Continue(())
    }
}

#[cfg(test)]
mod tests {
    use super::{BodyProduct, RequiresFullCheck};
    use crate::{
        PackageIndex,
        compile::{
            Compiler,
            analysis_products::SourceRange,
            context::Gcx,
            source::{FileContents, FileOverlay, SourceText, WorkspaceSources},
        },
        span::Position,
        test_support::{TempDir, with_lint_warnings, with_workspace_compiler},
    };
    use std::{path::Path, rc::Rc, sync::Arc};

    const CALLS: &str = include_str!("analysis_oracle/calls.tr");
    const DISPATCH: &str = include_str!("analysis_oracle/dispatch.tr");

    fn with_sources<R>(
        root: &Path,
        files: &[(&str, &str)],
        check: impl for<'ctx> FnOnce(&mut Compiler<'ctx>) -> R,
    ) -> R {
        let sources = files.iter().map(|(path, source)| {
            let source = Arc::new(SourceText::new((*source).into()));
            (
                root.join("src").join(path),
                FileOverlay::Contents(FileContents::Text(source)),
            )
        });
        let sources = Rc::new(WorkspaceSources::new(1, sources).unwrap());
        with_workspace_compiler(root, sources, None, check)
    }

    fn check(
        compiler: &mut Compiler<'_>,
        root: &Path,
        expected: Option<blake3::Hash>,
    ) -> Result<BodyProduct, RequiresFullCheck> {
        compiler.check_body_owned(&root.join("src/calls.tr"), Position::default(), expected)
    }

    fn inside(scope: &SourceRange, occurrence: &SourceRange) -> bool {
        scope.path == occurrence.path
            && scope.start <= occurrence.start
            && occurrence.end <= scope.end
    }

    #[test]
    fn selected_body_matches_full_overloads_closures_and_lints() {
        let root = TempDir::new("selected-body-differential");
        let decls = format!("{DISPATCH}\nfunc ignored() {{ local := true }}\n");
        let mut fingerprint = None;
        let mut overloads = Vec::new();
        for calls in [
            CALLS.into(),
            CALLS.replace("Cell[int64] = cell", "Cell[int32] = cell"),
        ] {
            let files = [
                ("dispatch.tr", decls.as_str()),
                ("calls.tr", calls.as_str()),
            ];
            let eager = with_lint_warnings(|| {
                with_sources(&root, &files, |compiler| compiler.analyze_owned(1))
            });
            assert!(eager.complete, "{:?}", eager.diagnostics);
            let product = with_lint_warnings(|| {
                with_sources(&root, &files, |compiler| {
                    let product = check(compiler, &root, fingerprint).unwrap();
                    let work = &compiler.context.dcx().analysis_work;
                    assert_eq!(work.parsed_files.get(), 2);
                    assert!(work.collected_callable_headers.get() > 1);
                    assert_eq!(work.checked_function_bodies.get(), 1);
                    product
                })
            });
            fingerprint = Some(product.package_fingerprint);
            assert!(eager.bodies.contains(&product.body));
            assert!(eager.declarations.contains(&product.declaration));
            let expected = eager
                .occurrences
                .into_iter()
                .filter(|occurrence| inside(&product.scope, &occurrence.source))
                .collect::<Vec<_>>();
            assert_eq!(product.occurrences, expected);
            let expected_warnings = eager
                .diagnostics
                .into_iter()
                .filter(|diagnostic| {
                    diagnostic
                        .source
                        .as_ref()
                        .is_some_and(|source| inside(&product.scope, source))
                })
                .collect::<Vec<_>>();
            assert!(!expected_warnings.is_empty());
            assert_eq!(product.diagnostics, expected_warnings);
            let closure_call = product
                .occurrences
                .iter()
                .filter_map(|occurrence| occurrence.declaration.as_ref())
                .filter(|declaration| declaration.name == "label")
                .last()
                .unwrap();
            overloads.push(closure_call.clone());
        }
        assert_ne!(overloads[0], overloads[1]);
    }

    #[test]
    fn changed_declarations_and_failed_lookups_require_a_package_check() {
        let root = TempDir::new("selected-body-invalidation");
        let initial = with_sources(
            &root,
            &[("calls.tr", CALLS), ("dispatch.tr", DISPATCH)],
            |compiler| check(compiler, &root, None).unwrap(),
        );
        let removed = DISPATCH.replace("    func label(_ n: string) -> int32 { 64 }\n", "");
        let files = [("calls.tr", CALLS), ("dispatch.tr", removed.as_str())];
        with_sources(&root, &files, |compiler| {
            assert_eq!(
                check(compiler, &root, Some(initial.package_fingerprint)),
                Err(RequiresFullCheck::PackageChanged)
            );
            assert_eq!(
                compiler
                    .context
                    .dcx()
                    .analysis_work
                    .checked_function_bodies
                    .get(),
                0
            );
        });
        with_sources(&root, &files, |compiler| {
            assert_eq!(
                check(compiler, &root, None),
                Err(RequiresFullCheck::BodyCheckFailed)
            );
        });
    }

    #[test]
    fn opaque_results_require_the_full_package_solver() {
        let root = TempDir::new("selected-body-opaque");
        let files = [
            ("calls.tr", "func read() -> int32 { 3 }"),
            (
                "other.tr",
                "interface Readable {}\nstruct Value {}\nconform Value to Readable {}\nfunc erased() -> some Readable { Value {} }",
            ),
        ];
        with_sources(&root, &files, |compiler| {
            assert_eq!(
                check(compiler, &root, None),
                Err(RequiresFullCheck::DeferredPackageValidation)
            );
        });
        with_sources(&root, &files, |compiler| {
            let eager = compiler.analyze_owned(1);
            assert!(eager.complete, "{:?}", eager.diagnostics);
        });
    }

    #[test]
    fn hydrated_constant_functions_are_part_of_the_body_context() {
        let dependency = TempDir::new("selected-body-dependency");
        let workspace = TempDir::new("selected-body-consumer");
        let freeze = |source| {
            with_sources(&dependency, &[("lib.tr", source)], |compiler| {
                let gcx = compiler.context;
                let mut config = gcx.config.clone();
                config.identifier = "test/dep".into();
                config.index = PackageIndex::new(2);
                let config = gcx.store.arenas.configs.alloc(config);
                let mut compiler = Compiler::new(*gcx, config);
                (compiler.freeze_dependency().unwrap(), config.clone())
            })
        };
        let (width_three, config) = freeze("public const func width() -> usize { 3 }");
        let (width_four, _) = freeze("public const func width() -> usize { 4 }");
        let files = [(
            "calls.tr",
            "func build() {\n    var items: [int32; dep::width()] = [1, 2, 3]\n    _ = items\n}",
        )];
        let run = |dependency, expected| {
            with_sources(&workspace, &files, |compiler| {
                let gcx = compiler.context;
                let arenas = gcx.store.arenas;
                let mut config = config.clone();
                let loaded = arenas.configs.alloc(config.clone());
                if let Some(snapshot) = dependency {
                    let snapshot: &crate::compile::frozen_dependencies::FrozenDependency = snapshot;
                    snapshot.hydrate(Gcx::new(*gcx, loaded)).unwrap();
                }
                config = gcx.config.clone();
                config.dependencies.insert("dep".into(), "test/dep".into());
                let mut compiler = Compiler::new(*gcx, arenas.configs.alloc(config));
                check(&mut compiler, &workspace, expected)
            })
        };
        let initial = run(Some(&width_three), None).unwrap();
        let expected = Some(initial.package_fingerprint);
        assert_eq!(run(Some(&width_three), expected), Ok(initial));
        assert_eq!(
            run(Some(&width_four), expected),
            Err(RequiresFullCheck::PackageChanged)
        );
        assert_eq!(
            run(None, expected),
            Err(RequiresFullCheck::UnavailablePackageInputs)
        );
    }
}
