//! A single-file proof for bodies with no non-local semantic reads.

use std::{collections::BTreeMap, ops::ControlFlow, sync::Arc};

use rustc_hash::FxHashSet;

use crate::{
    hir::{self, HirVisitor},
    sema::resolve::{
        models::{PrimaryType, ResolutionError, ScopeNamespace},
        scope_lookup::resolve_in_scope,
    },
    span::{Identifier, Span},
};

use super::{
    Compiler, TimingReport,
    analysis_products::{AnalysisProduct, SourceRange},
    body_check::{
        BodyProduct, RequiresFullCheck, capture_body_diagnostics, check_selected_hir,
        loaded_dependency_keys,
    },
    context::Gcx,
    semantic_revision::{self, SemanticFileInput},
    source::{SourceText, SourceVersion},
};

/// Proof for the currently edited function. It owns its previous immutable
/// text and declaration facts without retaining any compiler arena.
pub struct ClosedBodyRevision {
    pub(super) version: SourceVersion,
    pub(super) fingerprint: blake3::Hash,
    pub(super) input: SemanticFileInput,
    pub(super) dependencies: BTreeMap<String, blake3::Hash>,
    pub(super) source: Arc<SourceText>,
    pub(super) body: super::declarations::BodyRecord,
    pub(super) primitives: FxHashSet<PrimaryType>,
}

impl ClosedBodyRevision {
    pub(super) fn capture(
        gcx: Gcx<'_>,
        function: &hir::Declaration,
        span: Span,
        checked: &BodyProduct,
        input: SemanticFileInput,
        dependencies: BTreeMap<String, blake3::Hash>,
    ) -> Option<Self> {
        let dcx = gcx.dcx();
        let version = dcx.sources().source_version()?;
        let source = dcx.get_file_content(span.file)?;
        let output = gcx.resolution_output(gcx.package_index());
        let file_scope = *output.file_scope_mapping.get(&span.file)?;
        let primitives = PrimaryType::ALL
            .into_iter()
            .filter(|primitive| {
                let name = Identifier::new(gcx.intern_symbol(primitive.name_str()), span);
                [file_scope, output.root_scope].into_iter().all(|scope| {
                    matches!(
                        resolve_in_scope(scope, name, ScopeNamespace::Type),
                        Err(ResolutionError::UnknownSymbol(_))
                    )
                })
            })
            .collect();
        if !ClosedGrammar::supports(function, &primitives) {
            return None;
        }
        Some(Self {
            version,
            fingerprint: checked.package_fingerprint,
            input,
            dependencies,
            source,
            body: checked.body.clone(),
            primitives,
        })
    }

    /// Ensure the whole edit is contained in this function body. A single
    /// notification can change several disjoint positions in the edited file.
    pub(super) fn same_surroundings(&self, source: &SourceText, new_body: Span) -> Option<()> {
        let old_start = self.source.byte_offset(self.body.source.start)?;
        let old_end = self.source.byte_offset(self.body.source.end)?;
        let new_start = source.byte_offset(new_body.start)?;
        let new_end = source.byte_offset(new_body.end)?;
        let before_matches =
            self.source.text().get(..old_start)? == source.text().get(..new_start)?;
        let after_matches = self.source.text().get(old_end..)? == source.text().get(new_end..)?;
        (before_matches && after_matches).then_some(())
    }
}

pub(super) fn matches_eager(actual: &BodyProduct, eager: &AnalysisProduct) -> bool {
    let inside = |range: &SourceRange| {
        range.path == actual.scope.path
            && actual.scope.start <= range.start
            && range.end <= actual.scope.end
    };
    eager.complete
        && eager.bodies.contains(&actual.body)
        && eager.declarations.contains(&actual.declaration)
        && eager
            .occurrences
            .iter()
            .filter(|fact| inside(&fact.source))
            .eq(&actual.occurrences)
        && eager
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.source.as_ref().is_some_and(inside))
            .eq(&actual.diagnostics)
}

impl Compiler<'_> {
    /// Check another revision of the same closed body using only its current
    /// file and the same hydrated dependencies. A workspace must attest a
    /// single text replacement with unchanged file membership. On failure
    /// the previous proof stays tied to its old source version.
    pub fn check_closed_body_edit(
        &mut self,
        previous: &mut ClosedBodyRevision,
    ) -> Result<BodyProduct, RequiresFullCheck> {
        use RequiresFullCheck::*;
        let gcx = self.context;
        let dcx = gcx.dcx();
        let sources = dcx.sources();
        if gcx.config.is_std_provider
            || gcx.config.harness_mode.is_enabled()
            || gcx.try_resolution_output(gcx.package_index()).is_some()
        {
            return Err(UnsupportedContext);
        }
        let version = sources.source_version().ok_or(UnavailablePackageInputs)?;
        let path = &previous.input.file.path;
        let update = sources.single_file_edit().ok_or(PackageChanged)?;
        if update.previous != previous.version || update.path != *path {
            return Err(PackageChanged);
        }

        dcx.enable_recording();
        self.initialize_source_package();
        let result = (|| {
            let (mut package, input) = self
                .parse_semantic_root_file(path)
                .ok_or(PackagePreparationFailed)?;
            if input != previous.input || loaded_dependency_keys(gcx)? != previous.dependencies {
                return Err(PackageChanged);
            }
            let file = &mut package.root.files[0];
            let index = file
                .declarations
                .iter()
                .position(|declaration| {
                    semantic_revision::ordinary_body(declaration)
                        .is_some_and(|body| body.start == previous.body.source.start)
                })
                .ok_or(UnsupportedDeclaration)?;
            let declaration = file.declarations.swap_remove(index);
            let span = declaration.span;
            let body =
                semantic_revision::ordinary_body(&declaration).ok_or(UnsupportedDeclaration)?;
            let source = dcx
                .get_file_content(file.id)
                .ok_or(UnavailablePackageInputs)?;
            previous
                .same_surroundings(&source, body)
                .ok_or(PackageChanged)?;
            file.declarations = vec![declaration];

            let mut timings = TimingReport::default();
            let package = self
                .lower_configured_package(package, &mut timings, false)
                .map_err(|_| PackagePreparationFailed)?;
            dcx.ok().map_err(|_| PackagePreparationFailed)?;
            if !matches!(package.root.declarations.as_slice(), [declaration]
                if ClosedGrammar::supports(declaration, &previous.primitives))
            {
                return Err(UnsupportedDeclaration);
            }
            crate::sema::tycheck::prepare_declarations(&package, gcx, &mut None)
                .map_err(|_| PackagePreparationFailed)?;
            let product = check_selected_hir(gcx, &package, span, previous.fingerprint)?;
            if product.declaration.anchor != previous.body.identity.owner {
                return Err(PackageChanged);
            }
            Ok((product, span, source))
        })();
        let diagnostics = dcx.take_recorded_diagnostics();
        let (mut product, span, source) = result?;
        capture_body_diagnostics(gcx, &mut product, span, diagnostics);
        previous.version = version;
        previous.source = source;
        previous.body = product.body.clone();
        Ok(product)
    }
}

pub(super) struct ClosedGrammar<'a> {
    primitives: &'a FxHashSet<PrimaryType>,
}

impl ClosedGrammar<'_> {
    pub(super) fn supports(
        declaration: &hir::Declaration,
        primitives: &FxHashSet<PrimaryType>,
    ) -> bool {
        let hir::DeclarationKind::Function(function) = &declaration.kind else {
            return false;
        };
        if function
            .signature
            .prototype
            .inputs
            .iter()
            .any(|param| param.default_value.is_some())
        {
            return false;
        }
        hir::walk_declaration(&mut ClosedGrammar { primitives }, declaration).is_continue()
    }
}

impl HirVisitor for ClosedGrammar<'_> {
    type Result = ControlFlow<()>;

    fn visit_expression(&mut self, expr: &hir::Expression) -> Self::Result {
        use hir::ExpressionKind::*;
        match &expr.kind {
            Path(hir::ResolvedPath::Resolved(path))
                if matches!(path.resolution, hir::Resolution::LocalVariable(_)) => {}
            Literal(literal) if !matches!(literal, hir::Literal::Nil) => {}
            Closure(closure) if !closure.is_async && !closure.implicit_await => {}
            // Within this grammar the only callable values are lexical
            // closures and concrete function pointers.
            Call { .. } | If(_) | Tuple(..) | Discard | Assign(..) | Return { .. } | Block(_) => {}
            _ => return ControlFlow::Break(()),
        }
        hir::walk_expression(self, expr)
    }

    fn visit_type(&mut self, ty: &hir::Type) -> Self::Result {
        use hir::TypeKind::*;
        match &ty.kind {
            Nominal(hir::ResolvedPath::Resolved(path))
                if matches!(path.resolution, hir::Resolution::PrimaryType(ty) if self.primitives.contains(&ty))
                    && path.segments.len() == 1
                    && path.segments[0].arguments.is_none() => {}
            Pointer(..) | Reference(_) | Tuple(..) | Function { .. } | Infer | Never => {}
            _ => return ControlFlow::Break(()),
        }
        hir::walk_type(self, ty)
    }

    fn visit_statement(&mut self, statement: &hir::Statement) -> Self::Result {
        match &statement.kind {
            hir::StatementKind::Variable(local) if !local.is_async => {}
            hir::StatementKind::Expression(_) => {}
            _ => return ControlFlow::Break(()),
        }
        hir::walk_statement(self, statement)
    }

    fn visit_pattern(&mut self, pattern: &hir::Pattern) -> Self::Result {
        match &pattern.kind {
            hir::PatternKind::Binding { .. }
            | hir::PatternKind::Wildcard
            | hir::PatternKind::Tuple(..) => {}
            _ => return ControlFlow::Break(()),
        }
        hir::walk_pattern(self, pattern)
    }
}

#[cfg(test)]
mod tests {
    use std::{
        cell::Cell,
        io,
        path::{Path, PathBuf},
        rc::Rc,
        sync::Arc,
    };

    use crate::{
        compile::{
            Compiler,
            analysis_products::AnalysisProduct,
            body_check::{BodyProduct, RequiresFullCheck},
            source::{
                DirectoryEntry, FileContents, FileOverlay, SingleFileEdit, SourceProvider,
                SourceText, SourceVersion, WorkspaceSources,
            },
        },
        span::Position,
        test_support::{TempDir, with_lint_warnings, with_workspace_compiler},
    };

    struct CountReads {
        sources: Rc<WorkspaceSources>,
        edited: PathBuf,
        unrelated_reads: Cell<usize>,
        directory_reads: Cell<usize>,
        bytes_read: Cell<usize>,
    }

    impl SourceProvider for CountReads {
        fn source_version(&self) -> Option<SourceVersion> {
            self.sources.source_version()
        }

        fn single_file_edit(&self) -> Option<&SingleFileEdit> {
            self.sources.single_file_edit()
        }

        fn workspace_revision(&self) -> Option<u64> {
            self.sources.workspace_revision()
        }

        fn resolve(&self, path: &Path) -> io::Result<PathBuf> {
            self.sources.resolve(path)
        }

        fn read_directory(&self, path: &Path) -> io::Result<Vec<DirectoryEntry>> {
            self.directory_reads.update(|count| count + 1);
            self.sources.read_directory(path)
        }

        fn read_file(&self, path: &Path) -> io::Result<FileContents> {
            let content = self.sources.read_file(path)?;
            if path != self.edited {
                self.unrelated_reads.update(|count| count + 1);
            }
            self.bytes_read
                .update(|count| count + content.as_bytes().len());
            Ok(content)
        }
    }

    fn source(text: &str) -> Arc<SourceText> {
        Arc::new(SourceText::new(text.to_owned()))
    }

    fn overlay(text: &str) -> FileOverlay {
        FileOverlay::Contents(FileContents::Text(source(text)))
    }

    fn fixture(value: u16) -> String {
        format!(
            "private func useLocal(_ input: int32) -> int32 {{\n    unused := {value}\n    read := () => input\n    read()\n}}"
        )
    }

    fn clean(root: &Path, sources: Rc<WorkspaceSources>) -> AnalysisProduct {
        with_lint_warnings(|| {
            with_workspace_compiler(root, sources, None, |compiler| compiler.analyze_owned(0))
        })
    }

    fn assert_same_body(actual: &BodyProduct, oracle: AnalysisProduct) {
        assert!(oracle.complete, "{:?}", oracle.diagnostics);
        assert!(oracle.bodies.contains(&actual.body));
        assert!(oracle.declarations.contains(&actual.declaration));
        let inside = |span: &crate::compile::analysis_products::SourceRange| {
            span.path == actual.scope.path
                && actual.scope.start <= span.start
                && span.end <= actual.scope.end
        };
        let facts = oracle
            .occurrences
            .into_iter()
            .filter(|fact| inside(&fact.source))
            .collect::<Vec<_>>();
        assert_eq!(actual.occurrences, facts);
        let diagnostics = oracle
            .diagnostics
            .into_iter()
            .filter(|diagnostic| diagnostic.source.as_ref().is_some_and(inside))
            .collect::<Vec<_>>();
        assert_eq!(actual.diagnostics, diagnostics);
    }

    fn prepare(
        root: &Path,
        sources: Rc<WorkspaceSources>,
        path: &Path,
    ) -> super::ClosedBodyRevision {
        let eager = clean(root, Rc::clone(&sources));
        with_lint_warnings(|| {
            with_workspace_compiler(root, sources, None, |compiler| {
                compiler
                    .prepare_closed_body_edit(path, Position::default(), &eager)
                    .unwrap()
            })
        })
    }

    #[test]
    fn local_edits_avoid_sibling_work_at_three_package_sizes() {
        let iris_bytes = [
            include_bytes!("../../../showcase/adex_iris/src/config/config.tr").len(),
            include_bytes!("../../../showcase/adex_iris/src/data/data.tr").len(),
            include_bytes!("../../../showcase/adex_iris/src/encoding/rate.tr").len(),
            include_bytes!("../../../showcase/adex_iris/src/main.tr").len(),
            include_bytes!("../../../showcase/adex_iris/src/model/network.tr").len(),
            include_bytes!("../../../showcase/adex_iris/src/model/neuron.tr").len(),
            include_bytes!("../../../showcase/adex_iris/src/random/random.tr").len(),
            include_bytes!("../../../showcase/adex_iris/src/training/training.tr").len(),
        ]
        .into_iter()
        .sum::<usize>();
        for (count, padding) in [
            (10, 0),
            (100, 0),
            (1_000, 0),
            (10, iris_bytes),
            (10, iris_bytes * 4),
            (10, iris_bytes * 16),
        ] {
            let root = TempDir::new("closed-body-scale");
            let path = root.join("src/focus.tr");
            let original = fixture(0);
            let overlays = std::iter::once((path.clone(), overlay(&original))).chain(
                (0..count).map(|index| {
                    let padding = "x".repeat(padding / count);
                    let src =
                        format!("private func unrelated{index}() -> int32 {{ 7 }}\n// {padding}\n");
                    (root.join(format!("src/module{index:04}.tr")), overlay(&src))
                }),
            );
            let mut workspace = Rc::new(WorkspaceSources::new(1, overlays).unwrap());
            let mut baseline = prepare(&root, Rc::clone(&workspace), &path);
            let mut seed = 3u16;
            for revision in 2..=4 {
                seed = seed.wrapping_mul(25173).wrapping_add(13849);
                let changed = fixture(seed);
                Rc::get_mut(&mut workspace)
                    .unwrap()
                    .replace_open_text(revision, &path, source(&changed))
                    .unwrap();
                let reads = Rc::new(CountReads {
                    sources: Rc::clone(&workspace),
                    edited: workspace.resolve(&path).unwrap(),
                    unrelated_reads: Cell::new(0),
                    directory_reads: Cell::new(0),
                    bytes_read: Cell::new(0),
                });
                let actual = with_lint_warnings(|| {
                    with_workspace_compiler(&root, reads.clone(), None, |compiler| {
                        let actual = compiler.check_closed_body_edit(&mut baseline).unwrap();
                        let work = &compiler.context.dcx().analysis_work;
                        assert_eq!(work.parsed_files.get(), 1);
                        assert_eq!(work.summarized_files.get(), 1);
                        assert_eq!(work.summarized_source_bytes.get(), changed.len());
                        assert_eq!(work.collected_callable_headers.get(), 1);
                        assert_eq!(work.checked_function_bodies.get(), 1);
                        assert_eq!(work.indexed_declarations.get(), 1);
                        assert_eq!(work.copied_occurrences.get(), actual.occurrences.len());
                        actual
                    })
                });
                assert_eq!(reads.unrelated_reads.get(), 0);
                assert_eq!(reads.directory_reads.get(), 0);
                assert!(reads.bytes_read.get() <= changed.len() * 3);
                let eager = with_lint_warnings(|| {
                    with_workspace_compiler(&root, workspace.clone(), None, |compiler| {
                        let eager = compiler.analyze_owned(revision);
                        let work = &compiler.context.dcx().analysis_work;
                        assert_eq!(work.parsed_files.get(), count + 1);
                        assert_eq!(work.collected_callable_headers.get(), count + 1);
                        assert_eq!(work.checked_function_bodies.get(), count + 1);
                        assert!(work.indexed_declarations.get() > count);
                        eager
                    })
                });
                assert_same_body(&actual, eager);
            }
        }
    }

    #[test]
    fn a_larger_edited_file_may_be_parsed_but_only_the_focus_is_checked() {
        let root = TempDir::new("closed-body-one-large-file");
        let path = root.join("src/focus.tr");
        let inactive = (0..1_000)
            .map(|index| format!("\nfunc sameFile{index}() {{ _ = 7 }}\n"))
            .collect::<String>();
        let original = format!("{}{inactive}", fixture(0));
        let mut workspace =
            Rc::new(WorkspaceSources::new(1, [(path.clone(), overlay(&original))]).unwrap());
        let mut baseline = prepare(&root, Rc::clone(&workspace), &path);
        let changed = format!("{}{inactive}", fixture(17));
        Rc::get_mut(&mut workspace)
            .unwrap()
            .replace_open_text(2, &path, source(&changed))
            .unwrap();
        let actual = with_lint_warnings(|| {
            with_workspace_compiler(&root, workspace.clone(), None, |compiler| {
                let product = compiler.check_closed_body_edit(&mut baseline).unwrap();
                let work = &compiler.context.dcx().analysis_work;
                assert_eq!(work.parsed_files.get(), 1);
                assert_eq!(work.summarized_source_bytes.get(), changed.len());
                assert_eq!(work.collected_callable_headers.get(), 1);
                assert_eq!(work.checked_function_bodies.get(), 1);
                assert_eq!(work.indexed_declarations.get(), 1);
                product
            })
        });
        assert_same_body(&actual, clean(&root, workspace));
    }

    #[test]
    fn a_structural_edit_or_untracked_revision_requires_full_analysis() {
        let root = TempDir::new("closed-body-invalidation");
        let path = root.join("src/focus.tr");
        let original = fixture(0);
        let mut workspace =
            Rc::new(WorkspaceSources::new(1, [(path.clone(), overlay(&original))]).unwrap());
        let mut baseline = prepare(&root, Rc::clone(&workspace), &path);
        let modified = format!("{}\nfunc another() {{}}", fixture(1));
        Rc::get_mut(&mut workspace)
            .unwrap()
            .replace_open_text(2, &path, source(&modified))
            .unwrap();
        let fallback = with_lint_warnings(|| {
            with_workspace_compiler(&root, workspace, None, |compiler| {
                compiler.check_closed_body_edit(&mut baseline)
            })
        });
        assert_eq!(fallback, Err(RequiresFullCheck::PackageChanged));

        let workspace = Rc::new(WorkspaceSources::new(3, [(path, overlay(&fixture(1)))]).unwrap());
        let fallback = with_lint_warnings(|| {
            with_workspace_compiler(&root, workspace, None, |compiler| {
                compiler.check_closed_body_edit(&mut baseline)
            })
        });
        assert_eq!(fallback, Err(RequiresFullCheck::PackageChanged));
    }

    #[test]
    fn independent_edit_histories_produce_the_same_body() {
        let root = TempDir::new("closed-body-history");
        let path = root.join("src/focus.tr");
        let run = |history: &[u16]| {
            let mut workspace =
                Rc::new(WorkspaceSources::new(1, [(path.clone(), overlay(&fixture(0)))]).unwrap());
            let mut baseline = prepare(&root, Rc::clone(&workspace), &path);
            let mut result = None;
            for (index, &value) in history.iter().enumerate() {
                Rc::get_mut(&mut workspace)
                    .unwrap()
                    .replace_open_text(2 + index as u64, &path, source(&fixture(value)))
                    .unwrap();
                let product = with_lint_warnings(|| {
                    with_workspace_compiler(
                        &root,
                        workspace.clone(),
                        None,
                        |compiler: &mut Compiler<'_>| {
                            compiler.check_closed_body_edit(&mut baseline).unwrap()
                        },
                    )
                });
                assert_same_body(&product, clean(&root, Rc::clone(&workspace)));
                result = Some(product);
            }
            result.unwrap()
        };
        assert_eq!(run(&[5, 17, 9]), run(&[100, 11, 9]));
    }

    #[test]
    fn a_builtin_spelling_shadowed_in_a_sibling_is_not_local() {
        let root = TempDir::new("closed-body-shadowed");
        let path = root.join("src/focus.tr");
        let sibling = root.join("src/sibling.tr");
        let original = "private func useLocal() { _ = 1 }";
        let mut workspace = Rc::new(
            WorkspaceSources::new(
                1,
                [
                    (path.clone(), overlay(original)),
                    (sibling, overlay("struct int32 {}")),
                ],
            )
            .unwrap(),
        );
        let mut baseline = prepare(&root, Rc::clone(&workspace), &path);
        Rc::get_mut(&mut workspace)
            .unwrap()
            .replace_open_text(
                2,
                &path,
                source("private func useLocal() { var local: int32 = 1; _ = local }"),
            )
            .unwrap();
        let fallback = with_lint_warnings(|| {
            with_workspace_compiler(&root, workspace.clone(), None, |compiler| {
                compiler.check_closed_body_edit(&mut baseline)
            })
        });
        assert_eq!(fallback, Err(RequiresFullCheck::UnsupportedDeclaration));
        let eager = clean(&root, workspace);
        assert!(!eager.complete);
        assert!(!eager.diagnostics.is_empty());
    }

    #[test]
    fn a_change_to_two_bodies_in_one_file_requires_full_analysis() {
        let root = TempDir::new("closed-body-multi-edit");
        let path = root.join("src/focus.tr");
        let text = |seed| format!("{}\nfunc sibling() {{ _ = {seed} }}\n", fixture(seed));
        let mut workspace =
            Rc::new(WorkspaceSources::new(1, [(path.clone(), overlay(&text(1)))]).unwrap());
        let mut baseline = prepare(&root, Rc::clone(&workspace), &path);
        Rc::get_mut(&mut workspace)
            .unwrap()
            .replace_open_text(2, &path, source(&text(2)))
            .unwrap();
        let fallback = with_lint_warnings(|| {
            with_workspace_compiler(&root, workspace, None, |compiler| {
                compiler.check_closed_body_edit(&mut baseline)
            })
        });
        assert_eq!(fallback, Err(RequiresFullCheck::PackageChanged));
    }
}
