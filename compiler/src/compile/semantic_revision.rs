//! Conservative package inputs for checking a body in isolation.

use std::{
    collections::BTreeMap,
    io,
    ops::ControlFlow,
    path::{Path, PathBuf},
};

use blake3::{Hash, Hasher};
use petgraph::{algo::kosaraju_scc, graph::DiGraph};

use crate::{
    ast::{self, AstVisitor},
    constants::{FILE_EXTENSION, MANIFEST_FILE, SOURCE_DIRECTORY},
    error::{CompileResult, ReportedError},
    parse::SyntaxMode,
    span::Span,
};

use super::{Compiler, TimingReport, config::StdMode, context::Gcx};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FileSemanticSummary {
    pub path: PathBuf,
    pub declarations: Hash,
    pub embedded_inputs: BTreeMap<PathBuf, Hash>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticFileInput {
    pub settings: Hash,
    pub file: FileSemanticSummary,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackageSemanticSummary {
    pub files: Vec<FileSemanticSummary>,
    pub settings: Hash,
    pub fingerprint: Hash,
    /// Canonical package identifiers. A package must have a validated input
    /// summary before its consumers can reuse body results.
    pub dependencies: Vec<String>,
}

impl PackageSemanticSummary {
    /// Compare a single file after validating workspace membership and the
    /// package's dependency revisions. No sibling source needs to be parsed.
    pub fn unchanged_file(&self, input: &SemanticFileInput) -> bool {
        self.settings == input.settings
            && self
                .files
                .binary_search_by(|file| file.path.cmp(&input.file.path))
                .is_ok_and(|index| self.files[index] == input.file)
    }
}

#[derive(Debug, Default)]
pub struct PackageRevisionTracker {
    fingerprint: Option<Hash>,
    revision: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PackageRevision {
    Known { revision: u64, changed: bool },
    RequiresFullCheck,
}

impl PackageRevisionTracker {
    pub fn update(&mut self, fingerprint: Option<Hash>) -> PackageRevision {
        let Some(fingerprint) = fingerprint else {
            self.fingerprint = None;
            return PackageRevision::RequiresFullCheck;
        };
        let changed = self.fingerprint != Some(fingerprint);
        if changed {
            self.revision = self
                .revision
                .checked_add(1)
                .expect("package revision exhausted");
            self.fingerprint = Some(fingerprint);
        }
        PackageRevision::Known {
            revision: self.revision,
            changed,
        }
    }
}

/// Combine source summaries with validated frozen dependency fingerprints.
/// A cycle, an unknown dependency, or dependence on either leaves a package
/// without a reusable revision. Independent packages still receive a key.
pub fn resolve_package_fingerprints(
    sources: &BTreeMap<String, PackageSemanticSummary>,
    frozen: &BTreeMap<String, Hash>,
) -> BTreeMap<String, Hash> {
    let mut graph = DiGraph::new();
    let nodes = sources
        .keys()
        .map(|name| (name.as_str(), graph.add_node(name.as_str())))
        .collect::<BTreeMap<_, _>>();
    for (name, source) in sources {
        for dependency in &source.dependencies {
            if let Some(&dependency) = nodes.get(dependency.as_str()) {
                graph.add_edge(nodes[name.as_str()], dependency, ());
            }
        }
    }

    // Edges point from consumers to their dependencies. SCCs returned in
    // reverse topological order visit dependencies before their consumers.
    let mut fingerprints = BTreeMap::new();
    for component in kosaraju_scc(&graph) {
        let [node] = component.as_slice() else {
            continue;
        };
        if graph.contains_edge(*node, *node) {
            continue;
        }
        let name = graph[*node];
        let summary = &sources[name];
        let mut hash = Hasher::new();
        hash.update(b"taro-package-closure-v1");
        hash.update(summary.fingerprint.as_bytes());
        let known = summary.dependencies.iter().all(|dependency| {
            let value = if sources.contains_key(dependency) {
                fingerprints.get(dependency)
            } else {
                frozen.get(dependency)
            };
            if let Some(value) = value {
                update_part(&mut hash, dependency.as_bytes());
                hash.update(value.as_bytes());
                true
            } else {
                false
            }
        });
        if known {
            fingerprints.insert(name.to_owned(), hash.finalize());
        }
    }
    fingerprints
}

impl Compiler<'_> {
    /// Summarize a fresh source view before typechecking. A syntax or input
    /// error means the caller must fall back to a package check.
    pub fn summarize_semantic_package(&self) -> CompileResult<PackageSemanticSummary> {
        let gcx = self.context;
        let mut timings = TimingReport::default();
        let mut package = self.parse_source_package(&mut timings, SyntaxMode::Strict)?;
        let target = crate::cfg_eval::target_info(gcx);
        crate::cfg_eval::filter_package(&mut package, &target, gcx);
        gcx.dcx().ok()?;

        summarize(gcx, &package).map_err(|message| {
            gcx.dcx().emit_error(message, None);
            ReportedError
        })
    }

    /// Summarize an edited root file in the same prepared package context.
    /// A module whose activation depends on siblings needs a package check.
    pub fn summarize_semantic_file(&self, path: &Path) -> Option<SemanticFileInput> {
        let gcx = self.context;
        let dcx = gcx.dcx();
        let sources = dcx.sources();
        let path = sources.resolve(path).ok()?;
        if path.extension()?.to_str()? != FILE_EXTENSION {
            return None;
        }
        if gcx.config.is_script {
            if path != sources.resolve(&gcx.config.src).ok()? {
                return None;
            }
        } else {
            let root = sources
                .resolve(&gcx.config.src.join(SOURCE_DIRECTORY))
                .ok()?;
            if path.parent()? != root {
                return None;
            }
        }
        let id = dcx.add_file_mapping(path.clone());
        let lexed = crate::parse::lexer::tokenize_file(
            id,
            path,
            dcx,
            Some(gcx.store.target_facts.triple()),
            SyntaxMode::Strict,
        )
        .ok()?;
        let mut file =
            crate::parse::parser::parse_root_file(lexed, dcx, gcx.config.lint_warnings).ok()?;
        crate::cfg_eval::filter_file(&mut file, &crate::cfg_eval::target_info(gcx), gcx);
        dcx.ok().ok()?;
        Some(SemanticFileInput {
            settings: summarize_settings(gcx).ok()?.0,
            file: summarize_file(gcx, &file).ok()?,
        })
    }
}

pub(super) fn summarize(
    gcx: Gcx<'_>,
    package: &ast::Package,
) -> Result<PackageSemanticSummary, String> {
    let mut visitor = SummaryVisitor {
        gcx,
        files: Vec::new(),
    };
    if let ControlFlow::Break(error) = ast::walk_package(&mut visitor, package) {
        return Err(error);
    }
    visitor
        .files
        .sort_unstable_by(|left, right| left.path.cmp(&right.path));
    let (settings, dependencies) = summarize_settings(gcx)?;
    let mut fingerprint = Hasher::new();
    fingerprint.update(b"taro-package-source-v1");
    fingerprint.update(settings.as_bytes());
    fingerprint.update(&(visitor.files.len() as u64).to_le_bytes());
    let mut embedded_inputs = BTreeMap::new();
    for file in &visitor.files {
        update_part(&mut fingerprint, file.path.as_os_str().as_encoded_bytes());
        fingerprint.update(file.declarations.as_bytes());
        fingerprint.update(&(file.embedded_inputs.len() as u64).to_le_bytes());
        for (path, digest) in &file.embedded_inputs {
            if let Some(previous) = embedded_inputs.insert(path, digest)
                && previous != digest
            {
                return Err(format!(
                    "embedded asset '{}' changed during analysis",
                    path.display()
                ));
            }
            update_part(&mut fingerprint, path.as_os_str().as_encoded_bytes());
            fingerprint.update(digest.as_bytes());
        }
    }
    Ok(PackageSemanticSummary {
        files: visitor.files,
        settings,
        fingerprint: fingerprint.finalize(),
        dependencies,
    })
}

fn summarize_settings(gcx: Gcx<'_>) -> Result<(Hash, Vec<String>), String> {
    let config = gcx.config;
    let mut aliases = config
        .dependencies
        .iter()
        .map(|(alias, package)| (alias.as_str(), package.as_str()))
        .collect::<Vec<_>>();
    aliases.sort_unstable();
    let mut dependencies = aliases
        .iter()
        .map(|(_, package)| (*package).to_owned())
        .collect::<Vec<_>>();
    if config.std_mode == StdMode::FullStd && !config.is_std_provider {
        dependencies.push("std".into());
    }
    dependencies.sort_unstable();
    dependencies.dedup();

    let settings = (
        &gcx.store.target_facts,
        config.identifier.as_str(),
        config.index.raw(),
        aliases,
        config.kind,
        config.profile,
        config.std_mode,
        config.harness_mode as u8,
        (
            config.is_script,
            config.is_std_provider,
            config.no_std_prelude,
            config.overflow_checks,
            config.lint_warnings,
        ),
    );
    let settings = bincode::serialize(&settings).map_err(|error| error.to_string())?;
    let mut fingerprint = Hasher::new();
    fingerprint.update(b"taro-package-settings-v1");
    update_part(&mut fingerprint, &settings);
    let manifest = if config.is_script {
        None
    } else {
        let path = config.src.join(MANIFEST_FILE);
        match gcx.dcx().sources().digest_file(&path) {
            Ok(digest) => Some(digest),
            Err(error) if error.kind() == io::ErrorKind::NotFound => None,
            Err(error) => {
                return Err(format!("cannot read manifest {}: {error}", path.display()));
            }
        }
    };
    update_part(
        &mut fingerprint,
        manifest
            .as_ref()
            .map_or(&[][..], |digest| digest.as_bytes()),
    );
    Ok((fingerprint.finalize(), dependencies))
}

fn update_part(hash: &mut Hasher, bytes: &[u8]) {
    hash.update(&(bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
}

struct SummaryVisitor<'ctx> {
    gcx: Gcx<'ctx>,
    files: Vec<FileSemanticSummary>,
}

impl AstVisitor for SummaryVisitor<'_> {
    type Result = ControlFlow<String>;

    fn visit_file(&mut self, file: &ast::File) -> Self::Result {
        match summarize_file(self.gcx, file) {
            Ok(summary) => self.files.push(summary),
            Err(error) => return ControlFlow::Break(error),
        }
        ControlFlow::Continue(())
    }
}

struct EmbeddedInputs<'ctx> {
    gcx: Gcx<'ctx>,
    assets: BTreeMap<PathBuf, Hash>,
}

impl AstVisitor for EmbeddedInputs<'_> {
    type Result = ControlFlow<String>;

    fn visit_expression(&mut self, expression: &ast::Expression) -> Self::Result {
        if let ast::ExpressionKind::Embed { path, bytes } = &expression.kind {
            let (file, contents) = match self.gcx.embedded_input(expression.span.file, path) {
                Ok(input) => input,
                Err(error) => return ControlFlow::Break(error),
            };
            let contents = contents.as_bytes();
            if !bytes && std::str::from_utf8(contents).is_err() {
                return ControlFlow::Break(format!("embedded asset '{path}' is not valid UTF-8"));
            }
            let digest = blake3::hash(contents);
            if let Some(previous) = self.assets.insert(file, digest)
                && previous != digest
            {
                return ControlFlow::Break(format!(
                    "embedded asset '{path}' changed during analysis"
                ));
            }
        }
        ast::walk_expression(self, expression)
    }
}

fn summarize_file(gcx: Gcx<'_>, file: &ast::File) -> Result<FileSemanticSummary, String> {
    let dcx = gcx.dcx();
    let path = dcx.file_path(file.id).ok_or("source file has no path")?;
    let source = dcx
        .get_file_content(file.id)
        .ok_or_else(|| format!("cannot read {}", path.display()))?;
    let mut embedded = EmbeddedInputs {
        gcx,
        assets: BTreeMap::new(),
    };
    if let ControlFlow::Break(error) = ast::walk_file(&mut embedded, file) {
        return Err(error);
    }
    let mut bodies = file
        .declarations
        .iter()
        .filter_map(ordinary_body)
        .collect::<Vec<_>>();
    bodies.sort_unstable_by_key(|span| span.start);
    let mut hash = Hasher::new();
    let mut cursor = 0;
    for span in bodies {
        let start = source
            .byte_offset(span.start)
            .ok_or("invalid function start")?;
        let end = source.byte_offset(span.end).ok_or("invalid function end")?;
        let header = source
            .text()
            .as_bytes()
            .get(cursor..start)
            .ok_or("overlapping function bodies")?;
        update_part(&mut hash, header);
        hash.update(b"ordinary-body");
        cursor = end;
    }
    let trailing = source
        .text()
        .as_bytes()
        .get(cursor..)
        .ok_or("invalid source boundary")?;
    update_part(&mut hash, trailing);
    Ok(FileSemanticSummary {
        path,
        declarations: hash.finalize(),
        embedded_inputs: embedded.assets,
    })
}

/// The first reusable category is an ordinary free function with a declared
/// result. The compiler will still check whether its body needs a package pass.
pub(super) fn ordinary_body(declaration: &ast::Declaration) -> Option<Span> {
    let ast::DeclarationKind::Function(function) = &declaration.kind else {
        return None;
    };
    if function.is_const
        || function.is_async
        || function.is_unsafe
        || function.abi.is_some()
        || !declaration.attributes.is_empty()
        || function.generics.type_parameters.is_some()
        || function.generics.where_clause.is_some()
        || function
            .signature
            .prototype
            .output
            .as_deref()
            .is_some_and(contains_opaque_type)
    {
        return None;
    }
    function.block.as_ref().map(|body| body.span)
}

fn contains_opaque_type(ty: &ast::Type) -> bool {
    struct FindOpaque;
    impl AstVisitor for FindOpaque {
        type Result = ControlFlow<()>;
        fn visit_type(&mut self, ty: &ast::Type) -> Self::Result {
            if matches!(ty.kind, ast::TypeKind::ImplTrait { .. }) {
                return ControlFlow::Break(());
            }
            ast::walk_type(self, ty)
        }
    }
    FindOpaque.visit_type(ty).is_break()
}

#[cfg(test)]
mod tests {
    use super::{
        BTreeMap, Hash, PackageRevision, PackageRevisionTracker, PackageSemanticSummary,
        resolve_package_fingerprints,
    };
    use crate::{
        compile::source::{FileContents, FileOverlay, SourceText, WorkspaceSources},
        test_support::{TempDir, with_workspace_compiler},
    };
    use std::{path::Path, rc::Rc, sync::Arc};

    fn summarize(
        root: &Path,
        files: &[(&str, &str)],
        target: Option<&str>,
    ) -> PackageSemanticSummary {
        let entries = files.iter().map(|(path, text)| {
            (
                root.join(path),
                FileOverlay::Contents(FileContents::Text(Arc::new(SourceText::new(
                    (*text).into(),
                )))),
            )
        });
        let view = Rc::new(WorkspaceSources::new(1, entries).unwrap());
        with_workspace_compiler(root, view, target.map(str::to_owned), |compiler| {
            compiler.summarize_semantic_package().unwrap_or_else(|_| {
                panic!("{:?}", compiler.context.dcx().take_recorded_diagnostics())
            })
        })
    }

    fn key(summary: &PackageSemanticSummary) -> Hash {
        let sources = BTreeMap::from([("test".into(), summary.clone())]);
        resolve_package_fingerprints(&sources, &BTreeMap::new())["test"]
    }

    #[test]
    fn ordinary_body_edits_keep_the_revision_and_observable_edits_advance_it() {
        let root = TempDir::new("semantic-revision");
        let source = "const LIMIT: int32 = 3\nfunc read(_ input: int32) -> int32 { input }";
        let original = summarize(&root, &[("src/read.tr", source)], None);
        let mut tracker = PackageRevisionTracker::default();
        assert_eq!(
            tracker.update(Some(key(&original))),
            PackageRevision::Known {
                revision: 1,
                changed: true,
            }
        );

        let body = source.replace("{ input }", "{\n    42\n}");
        let edited = summarize(&root, &[("src/read.tr", &body)], None);
        assert_eq!(edited.files, original.files);
        assert_eq!(
            tracker.update(Some(key(&edited))),
            PackageRevision::Known {
                revision: 1,
                changed: false,
            }
        );

        let constant = body.replace("LIMIT: int32 = 3", "LIMIT: int32 = 4");
        let edited = summarize(&root, &[("src/read.tr", &constant)], None);
        assert_eq!(
            tracker.update(Some(key(&edited))),
            PackageRevision::Known {
                revision: 2,
                changed: true,
            }
        );

        let overloaded = summarize(
            &root,
            &[
                ("src/read.tr", &constant),
                (
                    "src/overload.tr",
                    "func read(_ input: string) -> int32 { 0 }",
                ),
            ],
            None,
        );
        assert_eq!(overloaded.files.len(), 2);
        assert_eq!(
            tracker.update(Some(key(&overloaded))),
            PackageRevision::Known {
                revision: 3,
                changed: true,
            }
        );

        assert_eq!(tracker.update(None), PackageRevision::RequiresFullCheck);
        assert_eq!(
            tracker.update(Some(key(&overloaded))),
            PackageRevision::Known {
                revision: 4,
                changed: true,
            }
        );
    }

    #[test]
    fn one_root_file_can_be_compared_without_parsing_its_siblings() {
        let root = TempDir::new("semantic-file");
        let edited = root.join("src/edited.tr");
        let sibling = root.join("src/sibling.tr");
        let before = summarize(
            &root,
            &[
                ("src/edited.tr", "func edited() -> int32 { 1 }"),
                ("src/sibling.tr", "func sibling() -> int32 { 2 }"),
            ],
            None,
        );
        let contents = |text: &str| {
            FileOverlay::Contents(FileContents::Text(Arc::new(SourceText::new(text.into()))))
        };
        let view = Rc::new(
            WorkspaceSources::new(
                2,
                [
                    (edited.clone(), contents("func edited() -> int32 { 3 }")),
                    (sibling, contents("\"unterminated")),
                ],
            )
            .unwrap(),
        );
        with_workspace_compiler(&root, view, None, |compiler| {
            let input = compiler
                .summarize_semantic_file(&edited)
                .expect("root file can be summarized independently");
            assert!(before.unchanged_file(&input));
            let diagnostics = compiler.context.dcx();
            assert_eq!(diagnostics.analysis_work.parsed_files.get(), 1);
            assert!(!diagnostics.has_error());
        });
    }

    #[test]
    fn observes_manifests_compile_time_and_opaque_bodies_and_embedded_bytes() {
        let root = TempDir::new("semantic-inputs");
        let sources = "const func width() -> int32 { 1 }\n\
                       interface Marker {}\n\
                       struct Item {}\n\
                       func make() -> some Marker { Item {} }\n\
                       func asset() -> string { #embed(\"asset.txt\") }";
        let manifest = "[package]\nname = 'example.org/test/app'\nkind = 'library'\n";
        let read = |source: &str, asset: &str, manifest: &str| {
            summarize(
                &root,
                &[
                    ("src/lib.tr", source),
                    ("src/asset.txt", asset),
                    ("package.toml", manifest),
                ],
                None,
            )
        };
        let original = read(sources, "first asset", manifest);
        let changed_asset = read(sources, "second asset", manifest);
        assert_eq!(
            changed_asset.files[0].declarations,
            original.files[0].declarations
        );
        assert_ne!(key(&original), key(&changed_asset));
        assert_ne!(
            key(&original),
            key(&read(
                sources,
                "first asset",
                &manifest.replace("library", "binary")
            )),
        );
        assert_ne!(
            key(&original),
            key(&read(
                &sources.replace("{ 1 }", "{ 2 }"),
                "first asset",
                manifest
            )),
        );
        assert_ne!(
            key(&original),
            key(&read(
                &sources.replace("{ Item {} }", "{ return Item {} }"),
                "first asset",
                manifest
            )),
        );
    }

    #[cfg(feature = "llvm")]
    #[test]
    fn target_facts_change_the_package_revision_without_changing_its_files() {
        let root = TempDir::new("semantic-target");
        let files = &[("src/lib.tr", "func word() -> isize { 3 }")];
        let wide = summarize(&root, files, Some("x86_64-unknown-linux-gnu"));
        let narrow = summarize(&root, files, Some("i686-unknown-linux-gnu"));
        assert_eq!(wide.files, narrow.files);
        assert_ne!(key(&wide), key(&narrow));
    }

    #[test]
    fn dependency_changes_propagate_and_cycles_invalidate_only_consumers() {
        let summary = |name: &str, dependencies: &[&str]| PackageSemanticSummary {
            files: Vec::new(),
            settings: blake3::hash(b"settings"),
            fingerprint: blake3::hash(name.as_bytes()),
            dependencies: dependencies.iter().map(|name| (*name).into()).collect(),
        };
        let mut sources = BTreeMap::from([
            ("a".into(), summary("a", &["b"])),
            ("b".into(), summary("b", &["c"])),
            ("c".into(), summary("c", &["b"])),
            ("d".into(), summary("d", &[])),
            ("e".into(), summary("e", &["missing"])),
            ("f".into(), summary("f", &["f"])),
        ]);
        let frozen = BTreeMap::new();
        let cyclic = resolve_package_fingerprints(&sources, &frozen);
        assert_eq!(cyclic.keys().collect::<Vec<_>>(), vec!["d"]);
        sources.insert("c".into(), summary("c", &["std"]));
        let old_std = BTreeMap::from([("std".into(), blake3::hash(b"std one"))]);
        let revised_std = BTreeMap::from([("std".into(), blake3::hash(b"std two"))]);
        let old = resolve_package_fingerprints(&sources, &old_std);
        let new = resolve_package_fingerprints(&sources, &revised_std);
        for name in ["a", "b", "c"] {
            assert_ne!(old[name], new[name]);
        }
        assert_eq!(old["d"], new["d"]);
        assert!(!old.contains_key("e"));
        assert!(!old.contains_key("f"));
    }
}
