use crate::{
    PackageIndex,
    compile::{
        Compiler, IdeAnalysis, IdeAnalysisMode, IdeAnalysisStatus,
        config::{BuildProfile, Config, DebugOptions, PackageKind, StdMode},
        context::{CompilerArenas, CompilerContext, CompilerStore, Gcx},
    },
    constants::{MANIFEST_FILE, STD_PACKAGE_PATH, STD_PREFIX},
    diagnostics::{DiagCtx, DiagnosticRecord},
    hir::{
        self, AssociatedDeclaration, AssociatedDeclarationKind, Declaration, DeclarationKind,
        DefinitionID, Expression, ExpressionField, ExpressionKind, FieldDefinition, HirVisitor,
        Module, PathSegment, Pattern, PatternKind, PatternPath, Resolution, ResolvedPath,
        StructLiteral, Type, UseTree, UseTreeAlias, UseTreeKind, Variant, walk_assoc_declaration,
        walk_declaration, walk_expression, walk_path_segment, walk_pattern, walk_resolved_path,
        walk_type, walk_use_tree,
    },
    interner,
    metadata::{self, MetadataLoadStatus, ReuseMode},
    package::{discover, manifest::Manifest, readonly, utils::normalize_module_path},
    sema::{
        models::{AdtKind, StructField, Ty, TyKind},
        resolve::models::{
            DefinitionKind, PrimaryType, Resolution as AnyResolution, Scope, TypeHead,
        },
        tycheck::results::TypeCheckResults,
    },
    span::{FileID, Position, Span},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::cmp::Ordering;
use std::path::{Path, PathBuf};
use std::rc::Rc;

pub use crate::ide_completion::{
    CompletionContext, CompletionProbeOverlay, build_completion_probe_overlay,
    completion_context_at, filter_completion_items_by_prefix,
};

// --- Public types matching LSP expectations ---

#[derive(Debug, Clone, Copy)]
pub enum AnalysisMode {
    OnType,
    OnSave,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AnalysisOwner {
    Package(PathBuf),
    Script(PathBuf),
}

impl AnalysisOwner {
    pub fn path(&self) -> &Path {
        match self {
            AnalysisOwner::Package(path) | AnalysisOwner::Script(path) => path.as_path(),
        }
    }
}

pub struct SourceOverlay {
    pub path: PathBuf,
    pub content: String,
}

pub struct AnalysisRequest {
    pub mode: AnalysisMode,
    pub overlays: Vec<SourceOverlay>,
}

#[derive(Debug, Clone)]
pub struct HoverInfo {
    pub span: Span,
    pub contents: String,
}

#[derive(Debug, Clone)]
pub struct DefinitionInfo {
    pub source: Span,
    pub target: Span,
}

#[derive(Debug, Clone)]
pub struct FileMapping {
    pub file: FileID,
    pub path: PathBuf,
}

#[derive(Debug, Clone, Default)]
pub struct NavigationData {
    pub hovers: Vec<HoverInfo>,
    pub hover_parents: Vec<Option<usize>>,
    pub definitions: Vec<DefinitionInfo>,
    pub definition_parents: Vec<Option<usize>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ReferenceKey {
    Definition(DefinitionID),
    Local(hir::NodeID),
}

#[derive(Debug, Clone)]
pub struct ReferenceInfo {
    pub span: Span,
    pub is_declaration: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DocumentSymbolKind {
    Namespace,
    Struct,
    Enum,
    Interface,
    Function,
    Method,
    Field,
    Property,
    EnumMember,
    TypeAlias,
    Constant,
    Variable,
    Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocumentSymbolInfo {
    pub name: String,
    pub detail: Option<String>,
    pub kind: DocumentSymbolKind,
    pub span: Span,
    pub selection_span: Span,
    pub children: Vec<DocumentSymbolInfo>,
}

#[derive(Debug, Clone, Default)]
pub struct DocumentSymbolData {
    items: Vec<DocumentSymbolInfo>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SemanticTokenKind {
    Namespace,
    Type,
    Struct,
    Enum,
    Interface,
    TypeParameter,
    Function,
    Method,
    Property,
    Variable,
    Parameter,
    EnumMember,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SemanticTokenModifiers {
    pub declaration: bool,
    pub readonly: bool,
    pub static_member: bool,
    pub async_member: bool,
    pub default_library: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SemanticTokenInfo {
    pub span: Span,
    pub kind: SemanticTokenKind,
    pub modifiers: SemanticTokenModifiers,
}

#[derive(Debug, Clone, Default)]
pub struct SemanticTokenData {
    items: Vec<SemanticTokenInfo>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InlayHintKind {
    Type,
    Parameter,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InlayHintInfo {
    pub position: Position,
    pub file: FileID,
    pub label: String,
    pub kind: InlayHintKind,
}

#[derive(Debug, Clone, Default)]
pub struct InlayHintData {
    items: Vec<InlayHintInfo>,
}

#[derive(Debug, Clone)]
struct ReferenceMention {
    key: ReferenceKey,
    span: Span,
}

#[derive(Debug, Clone)]
struct ReferenceGroup {
    key: ReferenceKey,
    items: Vec<ReferenceInfo>,
}

#[derive(Debug, Clone, Default)]
pub struct ReferenceData {
    groups: Vec<ReferenceGroup>,
    mentions: Vec<ReferenceMention>,
    parents: Vec<Option<usize>>,
}

#[derive(Debug, Clone, Copy, Default)]
pub struct AnalysisStatus {
    pub hir_available: bool,
    pub typed_available: bool,
}

#[derive(Debug, Clone)]
pub struct SignatureCandidate {
    pub label: String,
    pub parameters: Vec<String>,
}

#[derive(Debug, Clone, Default)]
pub struct SignatureHelpData {
    sites: Vec<SignatureHelpSite>,
    parents: Vec<Option<usize>>,
}

#[derive(Debug, Clone)]
struct SignatureHelpSite {
    span: Span,
    arguments: Vec<Span>,
    signatures: Vec<SignatureCandidate>,
}

#[derive(Debug, Clone)]
pub struct SignatureHelpResult {
    pub signatures: Vec<SignatureCandidate>,
    pub active_signature: usize,
    pub active_parameter: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompletionKind {
    Function,
    Method,
    Struct,
    Enum,
    Interface,
    Module,
    Namespace,
    Field,
    Variant,
    Variable,
    Constant,
    Property,
    TypeAlias,
    TypeParameter,
    Keyword,
    Type,
    Package,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CompletionInfo {
    pub label: String,
    pub kind: CompletionKind,
    pub detail: Option<String>,
}

#[derive(Debug, Clone, Default)]
pub struct CompletionData {
    scopes: Vec<CompletionScope>,
    member_sites: Vec<MemberCompletionSite>,
}

#[derive(Debug, Clone)]
struct CompletionScope {
    span: Span,
    items: Vec<CompletionInfo>,
}

#[derive(Debug, Clone)]
struct MemberCompletionSite {
    span: Span,
    items: Vec<CompletionInfo>,
}

#[derive(Debug, Clone, Default)]
pub struct AnalysisSnapshot {
    pub diagnostics: Vec<DiagnosticRecord>,
    pub navigation: NavigationData,
    pub references: ReferenceData,
    pub document_symbols: DocumentSymbolData,
    pub semantic_tokens: SemanticTokenData,
    pub inlay_hints: InlayHintData,
    pub signatures: SignatureHelpData,
    pub completions: CompletionData,
    pub status: AnalysisStatus,
    pub file_mappings: Vec<FileMapping>,
    pub file_lookup: FxHashMap<PathBuf, FileID>,
}

#[derive(Debug, Clone, Default)]
struct IdeArtifacts {
    navigation: NavigationData,
    references: ReferenceData,
    document_symbols: DocumentSymbolData,
    semantic_tokens: SemanticTokenData,
    inlay_hints: InlayHintData,
    signatures: SignatureHelpData,
    completions: CompletionData,
    status: AnalysisStatus,
}

// --- Analysis entry point ---

pub fn resolve_analysis_owner(
    path: PathBuf,
    _std_path: Option<PathBuf>,
) -> Result<AnalysisOwner, String> {
    let file_path = path
        .canonicalize()
        .map_err(|e| format!("failed to canonicalize '{}': {}", path.display(), e))?;

    if let Some(root) = discover::resolve_package_root(&file_path)? {
        return Ok(AnalysisOwner::Package(root));
    }

    Ok(AnalysisOwner::Script(file_path))
}

pub fn analyze_file_for_ide(
    path: PathBuf,
    request: AnalysisRequest,
    std_path: Option<PathBuf>,
) -> Result<AnalysisSnapshot, String> {
    let owner = resolve_analysis_owner(path, std_path.clone())?;
    analyze_owner_for_ide(owner, request, std_path)
}

pub fn analyze_script_file_for_ide(
    path: PathBuf,
    request: AnalysisRequest,
    std_path: Option<PathBuf>,
) -> Result<AnalysisSnapshot, String> {
    analyze_file_for_ide(path, request, std_path)
}

pub fn analyze_owner_for_ide(
    owner: AnalysisOwner,
    request: AnalysisRequest,
    std_path: Option<PathBuf>,
) -> Result<AnalysisSnapshot, String> {
    interner::reset_session();

    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let dcx = Rc::new(DiagCtx::new(cwd));
    dcx.enable_recording();

    // Apply content overrides
    for overlay in &request.overlays {
        if let Ok(canonical) = overlay.path.canonicalize() {
            dcx.set_content_override(canonical, overlay.content.clone());
        }
        // Also set the non-canonical path in case canonicalize fails
        dcx.set_content_override(overlay.path.clone(), overlay.content.clone());
    }

    let result = run_analysis(&dcx, &owner, request.mode, std_path);

    // Always collect diagnostics, even on failure
    let diagnostics = dcx.take_recorded_diagnostics();
    let file_mappings: Vec<FileMapping> = dcx
        .all_file_mappings()
        .into_iter()
        .map(|(file, path)| FileMapping { file, path })
        .collect();
    let file_lookup = file_mappings
        .iter()
        .map(|mapping: &FileMapping| (mapping.path.clone(), mapping.file))
        .collect();

    match result {
        Ok(artifacts) => Ok(AnalysisSnapshot {
            diagnostics,
            navigation: artifacts.navigation,
            references: artifacts.references,
            document_symbols: artifacts.document_symbols,
            semantic_tokens: artifacts.semantic_tokens,
            inlay_hints: artifacts.inlay_hints,
            signatures: artifacts.signatures,
            completions: artifacts.completions,
            status: artifacts.status,
            file_mappings,
            file_lookup,
        }),
        Err(err) => {
            // Return partial snapshot with whatever diagnostics were collected
            // If there are recorded diagnostics, use them; otherwise surface the error
            let mut snapshot_diagnostics = diagnostics;
            if snapshot_diagnostics.is_empty() {
                snapshot_diagnostics.push(DiagnosticRecord {
                    message: err,
                    span: None,
                    level: crate::diagnostics::DiagnosticLevel::Error,
                    code: None,
                    stage: crate::diagnostics::DiagnosticStage::General,
                    related_info: vec![],
                });
            }
            Ok(AnalysisSnapshot {
                diagnostics: snapshot_diagnostics,
                navigation: NavigationData::default(),
                references: ReferenceData::default(),
                document_symbols: DocumentSymbolData::default(),
                semantic_tokens: SemanticTokenData::default(),
                inlay_hints: InlayHintData::default(),
                signatures: SignatureHelpData::default(),
                completions: CompletionData::default(),
                status: AnalysisStatus::default(),
                file_mappings,
                file_lookup,
            })
        }
    }
}

fn run_analysis(
    dcx: &Rc<DiagCtx>,
    owner: &AnalysisOwner,
    mode: AnalysisMode,
    std_path: Option<PathBuf>,
) -> Result<IdeArtifacts, String> {
    let target_root = ide_target_dir(owner.path());
    std::fs::create_dir_all(&target_root).map_err(|e| {
        format!(
            "failed to create target directory '{}': {}",
            target_root.display(),
            e
        )
    })?;

    let arenas = CompilerArenas::new();
    let store = CompilerStore::new(
        &arenas,
        target_root.join("objects"),
        dcx,
        None, // use host target
        BuildProfile::Debug,
    )
    .map_err(|_| "failed to create compiler store".to_string())?;
    let icx = CompilerContext::new(dcx.clone(), store);

    match owner {
        AnalysisOwner::Script(file_path) => analyze_script_owner(&icx, file_path, mode, std_path),
        AnalysisOwner::Package(package_root) => {
            analyze_package_owner(&icx, package_root, mode, std_path)
        }
    }
}

fn analyze_script_owner<'a>(
    icx: &'a CompilerContext<'a>,
    file_path: &Path,
    mode: AnalysisMode,
    std_path: Option<PathBuf>,
) -> Result<IdeArtifacts, String> {
    let file_path = file_path
        .canonicalize()
        .map_err(|e| format!("failed to canonicalize '{}': {}", file_path.display(), e))?;
    let file_stem = file_path
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| format!("failed to extract filename from '{}'", file_path.display()))?
        .to_string();

    compile_std_for_ide(icx, std_path)?;

    let package_index = PackageIndex::new(1);
    let mut dependencies = FxHashMap::default();
    dependencies.insert("std".into(), "std".into());

    let config = icx.store.arenas.configs.alloc(Config {
        name: file_stem.into(),
        identifier: format!(
            "script-{}",
            file_path.file_stem().unwrap().to_string_lossy()
        )
        .into(),
        src: file_path,
        dependencies,
        index: package_index,
        kind: PackageKind::Executable,
        executable_out: None,
        no_std_prelude: false,
        is_script: true,
        profile: BuildProfile::Debug,
        codegen: Default::default(),
        overflow_checks: false,
        debug: DebugOptions {
            dump_mir: false,
            dump_llvm: false,
            timings: false,
            debug_info: Default::default(),
        },
        harness_mode: Default::default(),
        std_mode: StdMode::FullStd,
        is_std_provider: false,
    });

    let gcx = Gcx::new(icx, config);
    let mut compiler = Compiler::new(icx, config);
    let IdeAnalysis {
        package,
        results,
        status,
    } = compiler
        .analyze_for_ide(compile_ide_mode(mode))
        .map_err(|_| String::new())?;
    let file_paths = icx.dcx.all_file_mappings().into_iter().collect();
    let module_targets = build_module_target_map(&package.root, &file_paths);

    Ok(collect_ide_artifacts(
        gcx,
        &package,
        results.as_ref(),
        &module_targets,
        analysis_status(status),
    ))
}

fn analyze_package_owner<'a>(
    icx: &'a CompilerContext<'a>,
    package_root: &Path,
    mode: AnalysisMode,
    std_path: Option<PathBuf>,
) -> Result<IdeArtifacts, String> {
    let package_root = package_root
        .canonicalize()
        .map_err(|e| format!("failed to canonicalize '{}': {}", package_root.display(), e))?;
    let is_std_package = is_std_package_root(&package_root, std_path.clone())?;

    if !is_std_package {
        compile_std_for_ide(icx, std_path)?;
    }

    let packages = readonly::load_package_graph(&package_root)?;
    if packages.is_empty() {
        return Err(format!(
            "no packages found for '{}'",
            package_root.display()
        ));
    }

    let total = packages.len();
    for (index, package) in packages.iter().enumerate() {
        let is_root = index + 1 == total;
        if !is_root && !matches!(package.kind, PackageKind::Library | PackageKind::Both) {
            return Err(format!(
                "dependency `{}` must be a library (found {:?})",
                package.package_path, package.kind
            ));
        }

        let is_std_provider = is_root && is_std_package;
        let mut dependencies = package.dependencies.clone();
        if !is_std_provider {
            dependencies.insert("std".into(), "std".into());
        }

        let package_index = if is_std_provider {
            PackageIndex::new(0)
        } else {
            PackageIndex::new(index + 1)
        };
        let identifier = if is_std_provider {
            STD_PREFIX.into()
        } else {
            package.unique_identifier()?.into()
        };

        let config = icx.store.arenas.configs.alloc(Config {
            name: package.display_name.clone().into(),
            identifier,
            src: package.root.clone(),
            dependencies,
            index: package_index,
            kind: package.kind,
            executable_out: None,
            no_std_prelude: package.no_std_prelude,
            is_script: false,
            profile: BuildProfile::Debug,
            codegen: Default::default(),
            overflow_checks: false,
            debug: DebugOptions {
                dump_mir: false,
                dump_llvm: false,
                timings: false,
                debug_info: Default::default(),
            },
            harness_mode: Default::default(),
            std_mode: if is_std_provider {
                StdMode::BootstrapStd
            } else {
                StdMode::FullStd
            },
            is_std_provider,
        });

        let mut compiler = Compiler::new(icx, config);
        if is_root {
            let gcx = Gcx::new(icx, config);
            let IdeAnalysis {
                package,
                results,
                status,
            } = compiler
                .analyze_for_ide(compile_ide_mode(mode))
                .map_err(|_| String::new())?;
            let file_paths = icx.dcx.all_file_mappings().into_iter().collect();
            let module_targets = build_module_target_map(&package.root, &file_paths);
            return Ok(collect_ide_artifacts(
                gcx,
                &package,
                results.as_ref(),
                &module_targets,
                analysis_status(status),
            ));
        }

        let _ = compiler.analyze_for_ide(IdeAnalysisMode::OnType);
    }

    Err("package analysis did not produce a root package".into())
}

fn analysis_status(status: IdeAnalysisStatus) -> AnalysisStatus {
    AnalysisStatus {
        hir_available: status.hir_available,
        typed_available: status.typed_available,
    }
}

fn compile_ide_mode(mode: AnalysisMode) -> IdeAnalysisMode {
    match mode {
        AnalysisMode::OnType => IdeAnalysisMode::OnType,
        AnalysisMode::OnSave => IdeAnalysisMode::OnSave,
    }
}

struct NavigationVisitor<'ctx, 'results> {
    gcx: Gcx<'ctx>,
    results: Option<&'results TypeCheckResults<'ctx>>,
    module_targets: &'results FxHashMap<DefinitionID, Span>,
    nav_data: NavigationData,
    local_binding_spans: FxHashMap<hir::NodeID, Span>,
}

impl<'ctx, 'results> NavigationVisitor<'ctx, 'results> {
    fn new(
        gcx: Gcx<'ctx>,
        results: Option<&'results TypeCheckResults<'ctx>>,
        module_targets: &'results FxHashMap<DefinitionID, Span>,
    ) -> Self {
        Self {
            gcx,
            results,
            module_targets,
            nav_data: NavigationData::default(),
            local_binding_spans: FxHashMap::default(),
        }
    }

    fn finish(mut self) -> NavigationData {
        self.nav_data
            .hovers
            .sort_by(|lhs, rhs| compare_navigation_spans(lhs.span, rhs.span));
        self.nav_data
            .hovers
            .dedup_by(|lhs, rhs| lhs.span == rhs.span && lhs.contents == rhs.contents);
        self.nav_data
            .definitions
            .sort_by(|lhs, rhs| compare_navigation_spans(lhs.source, rhs.source));
        self.nav_data
            .definitions
            .dedup_by(|lhs, rhs| lhs.source == rhs.source && lhs.target == rhs.target);
        self.nav_data.hover_parents =
            build_parent_links(self.nav_data.hovers.iter().map(|hover| hover.span));
        self.nav_data.definition_parents = build_parent_links(
            self.nav_data
                .definitions
                .iter()
                .map(|definition| definition.source),
        );
        self.nav_data
    }

    fn push_expression_hover(&mut self, node: &Expression) {
        if let ExpressionKind::Member { target, name } = &node.kind
            && let Some(contents) = self.member_hover_contents(node, target)
        {
            self.nav_data.hovers.push(HoverInfo {
                span: name.span,
                contents,
            });
        }

        if let ExpressionKind::StructLiteral(literal) = &node.kind {
            self.push_struct_literal_field_hovers(node, literal);
        }

        let Some(contents) = self.expression_hover_contents(node) else {
            return;
        };

        self.nav_data.hovers.push(HoverInfo {
            span: node.span,
            contents,
        });
    }

    fn push_pattern_hover(&mut self, node: &Pattern) {
        let Some(ty) = self
            .results
            .and_then(|results| results.try_node_type(node.id))
        else {
            return;
        };

        self.nav_data.hovers.push(HoverInfo {
            span: pattern_navigation_span(node),
            contents: ty.format(self.gcx),
        });
    }

    fn push_type_hover(&mut self, node: &Type) {
        let Some(ty) = self
            .results
            .and_then(|results| results.try_node_type(node.id))
        else {
            return;
        };

        self.nav_data.hovers.push(HoverInfo {
            span: node.span,
            contents: ty.format(self.gcx),
        });
    }

    fn push_path_segment_hover(&mut self, node: &PathSegment) {
        let Some(contents) = self
            .resolution_hover_contents(&node.resolution)
            .or_else(|| {
                self.results
                    .and_then(|results| results.try_node_type(node.id))
                    .map(|ty| ty.format(self.gcx))
            })
        else {
            return;
        };

        self.nav_data.hovers.push(HoverInfo {
            span: node.span,
            contents,
        });
    }

    fn push_declaration_hover(&mut self, id: DefinitionID, span: Span, kind: &DeclarationKind) {
        let contents = match kind {
            DeclarationKind::Function(..) => {
                crate::sema::models::format_definition_signature_for_display(self.gcx, id)
            }
            DeclarationKind::Constant(..) | DeclarationKind::StaticVariable(..) => {
                Some(self.gcx.get_type(id).format(self.gcx))
            }
            DeclarationKind::TypeAlias(..) => self
                .gcx
                .try_get_alias_type(id)
                .map(|ty| ty.format(self.gcx)),
            _ => None,
        };

        if let Some(contents) = contents {
            self.nav_data.hovers.push(HoverInfo { span, contents });
        }
    }

    fn push_assoc_declaration_hover(
        &mut self,
        id: DefinitionID,
        span: Span,
        kind: &AssociatedDeclarationKind,
    ) {
        let contents = match kind {
            AssociatedDeclarationKind::Function(..) => {
                crate::sema::models::format_definition_signature_for_display(self.gcx, id)
            }
            AssociatedDeclarationKind::Constant(..) => Some(self.gcx.get_type(id).format(self.gcx)),
            AssociatedDeclarationKind::Property(..) => Some(self.gcx.get_type(id).format(self.gcx)),
            AssociatedDeclarationKind::Type(..) => self
                .gcx
                .try_get_alias_type(id)
                .map(|ty| ty.format(self.gcx)),
        };

        if let Some(contents) = contents {
            self.nav_data.hovers.push(HoverInfo { span, contents });
        }
    }

    fn push_expression_definition(&mut self, node: &Expression) {
        if let ExpressionKind::Member { target, name } = &node.kind
            && let Some(target) = self.member_definition_target(node, target)
        {
            self.nav_data.definitions.push(DefinitionInfo {
                source: name.span,
                target,
            });
        }

        if let ExpressionKind::StructLiteral(literal) = &node.kind {
            self.push_struct_literal_field_definitions(node, literal);
        }

        let Some(target) = self.definition_target_for_expression(node) else {
            return;
        };

        self.nav_data.definitions.push(DefinitionInfo {
            source: node.span,
            target,
        });
    }

    fn push_pattern_definition(&mut self, node: &Pattern) {
        let Some(target) = self.definition_target_for_pattern(node) else {
            return;
        };

        self.nav_data.definitions.push(DefinitionInfo {
            source: pattern_navigation_span(node),
            target,
        });
    }

    fn push_path_segment_definition(&mut self, node: &PathSegment) {
        let Some(target) = self.definition_target_for_resolution(&node.resolution) else {
            return;
        };

        self.nav_data.definitions.push(DefinitionInfo {
            source: node.span,
            target,
        });
    }

    fn definition_target_for_expression(&self, node: &Expression) -> Option<Span> {
        let resolution = self.expression_resolution(node);
        self.definition_target_for_resolution(resolution.as_ref()?)
    }

    fn definition_target_for_pattern(&self, node: &Pattern) -> Option<Span> {
        let resolution = self.pattern_resolution(node);
        self.definition_target_for_resolution(resolution.as_ref()?)
    }

    fn expression_hover_contents(&self, node: &Expression) -> Option<String> {
        if let Some(def_id) = self
            .expression_resolution(node)
            .as_ref()
            .and_then(Resolution::definition_id)
            && let Some(contents) = self.definition_hover_contents(def_id)
        {
            return Some(contents);
        }

        self.results
            .and_then(|results| results.try_node_type(node.id))
            .map(|ty| ty.format(self.gcx))
    }

    fn resolution_hover_contents(&self, resolution: &Resolution) -> Option<String> {
        let def_id = resolution.definition_id()?;
        self.definition_hover_contents(def_id)
    }

    fn definition_hover_contents(&self, def_id: DefinitionID) -> Option<String> {
        match self.gcx.definition_kind(def_id) {
            DefinitionKind::Function
            | DefinitionKind::AssociatedFunction
            | DefinitionKind::AssociatedOperator => {
                crate::sema::models::format_definition_signature_for_display(self.gcx, def_id)
            }
            DefinitionKind::Module | DefinitionKind::Namespace | DefinitionKind::Interface => {
                Some(format!(
                    "{} {}",
                    self.gcx.definition_kind(def_id).description(),
                    self.gcx
                        .symbol_text(self.gcx.definition_ident(def_id).symbol)
                ))
            }
            DefinitionKind::TypeAlias | DefinitionKind::AssociatedType => self
                .gcx
                .try_get_alias_type(def_id)
                .map(|ty| ty.format(self.gcx)),
            DefinitionKind::Struct
            | DefinitionKind::Enum
            | DefinitionKind::Field
            | DefinitionKind::Variant
            | DefinitionKind::Constant
            | DefinitionKind::AssociatedConstant
            | DefinitionKind::AssociatedProperty
            | DefinitionKind::ModuleVariable
            | DefinitionKind::OpaqueType
            | DefinitionKind::TypeParameter
            | DefinitionKind::ConstParameter => Some(self.gcx.get_type(def_id).format(self.gcx)),
            _ => None,
        }
    }

    fn expression_resolution(&self, node: &Expression) -> Option<Resolution> {
        self.results
            .and_then(|results| results.overload_source(node.id))
            .map(|def_id| Resolution::Definition(def_id, self.gcx.definition_kind(def_id)))
            .or_else(|| {
                self.results
                    .and_then(|results| results.value_resolution(node.id))
            })
            .or_else(|| expression_fallback_resolution(node))
    }

    fn pattern_resolution(&self, node: &Pattern) -> Option<Resolution> {
        self.results
            .and_then(|results| results.overload_source(node.id))
            .map(|def_id| Resolution::Definition(def_id, self.gcx.definition_kind(def_id)))
            .or_else(|| {
                self.results
                    .and_then(|results| results.value_resolution(node.id))
            })
            .or_else(|| pattern_fallback_resolution(node))
    }

    fn definition_target_for_resolution(&self, resolution: &Resolution) -> Option<Span> {
        match resolution {
            Resolution::LocalVariable(id) => self.local_binding_spans.get(id).copied(),
            _ => {
                let def_id = resolution.definition_id()?;
                if self.gcx.definition_kind(def_id) == DefinitionKind::Module {
                    self.module_targets
                        .get(&def_id)
                        .copied()
                        .or_else(|| Some(self.gcx.definition_ident(def_id).span))
                } else {
                    Some(self.gcx.definition_ident(def_id).span)
                }
            }
        }
    }

    fn member_hover_contents(&self, node: &Expression, target: &Expression) -> Option<String> {
        let has_definition = self
            .results
            .and_then(|results| results.property_read(node.id))
            .is_some()
            || self.member_definition(node, target).is_some();
        if !has_definition {
            return None;
        }

        self.results
            .and_then(|results| results.try_node_type(node.id))
            .map(|ty| ty.format(self.gcx))
    }

    fn member_definition_target(&self, node: &Expression, target: &Expression) -> Option<Span> {
        if let Some(property) = self
            .results
            .and_then(|results| results.property_read(node.id))
        {
            return Some(self.gcx.definition_ident(property.property_id).span);
        }

        let (field_def, _) = self.member_definition(node, target)?;
        Some(self.gcx.definition_ident(field_def.def_id).span)
    }

    fn member_definition(
        &self,
        node: &Expression,
        target: &Expression,
    ) -> Option<(StructField<'ctx>, usize)> {
        let results = self.results?;
        let index = results.field_index(node.id)?;
        let target_ty = results.try_node_type(target.id)?;
        self.struct_field_for_ty(target_ty, index)
            .map(|field| (field, index))
    }

    fn push_struct_literal_field_hovers(&mut self, node: &Expression, literal: &StructLiteral) {
        let Some(results) = self.results else {
            return;
        };
        let Some(struct_ty) = results.try_node_type(node.id) else {
            return;
        };

        for field in &literal.fields {
            let Some(name) = struct_literal_field_name(field) else {
                continue;
            };
            let Some(field_def) = self.struct_field_by_name(struct_ty, name) else {
                continue;
            };
            self.nav_data.hovers.push(HoverInfo {
                span: struct_literal_field_navigation_span(field),
                contents: field_def.ty.format(self.gcx),
            });
        }
    }

    fn push_struct_literal_field_definitions(
        &mut self,
        node: &Expression,
        literal: &StructLiteral,
    ) {
        let Some(results) = self.results else {
            return;
        };
        let Some(struct_ty) = results.try_node_type(node.id) else {
            return;
        };

        for field in &literal.fields {
            let Some(name) = struct_literal_field_name(field) else {
                continue;
            };
            let Some(field_def) = self.struct_field_by_name(struct_ty, name) else {
                continue;
            };
            self.nav_data.definitions.push(DefinitionInfo {
                source: struct_literal_field_navigation_span(field),
                target: self.gcx.definition_ident(field_def.def_id).span,
            });
        }
    }

    fn struct_field_by_name(
        &self,
        ty: Ty<'ctx>,
        name: crate::span::Symbol,
    ) -> Option<StructField<'ctx>> {
        match ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
                self.struct_field_by_name(inner, name)
            }
            TyKind::Alias { def_id, .. } => self
                .gcx
                .try_get_alias_type(def_id)
                .and_then(|alias_ty| self.struct_field_by_name(alias_ty, name)),
            TyKind::Adt(def, _) if def.kind == AdtKind::Struct => self
                .gcx
                .try_get_struct_definition(def.id)
                .and_then(|struct_def| {
                    struct_def
                        .fields
                        .iter()
                        .find(|field| field.name == name)
                        .copied()
                }),
            _ => None,
        }
    }

    fn struct_field_for_ty(&self, ty: Ty<'ctx>, index: usize) -> Option<StructField<'ctx>> {
        match ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
                self.struct_field_for_ty(inner, index)
            }
            TyKind::Alias { def_id, .. } => self
                .gcx
                .try_get_alias_type(def_id)
                .and_then(|alias_ty| self.struct_field_for_ty(alias_ty, index)),
            TyKind::Adt(def, _) if def.kind == AdtKind::Struct => self
                .gcx
                .try_get_struct_definition(def.id)
                .and_then(|struct_def| struct_def.fields.get(index).copied()),
            _ => None,
        }
    }

    fn push_use_tree_alias_hover(&mut self, alias: &UseTreeAlias, resolution: &Resolution) {
        let Some(contents) = self.resolution_hover_contents(resolution) else {
            return;
        };

        self.nav_data.hovers.push(HoverInfo {
            span: alias.span,
            contents,
        });
    }

    fn push_use_tree_alias_definition(&mut self, alias: &UseTreeAlias, resolution: &Resolution) {
        let Some(target) = self.definition_target_for_resolution(resolution) else {
            return;
        };

        self.nav_data.definitions.push(DefinitionInfo {
            source: alias.span,
            target,
        });
    }
}

impl<'ctx, 'results> HirVisitor for NavigationVisitor<'ctx, 'results> {
    fn visit_expression(&mut self, node: &Expression) {
        self.push_expression_hover(node);
        self.push_expression_definition(node);
        walk_expression(self, node)
    }

    fn visit_pattern(&mut self, node: &Pattern) {
        if let PatternKind::Binding { name, .. } = &node.kind {
            self.local_binding_spans.insert(node.id, name.span);
        }

        self.push_pattern_hover(node);
        self.push_pattern_definition(node);
        walk_pattern(self, node)
    }

    fn visit_function_parameter(&mut self, node: &hir::FunctionParameter) {
        self.local_binding_spans.insert(node.id, node.name.span);
        hir::walk_function_parameter(self, node)
    }

    fn visit_type(&mut self, node: &Type) {
        self.push_type_hover(node);
        walk_type(self, node)
    }

    fn visit_path_segment(&mut self, node: &PathSegment) {
        self.push_path_segment_hover(node);
        self.push_path_segment_definition(node);
        walk_path_segment(self, node)
    }

    fn visit_declaration(&mut self, node: &Declaration) {
        self.push_declaration_hover(node.id, node.identifier.span, &node.kind);
        walk_declaration(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &AssociatedDeclaration,
        context: hir::AssocContext,
    ) {
        self.push_assoc_declaration_hover(node.id, node.identifier.span, &node.kind);
        walk_assoc_declaration(self, node, context)
    }

    fn visit_use_tree(&mut self, node: &UseTree, context: hir::UseTreeContext) {
        match &node.kind {
            UseTreeKind::Simple { source, alias } => {
                if let Some(alias) = alias {
                    self.push_use_tree_alias_hover(alias, &source.resolution);
                    self.push_use_tree_alias_definition(alias, &source.resolution);
                }
            }
            UseTreeKind::Nested { items, .. } => {
                for item in items {
                    if let Some(alias) = &item.alias {
                        self.push_use_tree_alias_hover(alias, &item.source.resolution);
                        self.push_use_tree_alias_definition(alias, &item.source.resolution);
                    }
                }
            }
            UseTreeKind::Glob => {}
        }

        walk_use_tree(self, node, context)
    }
}

fn collect_navigation_data<'ctx>(
    gcx: Gcx<'ctx>,
    package: &hir::Package,
    results: Option<&TypeCheckResults<'ctx>>,
    module_targets: &FxHashMap<DefinitionID, Span>,
) -> NavigationData {
    let mut visitor = NavigationVisitor::new(gcx, results, module_targets);
    visitor.visit_package(package);
    visitor.finish()
}

struct ReferenceVisitor<'ctx, 'results> {
    gcx: Gcx<'ctx>,
    results: Option<&'results TypeCheckResults<'ctx>>,
    groups: FxHashMap<ReferenceKey, Vec<ReferenceInfo>>,
    mentions: Vec<ReferenceMention>,
}

impl<'ctx, 'results> ReferenceVisitor<'ctx, 'results> {
    fn new(gcx: Gcx<'ctx>, results: Option<&'results TypeCheckResults<'ctx>>) -> Self {
        Self {
            gcx,
            results,
            groups: FxHashMap::default(),
            mentions: Vec::new(),
        }
    }

    fn finish(mut self) -> ReferenceData {
        let mut groups: Vec<_> = self
            .groups
            .drain()
            .map(|(key, mut items)| {
                items.sort_by(|lhs, rhs| {
                    compare_navigation_spans(lhs.span, rhs.span)
                        .then_with(|| rhs.is_declaration.cmp(&lhs.is_declaration))
                });
                items.dedup_by(|lhs, rhs| {
                    lhs.span == rhs.span && lhs.is_declaration == rhs.is_declaration
                });
                ReferenceGroup { key, items }
            })
            .collect();
        groups.sort_by(|lhs, rhs| compare_reference_keys(lhs.key, rhs.key));

        self.mentions.sort_by(|lhs, rhs| {
            compare_navigation_spans(lhs.span, rhs.span)
                .then_with(|| compare_reference_keys(lhs.key, rhs.key))
        });
        self.mentions
            .dedup_by(|lhs, rhs| lhs.key == rhs.key && lhs.span == rhs.span);
        let parents = build_parent_links(self.mentions.iter().map(|mention| mention.span));

        ReferenceData {
            groups,
            mentions: self.mentions,
            parents,
        }
    }

    fn push_reference(&mut self, key: ReferenceKey, span: Span, is_declaration: bool) {
        if span.start == span.end {
            return;
        }

        self.groups.entry(key).or_default().push(ReferenceInfo {
            span,
            is_declaration,
        });
        self.mentions.push(ReferenceMention { key, span });
    }

    fn push_definition_reference(
        &mut self,
        def_id: DefinitionID,
        span: Span,
        is_declaration: bool,
    ) {
        let key = self.reference_key_for_definition(def_id);
        self.push_reference(key, span, is_declaration);
    }

    fn push_resolution_reference(
        &mut self,
        resolution: &Resolution,
        span: Span,
        is_declaration: bool,
    ) {
        let Some(key) = self.reference_key_for_resolution(resolution) else {
            return;
        };
        self.push_reference(key, span, is_declaration);
    }

    fn reference_key_for_definition(&self, def_id: DefinitionID) -> ReferenceKey {
        if matches!(
            self.gcx.definition_kind(def_id),
            DefinitionKind::VariantConstructor(..)
        ) && let Some(enum_id) = self.gcx.definition_parent(def_id)
            && let Some(enum_def) = self.gcx.try_get_enum_definition(enum_id)
            && let Some(variant) = enum_def
                .variants
                .iter()
                .find(|variant| variant.ctor_def_id == def_id)
        {
            return ReferenceKey::Definition(variant.def_id);
        }

        ReferenceKey::Definition(def_id)
    }

    fn reference_key_for_resolution(&self, resolution: &Resolution) -> Option<ReferenceKey> {
        match resolution {
            Resolution::LocalVariable(id) => Some(ReferenceKey::Local(*id)),
            Resolution::FunctionSet(ids) if ids.len() == 1 => {
                Some(self.reference_key_for_definition(ids[0]))
            }
            _ => resolution
                .definition_id()
                .map(|def_id| self.reference_key_for_definition(def_id)),
        }
    }

    fn expression_resolution(&self, node: &Expression) -> Option<Resolution> {
        expression_resolution_for_ide(self.gcx, self.results, node)
    }

    fn pattern_resolution(&self, node: &Pattern) -> Option<Resolution> {
        self.results
            .and_then(|results| results.overload_source(node.id))
            .map(|def_id| Resolution::Definition(def_id, self.gcx.definition_kind(def_id)))
            .or_else(|| {
                self.results
                    .and_then(|results| results.value_resolution(node.id))
            })
            .or_else(|| pattern_fallback_resolution(node))
    }

    fn push_expression_references(&mut self, node: &Expression) {
        match &node.kind {
            ExpressionKind::Path(ResolvedPath::Resolved(path)) => {
                if let Some(segment) = path.segments.last() {
                    self.push_resolution_reference(&path.resolution, segment.span, false);
                }
            }
            ExpressionKind::Path(ResolvedPath::Relative(_, segment)) => {
                if let Some(resolution) = self.expression_resolution(node) {
                    self.push_resolution_reference(&resolution, segment.span, false);
                }
            }
            ExpressionKind::Member { target, name } => {
                if let Some(property) = self
                    .results
                    .and_then(|results| results.property_read(node.id))
                {
                    self.push_definition_reference(property.property_id, name.span, false);
                    return;
                }

                if let Some((field, _)) = self.member_definition(node, target) {
                    self.push_definition_reference(field.def_id, name.span, false);
                } else if let Some(resolution) = self.expression_resolution(node) {
                    self.push_resolution_reference(&resolution, name.span, false);
                }
            }
            ExpressionKind::MethodCall { name, .. } => {
                if let Some(def_id) = self
                    .results
                    .and_then(|results| results.overload_source(node.id))
                {
                    self.push_definition_reference(def_id, name.span, false);
                }
            }
            ExpressionKind::InferredMember { name } => {
                if let Some(resolution) = self.expression_resolution(node) {
                    self.push_resolution_reference(&resolution, name.span, false);
                }
            }
            ExpressionKind::StructLiteral(literal) => {
                self.push_struct_literal_field_references(node, literal);
            }
            _ => {}
        }
    }

    fn push_pattern_references(&mut self, node: &Pattern) {
        match &node.kind {
            PatternKind::Binding { name, .. } => {
                self.push_reference(ReferenceKey::Local(node.id), name.span, true);
            }
            PatternKind::Member(PatternPath::Inferred { name, .. })
            | PatternKind::PathTuple {
                path: PatternPath::Inferred { name, .. },
                ..
            } => {
                if let Some(resolution) = self.pattern_resolution(node) {
                    self.push_resolution_reference(&resolution, name.span, false);
                }
            }
            _ => {
                if let Some(resolution) = self.pattern_resolution(node) {
                    self.push_resolution_reference(
                        &resolution,
                        pattern_navigation_span(node),
                        false,
                    );
                }
            }
        }
    }

    fn push_struct_literal_field_references(&mut self, node: &Expression, literal: &StructLiteral) {
        let Some(results) = self.results else {
            return;
        };
        let Some(struct_ty) = results.try_node_type(node.id) else {
            return;
        };

        for field in &literal.fields {
            let Some(name) = struct_literal_field_name(field) else {
                continue;
            };
            let Some(field_def) = self.struct_field_by_name(struct_ty, name) else {
                continue;
            };
            self.push_definition_reference(
                field_def.def_id,
                struct_literal_field_navigation_span(field),
                false,
            );
        }
    }

    fn member_definition(
        &self,
        node: &Expression,
        target: &Expression,
    ) -> Option<(StructField<'ctx>, usize)> {
        let results = self.results?;
        let index = results.field_index(node.id)?;
        let target_ty = results.try_node_type(target.id)?;
        self.struct_field_for_ty(target_ty, index)
            .map(|field| (field, index))
    }

    fn struct_field_by_name(
        &self,
        ty: Ty<'ctx>,
        name: crate::span::Symbol,
    ) -> Option<StructField<'ctx>> {
        match ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
                self.struct_field_by_name(inner, name)
            }
            TyKind::Alias { def_id, .. } => self
                .gcx
                .try_get_alias_type(def_id)
                .and_then(|alias_ty| self.struct_field_by_name(alias_ty, name)),
            TyKind::Adt(def, _) if def.kind == AdtKind::Struct => self
                .gcx
                .try_get_struct_definition(def.id)
                .and_then(|struct_def| {
                    struct_def
                        .fields
                        .iter()
                        .find(|field| field.name == name)
                        .copied()
                }),
            _ => None,
        }
    }

    fn struct_field_for_ty(&self, ty: Ty<'ctx>, index: usize) -> Option<StructField<'ctx>> {
        match ty.kind() {
            TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
                self.struct_field_for_ty(inner, index)
            }
            TyKind::Alias { def_id, .. } => self
                .gcx
                .try_get_alias_type(def_id)
                .and_then(|alias_ty| self.struct_field_for_ty(alias_ty, index)),
            TyKind::Adt(def, _) if def.kind == AdtKind::Struct => self
                .gcx
                .try_get_struct_definition(def.id)
                .and_then(|struct_def| struct_def.fields.get(index).copied()),
            _ => None,
        }
    }
}

impl<'ctx, 'results> HirVisitor for ReferenceVisitor<'ctx, 'results> {
    fn visit_declaration(&mut self, node: &Declaration) {
        if !matches!(
            self.gcx.definition_kind(node.id),
            DefinitionKind::Import | DefinitionKind::Export | DefinitionKind::Impl
        ) {
            self.push_definition_reference(node.id, node.identifier.span, true);
        }
        walk_declaration(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &AssociatedDeclaration,
        context: hir::AssocContext,
    ) {
        self.push_definition_reference(node.id, node.identifier.span, true);
        walk_assoc_declaration(self, node, context)
    }

    fn visit_variant(&mut self, node: &Variant) {
        self.push_definition_reference(node.def_id, node.identifier.span, true);
        hir::walk_variant(self, node)
    }

    fn visit_field_definition(&mut self, node: &FieldDefinition) {
        self.push_definition_reference(node.def_id, node.identifier.span, true);
        hir::walk_field_definition(self, node)
    }

    fn visit_type_parameter(&mut self, node: &hir::TypeParameter) {
        self.push_definition_reference(node.id, node.identifier.span, true);
        hir::walk_type_parameter(self, node)
    }

    fn visit_function_parameter(&mut self, node: &hir::FunctionParameter) {
        self.push_reference(ReferenceKey::Local(node.id), node.name.span, true);
        hir::walk_function_parameter(self, node)
    }

    fn visit_expression(&mut self, node: &Expression) {
        self.push_expression_references(node);
        walk_expression(self, node)
    }

    fn visit_pattern(&mut self, node: &Pattern) {
        self.push_pattern_references(node);
        walk_pattern(self, node)
    }

    fn visit_path_segment(&mut self, node: &PathSegment) {
        self.push_resolution_reference(&node.resolution, node.span, false);
        walk_path_segment(self, node)
    }
}

fn collect_reference_data<'ctx>(
    gcx: Gcx<'ctx>,
    package: &hir::Package,
    results: Option<&TypeCheckResults<'ctx>>,
) -> ReferenceData {
    let mut visitor = ReferenceVisitor::new(gcx, results);
    visitor.visit_package(package);
    visitor.finish()
}

struct SignatureVisitor<'ctx, 'results> {
    gcx: Gcx<'ctx>,
    results: Option<&'results TypeCheckResults<'ctx>>,
    data: SignatureHelpData,
}

impl<'ctx, 'results> SignatureVisitor<'ctx, 'results> {
    fn new(gcx: Gcx<'ctx>, results: Option<&'results TypeCheckResults<'ctx>>) -> Self {
        Self {
            gcx,
            results,
            data: SignatureHelpData::default(),
        }
    }

    fn finish(mut self) -> SignatureHelpData {
        self.data
            .sites
            .sort_by(|lhs, rhs| compare_navigation_spans(lhs.span, rhs.span));
        self.data.parents = build_parent_links(self.data.sites.iter().map(|site| site.span));
        self.data
    }

    fn push_call_site(&mut self, node: &Expression) {
        let (signatures, arguments) = match &node.kind {
            ExpressionKind::Call { callee, arguments } => (
                call_signature_candidates(self.gcx, self.results, node, Some(callee.as_ref())),
                arguments
                    .iter()
                    .map(|argument| argument.span)
                    .collect::<Vec<_>>(),
            ),
            ExpressionKind::MethodCall { arguments, .. } => (
                call_signature_candidates(self.gcx, self.results, node, None),
                arguments
                    .iter()
                    .map(|argument| argument.span)
                    .collect::<Vec<_>>(),
            ),
            _ => return,
        };

        if signatures.is_empty() {
            return;
        }

        self.data.sites.push(SignatureHelpSite {
            span: node.span,
            arguments,
            signatures,
        });
    }
}

impl<'ctx, 'results> HirVisitor for SignatureVisitor<'ctx, 'results> {
    fn visit_expression(&mut self, node: &Expression) {
        self.push_call_site(node);
        walk_expression(self, node)
    }
}

fn collect_signature_help_data<'ctx>(
    gcx: Gcx<'ctx>,
    package: &hir::Package,
    results: Option<&TypeCheckResults<'ctx>>,
) -> SignatureHelpData {
    let mut visitor = SignatureVisitor::new(gcx, results);
    visitor.visit_package(package);
    visitor.finish()
}

struct CompletionVisitor<'ctx, 'results> {
    gcx: Gcx<'ctx>,
    results: Option<&'results TypeCheckResults<'ctx>>,
    resolution_output: &'results crate::sema::resolve::models::ResolutionOutput<'ctx>,
    data: CompletionData,
    current_def: Option<DefinitionID>,
}

impl<'ctx, 'results> CompletionVisitor<'ctx, 'results> {
    fn new(
        gcx: Gcx<'ctx>,
        results: Option<&'results TypeCheckResults<'ctx>>,
        resolution_output: &'results crate::sema::resolve::models::ResolutionOutput<'ctx>,
    ) -> Self {
        Self {
            gcx,
            results,
            resolution_output,
            data: CompletionData::default(),
            current_def: None,
        }
    }

    fn finish(mut self) -> CompletionData {
        self.data
            .scopes
            .sort_by(|lhs, rhs| compare_navigation_spans(lhs.span, rhs.span));
        self.data
            .member_sites
            .sort_by(|lhs, rhs| compare_navigation_spans(lhs.span, rhs.span));
        self.data
    }

    fn push_scope(&mut self, span: Span, scope: Scope<'ctx>) {
        let items = completion_items_for_scope(self.gcx, scope);
        self.data.scopes.push(CompletionScope { span, items });
    }

    fn push_member_site(&mut self, span: Span, items: Vec<CompletionInfo>) {
        if !items.is_empty() {
            self.data
                .member_sites
                .push(MemberCompletionSite { span, items });
        }
    }

    fn push_expression_member_sites(&mut self, node: &Expression) {
        match &node.kind {
            ExpressionKind::Member { target, name }
            | ExpressionKind::MethodCall {
                receiver: target,
                name,
                ..
            } => {
                let Some(results) = self.results else {
                    return;
                };
                let mut items = if let Some(target_ty) = results.try_node_type(target.id) {
                    member_completion_items_for_ty(
                        self.gcx,
                        target_ty,
                        MemberCompletionMode::Instance,
                        self.current_def,
                    )
                } else if let Some(def_id) =
                    expression_resolution_for_ide(self.gcx, self.results, target)
                        .and_then(|resolution| resolution.definition_id())
                {
                    static_member_completion_items_for_definition(
                        self.gcx,
                        def_id,
                        self.current_def,
                    )
                } else {
                    Vec::new()
                };
                if items.is_empty()
                    && let Some(def_id) =
                        expression_resolution_for_ide(self.gcx, self.results, target)
                            .and_then(|resolution| resolution.definition_id())
                {
                    items = static_member_completion_items_for_definition(
                        self.gcx,
                        def_id,
                        self.current_def,
                    );
                }
                self.push_member_site(name.span, items);
            }
            ExpressionKind::Path(ResolvedPath::Relative(base, segment)) => {
                let items = if let Some(results) = self.results
                    && let Some(base_ty) = results.try_node_type(base.id)
                {
                    member_completion_items_for_ty(
                        self.gcx,
                        base_ty,
                        MemberCompletionMode::Static,
                        self.current_def,
                    )
                } else if let Some(def_id) = type_definition_id_for_completion(base) {
                    static_member_completion_items_for_definition(
                        self.gcx,
                        def_id,
                        self.current_def,
                    )
                } else {
                    Vec::new()
                };
                self.push_member_site(segment.span, items);
            }
            _ => {}
        }
    }
}

impl<'ctx, 'results> HirVisitor for CompletionVisitor<'ctx, 'results> {
    fn visit_module(&mut self, node: &Module, is_root: bool) {
        for file in &node.files {
            if let Some(scope) = self.resolution_output.file_scope_mapping.get(file).copied() {
                self.push_scope(file_completion_span(*file), scope);
            }
        }

        if let Some(scope) = self
            .resolution_output
            .definition_scope_mapping
            .get(&node.id)
            .copied()
        {
            self.push_scope(module_completion_span(node), scope);
        }

        hir::walk_module(self, node, is_root)
    }

    fn visit_declaration(&mut self, node: &Declaration) {
        if let Some(scope) = self
            .resolution_output
            .definition_scope_mapping
            .get(&node.id)
            .copied()
        {
            self.push_scope(node.span, scope);
        }

        let previous = self.current_def.replace(node.id);
        walk_declaration(self, node);
        self.current_def = previous;
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &AssociatedDeclaration,
        context: hir::AssocContext,
    ) {
        if let Some(scope) = self
            .resolution_output
            .definition_scope_mapping
            .get(&node.id)
            .copied()
        {
            self.push_scope(node.span, scope);
        }

        let previous = self.current_def.replace(node.id);
        walk_assoc_declaration(self, node, context);
        self.current_def = previous;
    }

    fn visit_block(&mut self, node: &hir::Block) {
        let mut items = self
            .resolution_output
            .file_scope_mapping
            .get(&node.span.file)
            .copied()
            .map(|scope| completion_items_for_scope(self.gcx, scope))
            .unwrap_or_default();
        let mut seen: FxHashSet<_> = items
            .iter()
            .map(|item| (item.label.clone(), item.kind))
            .collect();
        if let Some(scope) = self.current_def.and_then(|def_id| {
            self.resolution_output
                .definition_scope_mapping
                .get(&def_id)
                .copied()
        }) {
            for item in completion_items_for_scope(self.gcx, scope) {
                push_completion(&mut items, &mut seen, item);
            }
        }
        collect_block_local_completions(self.gcx, node, &mut items, &mut seen);
        if !items.is_empty() {
            self.data.scopes.push(CompletionScope {
                span: node.span,
                items,
            });
        }
        hir::walk_block(self, node)
    }

    fn visit_expression(&mut self, node: &Expression) {
        self.push_expression_member_sites(node);
        walk_expression(self, node)
    }

    fn visit_resolved_path(&mut self, node: &ResolvedPath) {
        match node {
            ResolvedPath::Resolved(path) => {
                for pair in path.segments.windows(2) {
                    let base = &pair[0];
                    let member = &pair[1];
                    if let Some(def_id) = base.resolution.definition_id() {
                        let items = static_member_completion_items_for_definition(
                            self.gcx,
                            def_id,
                            self.current_def,
                        );
                        self.push_member_site(member.span, items);
                    }
                }
            }
            ResolvedPath::Relative(base, segment) => {
                if let Some(def_id) = type_definition_id_for_completion(base) {
                    let items = static_member_completion_items_for_definition(
                        self.gcx,
                        def_id,
                        self.current_def,
                    );
                    self.push_member_site(segment.span, items);
                }
            }
        }

        walk_resolved_path(self, node)
    }
}

fn collect_completion_data<'ctx>(
    gcx: Gcx<'ctx>,
    package: &hir::Package,
    results: Option<&TypeCheckResults<'ctx>>,
) -> CompletionData {
    let Some(resolution_output) = gcx.try_resolution_output(gcx.package_index()) else {
        return CompletionData::default();
    };
    let mut visitor = CompletionVisitor::new(gcx, results, resolution_output);
    visitor.visit_package(package);
    visitor.finish()
}

#[derive(Clone, Copy)]
enum MemberCompletionMode {
    Instance,
    Static,
}

fn completion_items_for_scope(gcx: Gcx<'_>, scope: Scope<'_>) -> Vec<CompletionInfo> {
    let mut items = Vec::new();
    let mut seen = FxHashSet::default();
    let mut current = Some(scope);
    let mut depth = 0usize;

    while let Some(scope) = current {
        collect_scope_completion_items(gcx, scope, &mut items, &mut seen, 0);
        current = scope.parent;
        depth += 1;
        if depth > 128 {
            break;
        }
    }

    for primary in PrimaryType::ALL {
        push_completion(
            &mut items,
            &mut seen,
            CompletionInfo {
                label: primary.name_str().to_string(),
                kind: CompletionKind::Type,
                detail: Some("builtin type".into()),
            },
        );
    }

    push_completion(
        &mut items,
        &mut seen,
        CompletionInfo {
            label: "make".into(),
            kind: CompletionKind::Function,
            detail: Some("builtin function".into()),
        },
    );

    push_completion(
        &mut items,
        &mut seen,
        CompletionInfo {
            label: gcx.config.name.to_string(),
            kind: CompletionKind::Package,
            detail: Some("package".into()),
        },
    );
    for alias in gcx.config.dependencies.keys() {
        push_completion(
            &mut items,
            &mut seen,
            CompletionInfo {
                label: alias.to_string(),
                kind: CompletionKind::Package,
                detail: Some("package".into()),
            },
        );
    }

    items
}

fn collect_block_local_completions(
    gcx: Gcx<'_>,
    block: &hir::Block,
    items: &mut Vec<CompletionInfo>,
    seen: &mut FxHashSet<(String, CompletionKind)>,
) {
    for statement in &block.statements {
        if let hir::StatementKind::Variable(local) = &statement.kind {
            collect_pattern_completion_items(gcx, &local.pattern, items, seen);
        }
    }
}

fn collect_pattern_completion_items(
    gcx: Gcx<'_>,
    pattern: &Pattern,
    items: &mut Vec<CompletionInfo>,
    seen: &mut FxHashSet<(String, CompletionKind)>,
) {
    match &pattern.kind {
        PatternKind::Binding { name, .. } => push_completion(
            items,
            seen,
            CompletionInfo {
                label: gcx.symbol_text(name.symbol).to_string(),
                kind: CompletionKind::Variable,
                detail: Some("local variable".into()),
            },
        ),
        PatternKind::Tuple(items_pattern, _) | PatternKind::Or(items_pattern, _) => {
            for item in items_pattern {
                collect_pattern_completion_items(gcx, item, items, seen);
            }
        }
        PatternKind::Reference { pattern, .. } => {
            collect_pattern_completion_items(gcx, pattern, items, seen);
        }
        PatternKind::PathTuple { fields, .. } => {
            for field in fields {
                collect_pattern_completion_items(gcx, field, items, seen);
            }
        }
        _ => {}
    }
}

fn collect_scope_completion_items(
    gcx: Gcx<'_>,
    scope: Scope<'_>,
    items: &mut Vec<CompletionInfo>,
    seen: &mut FxHashSet<(String, CompletionKind)>,
    depth: usize,
) {
    if depth > 16 {
        return;
    }

    {
        let table = scope.table.borrow();
        for (symbol, entry) in table.iter() {
            let label = gcx.symbol_text(*symbol).to_string();
            if let Some(type_entry) = entry.ty {
                push_completion(
                    items,
                    seen,
                    completion_for_resolution(gcx, label.clone(), type_entry.resolution()),
                );
            }
            if !entry.values.is_empty() {
                let resolution = if entry.values.len() == 1 {
                    entry.values[0].resolution()
                } else {
                    AnyResolution::FunctionSet(
                        entry
                            .values
                            .iter()
                            .filter_map(|entry| entry.resolution().definition_id())
                            .collect(),
                    )
                };
                push_completion(
                    items,
                    seen,
                    completion_for_resolution(gcx, label.clone(), resolution),
                );
            }
        }
    }

    let globs = match scope.kind {
        crate::sema::resolve::models::ScopeKind::File(..)
        | crate::sema::resolve::models::ScopeKind::Block(..) => Some(&scope.glob_imports),
        crate::sema::resolve::models::ScopeKind::Definition(
            _,
            DefinitionKind::Module | DefinitionKind::Namespace,
        ) => Some(&scope.glob_exports),
        _ => None,
    };

    if let Some(globs) = globs {
        for usage in globs.borrow().iter() {
            if let Some(scope) = usage.module_scope.get() {
                collect_scope_completion_items(gcx, scope, items, seen, depth + 1);
            }
        }
    }
}

fn completion_for_resolution<LocalNode>(
    gcx: Gcx<'_>,
    label: String,
    resolution: AnyResolution<LocalNode>,
) -> CompletionInfo {
    match resolution {
        AnyResolution::Definition(def_id, kind) => CompletionInfo {
            label,
            kind: completion_kind_for_definition(kind),
            detail: completion_detail_for_definition(gcx, def_id, kind),
        },
        AnyResolution::FunctionSet(defs) => CompletionInfo {
            label,
            kind: CompletionKind::Function,
            detail: defs
                .first()
                .and_then(|def_id| {
                    completion_detail_for_definition(gcx, *def_id, DefinitionKind::Function)
                })
                .or_else(|| Some("overloaded function".into())),
        },
        AnyResolution::LocalVariable(_) => CompletionInfo {
            label,
            kind: CompletionKind::Variable,
            detail: Some("local variable".into()),
        },
        AnyResolution::PrimaryType(primary) => CompletionInfo {
            label: primary.name_str().to_string(),
            kind: CompletionKind::Type,
            detail: Some("builtin type".into()),
        },
        AnyResolution::StdItem(item) => CompletionInfo {
            label,
            kind: item
                .expected_def_kind()
                .map(completion_kind_for_definition)
                .unwrap_or(CompletionKind::Function),
            detail: Some("std item".into()),
        },
        AnyResolution::SelfTypeAlias(_) | AnyResolution::InterfaceSelfTypeParameter(_) => {
            CompletionInfo {
                label,
                kind: CompletionKind::TypeParameter,
                detail: Some("self type".into()),
            }
        }
        AnyResolution::SelfConstructor(def_id) => CompletionInfo {
            label,
            kind: CompletionKind::Function,
            detail: completion_detail_for_definition(gcx, def_id, DefinitionKind::Function),
        },
        AnyResolution::Error => CompletionInfo {
            label,
            kind: CompletionKind::Unknown,
            detail: None,
        },
    }
}

fn completion_kind_for_definition(kind: DefinitionKind) -> CompletionKind {
    match kind {
        DefinitionKind::Function
        | DefinitionKind::AssociatedFunction
        | DefinitionKind::AssociatedOperator => CompletionKind::Function,
        DefinitionKind::Struct => CompletionKind::Struct,
        DefinitionKind::Enum => CompletionKind::Enum,
        DefinitionKind::Interface => CompletionKind::Interface,
        DefinitionKind::Module => CompletionKind::Module,
        DefinitionKind::Namespace => CompletionKind::Namespace,
        DefinitionKind::Field => CompletionKind::Field,
        DefinitionKind::Variant | DefinitionKind::VariantConstructor(..) => CompletionKind::Variant,
        DefinitionKind::Constant | DefinitionKind::AssociatedConstant => CompletionKind::Constant,
        DefinitionKind::ModuleVariable => CompletionKind::Variable,
        DefinitionKind::AssociatedProperty => CompletionKind::Property,
        DefinitionKind::TypeAlias | DefinitionKind::AssociatedType => CompletionKind::TypeAlias,
        DefinitionKind::TypeParameter | DefinitionKind::ConstParameter => {
            CompletionKind::TypeParameter
        }
        DefinitionKind::Import
        | DefinitionKind::Export
        | DefinitionKind::Impl
        | DefinitionKind::OpaqueType => CompletionKind::Unknown,
    }
}

fn completion_detail_for_definition(
    gcx: Gcx<'_>,
    def_id: DefinitionID,
    kind: DefinitionKind,
) -> Option<String> {
    match kind {
        DefinitionKind::Function
        | DefinitionKind::AssociatedFunction
        | DefinitionKind::AssociatedOperator
        | DefinitionKind::VariantConstructor(..) => {
            crate::sema::models::format_definition_signature_for_display(gcx, def_id)
        }
        DefinitionKind::Struct
        | DefinitionKind::Enum
        | DefinitionKind::Interface
        | DefinitionKind::Module
        | DefinitionKind::Namespace
        | DefinitionKind::Field
        | DefinitionKind::Variant
        | DefinitionKind::Constant
        | DefinitionKind::AssociatedConstant
        | DefinitionKind::AssociatedProperty
        | DefinitionKind::ModuleVariable
        | DefinitionKind::TypeAlias
        | DefinitionKind::AssociatedType
        | DefinitionKind::TypeParameter
        | DefinitionKind::ConstParameter
        | DefinitionKind::OpaqueType => Some(kind.description().into()),
        _ => None,
    }
}

fn push_completion(
    items: &mut Vec<CompletionInfo>,
    seen: &mut FxHashSet<(String, CompletionKind)>,
    item: CompletionInfo,
) {
    if seen.insert((item.label.clone(), item.kind)) {
        items.push(item);
    }
}

fn member_completion_items_for_ty<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
    mode: MemberCompletionMode,
    current_def: Option<DefinitionID>,
) -> Vec<CompletionInfo> {
    let mut items = Vec::new();
    let mut seen = FxHashSet::default();
    let Some(head) = type_head_for_completion(gcx, ty) else {
        return items;
    };

    if matches!(mode, MemberCompletionMode::Instance) {
        collect_struct_field_completions(gcx, ty, &mut items, &mut seen);
        collect_property_completions(gcx, head, current_def, &mut items, &mut seen);
    } else {
        collect_enum_variant_completions(gcx, ty, current_def, &mut items, &mut seen);
    }

    collect_method_completions(gcx, head, mode, current_def, &mut items, &mut seen);
    items
}

fn static_member_completion_items_for_definition(
    gcx: Gcx<'_>,
    def_id: DefinitionID,
    current_def: Option<DefinitionID>,
) -> Vec<CompletionInfo> {
    let mut items = Vec::new();
    let mut seen = FxHashSet::default();
    let Some(kind) = gcx.try_definition_kind(def_id) else {
        return items;
    };

    if kind == DefinitionKind::Enum
        && let Some(enum_def) = gcx.try_get_enum_definition(def_id)
    {
        for variant in enum_def.variants {
            if !definition_is_visible_for_completion(gcx, variant.ctor_def_id, current_def) {
                continue;
            }
            push_completion(
                &mut items,
                &mut seen,
                CompletionInfo {
                    label: gcx.symbol_text(variant.name).to_string(),
                    kind: CompletionKind::Variant,
                    detail: Some("variant".into()),
                },
            );
        }
    }

    if matches!(
        kind,
        DefinitionKind::Struct | DefinitionKind::Enum | DefinitionKind::Interface
    ) {
        collect_method_completions(
            gcx,
            TypeHead::Nominal(def_id),
            MemberCompletionMode::Static,
            current_def,
            &mut items,
            &mut seen,
        );
    }

    items
}

fn type_definition_id_for_completion(ty: &Type) -> Option<DefinitionID> {
    match &ty.kind {
        hir::TypeKind::Nominal(ResolvedPath::Resolved(path)) => path
            .segments
            .last()
            .and_then(|segment| segment.resolution.definition_id()),
        _ => None,
    }
}

fn type_head_for_completion<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> Option<TypeHead> {
    match ty.kind() {
        TyKind::Bool => Some(TypeHead::Primary(PrimaryType::Bool)),
        TyKind::Rune => Some(TypeHead::Primary(PrimaryType::Rune)),
        TyKind::String => Some(TypeHead::Primary(PrimaryType::String)),
        TyKind::Int(k) => Some(TypeHead::Primary(PrimaryType::Int(k))),
        TyKind::UInt(k) => Some(TypeHead::Primary(PrimaryType::UInt(k))),
        TyKind::Float(k) => Some(TypeHead::Primary(PrimaryType::Float(k))),
        TyKind::Adt(def, _) => Some(TypeHead::Nominal(def.id)),
        TyKind::Reference(_, mutbl) => Some(TypeHead::Reference(mutbl)),
        TyKind::Pointer(_, mutbl) => Some(TypeHead::Pointer(mutbl)),
        TyKind::Tuple(items) => Some(TypeHead::Tuple(items.len() as u16)),
        TyKind::Array { .. } => Some(TypeHead::Array),
        TyKind::Closure { closure_def_id, .. } => Some(TypeHead::Closure(closure_def_id)),
        TyKind::Alias { def_id, .. } => gcx
            .try_get_alias_type(def_id)
            .and_then(|ty| type_head_for_completion(gcx, ty)),
        _ => None,
    }
}

fn collect_struct_field_completions(
    gcx: Gcx<'_>,
    ty: Ty<'_>,
    items: &mut Vec<CompletionInfo>,
    seen: &mut FxHashSet<(String, CompletionKind)>,
) {
    match ty.kind() {
        TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => {
            collect_struct_field_completions(gcx, inner, items, seen)
        }
        TyKind::Alias { def_id, .. } => {
            if let Some(alias_ty) = gcx.try_get_alias_type(def_id) {
                collect_struct_field_completions(gcx, alias_ty, items, seen);
            }
        }
        TyKind::Adt(def, _) if def.kind == AdtKind::Struct => {
            if let Some(struct_def) = gcx.try_get_struct_definition(def.id) {
                for field in struct_def.fields {
                    let ident = gcx.definition_ident(field.def_id);
                    push_completion(
                        items,
                        seen,
                        CompletionInfo {
                            label: gcx.symbol_text(ident.symbol).to_string(),
                            kind: CompletionKind::Field,
                            detail: Some(field.ty.format(gcx)),
                        },
                    );
                }
            }
        }
        _ => {}
    }
}

fn collect_enum_variant_completions(
    gcx: Gcx<'_>,
    ty: Ty<'_>,
    current_def: Option<DefinitionID>,
    items: &mut Vec<CompletionInfo>,
    seen: &mut FxHashSet<(String, CompletionKind)>,
) {
    if let TyKind::Adt(def, _) = ty.kind()
        && def.kind == AdtKind::Enum
        && let Some(enum_def) = gcx.try_get_enum_definition(def.id)
    {
        for variant in enum_def.variants {
            if !definition_is_visible_for_completion(gcx, variant.ctor_def_id, current_def) {
                continue;
            }
            push_completion(
                items,
                seen,
                CompletionInfo {
                    label: gcx.symbol_text(variant.name).to_string(),
                    kind: CompletionKind::Variant,
                    detail: Some("variant".into()),
                },
            );
        }
    }
}

fn collect_property_completions(
    gcx: Gcx<'_>,
    head: TypeHead,
    current_def: Option<DefinitionID>,
    items: &mut Vec<CompletionInfo>,
    seen: &mut FxHashSet<(String, CompletionKind)>,
) {
    let mut properties = Vec::new();
    gcx.with_session_type_database(|db| {
        if let Some(map) = db.type_head_to_properties.get(&head) {
            properties.extend(map.values().copied());
        }
    });
    for index in gcx.visible_packages() {
        gcx.with_type_database(index, |db| {
            if let Some(map) = db.type_head_to_properties.get(&head) {
                properties.extend(map.values().copied());
            }
        });
    }

    for property in properties {
        if !definition_is_visible_for_completion(gcx, property.property_id, current_def) {
            continue;
        }
        let ident = gcx.definition_ident(property.property_id);
        push_completion(
            items,
            seen,
            CompletionInfo {
                label: gcx.symbol_text(ident.symbol).to_string(),
                kind: CompletionKind::Property,
                detail: Some(property.ty.format(gcx)),
            },
        );
    }
}

fn collect_method_completions(
    gcx: Gcx<'_>,
    head: TypeHead,
    mode: MemberCompletionMode,
    current_def: Option<DefinitionID>,
    items: &mut Vec<CompletionInfo>,
    seen: &mut FxHashSet<(String, CompletionKind)>,
) {
    let mut methods = Vec::new();
    let mut collect = |db: &mut crate::compile::context::TypeDatabase<'_>| {
        if let Some(index) = db.type_head_to_members.get(&head) {
            let source = match mode {
                MemberCompletionMode::Instance => &index.inherent_instance,
                MemberCompletionMode::Static => &index.inherent_static,
            };
            for set in source.values() {
                methods.extend(set.members.iter().copied());
            }
            if matches!(mode, MemberCompletionMode::Instance) {
                for defs in index.trait_methods_by_name.values() {
                    methods.extend(defs.iter().copied());
                }
            }
        }
    };

    gcx.with_session_type_database(&mut collect);
    for index in gcx.visible_packages() {
        gcx.with_type_database(index, &mut collect);
    }

    let mut seen_defs = FxHashSet::default();
    for def_id in methods {
        if !seen_defs.insert(def_id)
            || !definition_is_visible_for_completion(gcx, def_id, current_def)
        {
            continue;
        }
        let Some(kind) = gcx.try_definition_kind(def_id) else {
            continue;
        };
        let Some(ident) = gcx.try_definition_ident(def_id) else {
            continue;
        };
        push_completion(
            items,
            seen,
            CompletionInfo {
                label: gcx.symbol_text(ident.symbol).to_string(),
                kind: CompletionKind::Method,
                detail: completion_detail_for_definition(gcx, def_id, kind),
            },
        );
    }
}

fn definition_is_visible_for_completion(
    gcx: Gcx<'_>,
    target: DefinitionID,
    current_def: Option<DefinitionID>,
) -> bool {
    current_def
        .map(|current_def| gcx.is_definition_visible(target, current_def))
        .unwrap_or_else(|| {
            matches!(
                gcx.definition_visibility(target),
                crate::sema::resolve::models::Visibility::Public
            )
        })
}

fn file_completion_span(file: FileID) -> Span {
    Span {
        file,
        start: Position { line: 0, offset: 0 },
        end: Position {
            line: usize::MAX,
            offset: usize::MAX,
        },
    }
}

fn module_completion_span(module: &Module) -> Span {
    module
        .declarations
        .iter()
        .map(|declaration| declaration.span)
        .min_by(|lhs, rhs| compare_navigation_spans(*lhs, *rhs))
        .unwrap_or_else(|| {
            module
                .files
                .first()
                .copied()
                .map(file_completion_span)
                .unwrap_or_else(|| Span::empty(FileID::new(0)))
        })
}

fn call_signature_candidates<'ctx>(
    gcx: Gcx<'ctx>,
    results: Option<&TypeCheckResults<'ctx>>,
    node: &Expression,
    callee: Option<&Expression>,
) -> Vec<SignatureCandidate> {
    let def_id = results
        .and_then(|results| results.overload_source(node.id))
        .or_else(|| {
            callee
                .and_then(|callee| expression_resolution_for_ide(gcx, results, callee))
                .and_then(|resolution| resolution.definition_id())
        });

    def_id
        .and_then(|def_id| signature_candidate_for_definition(gcx, def_id))
        .into_iter()
        .collect()
}

fn signature_candidate_for_definition(
    gcx: Gcx<'_>,
    def_id: DefinitionID,
) -> Option<SignatureCandidate> {
    let label = crate::sema::models::format_definition_signature_for_display(gcx, def_id)?;
    let parameters =
        crate::sema::models::format_definition_signature_parameter_labels_for_display(gcx, def_id)?;
    Some(SignatureCandidate { label, parameters })
}

fn collect_document_symbol_data(gcx: Gcx<'_>, package: &hir::Package) -> DocumentSymbolData {
    fn module_symbols(gcx: Gcx<'_>, module: &Module, items: &mut Vec<DocumentSymbolInfo>) {
        items.extend(
            module
                .declarations
                .iter()
                .filter_map(|declaration| declaration_symbol(gcx, declaration)),
        );
        for submodule in &module.submodules {
            module_symbols(gcx, submodule, items);
        }
    }

    fn declaration_symbol(gcx: Gcx<'_>, declaration: &Declaration) -> Option<DocumentSymbolInfo> {
        let name = gcx.symbol_text(declaration.identifier.symbol).to_string();
        let mut symbol = DocumentSymbolInfo {
            name,
            detail: signature_candidate_for_definition(gcx, declaration.id).map(|item| item.label),
            kind: DocumentSymbolKind::Type,
            span: declaration.span,
            selection_span: declaration.identifier.span,
            children: Vec::new(),
        };
        match &declaration.kind {
            DeclarationKind::Namespace(namespace) => {
                symbol.kind = DocumentSymbolKind::Namespace;
                symbol.children = namespace
                    .declarations
                    .iter()
                    .filter_map(|item| declaration_symbol(gcx, item))
                    .collect();
            }
            DeclarationKind::Struct(definition) => {
                symbol.kind = DocumentSymbolKind::Struct;
                symbol.children = definition
                    .fields
                    .iter()
                    .map(|field| field_symbol(gcx, field))
                    .collect();
            }
            DeclarationKind::Enum(definition) => {
                symbol.kind = DocumentSymbolKind::Enum;
                symbol.children = definition
                    .variants
                    .iter()
                    .map(|variant| variant_symbol(gcx, variant))
                    .collect();
            }
            DeclarationKind::Interface(definition) => {
                symbol.kind = DocumentSymbolKind::Interface;
                symbol.children = definition
                    .declarations
                    .iter()
                    .map(|item| associated_symbol(gcx, item))
                    .collect();
            }
            DeclarationKind::Function(_) => symbol.kind = DocumentSymbolKind::Function,
            DeclarationKind::TypeAlias(_) => symbol.kind = DocumentSymbolKind::TypeAlias,
            DeclarationKind::Constant(_) => symbol.kind = DocumentSymbolKind::Constant,
            DeclarationKind::StaticVariable(_) => symbol.kind = DocumentSymbolKind::Variable,
            DeclarationKind::Impl(definition) => {
                let target = gcx
                    .get_impl_target_ty(declaration.id)
                    .map(|ty| ty.format(gcx))
                    .unwrap_or_else(|| "target".to_string());
                symbol.name = format!("impl {target}");
                symbol.kind = DocumentSymbolKind::Namespace;
                symbol.selection_span = definition.target.span;
                symbol.children = definition
                    .declarations
                    .iter()
                    .map(|item| associated_symbol(gcx, item))
                    .collect();
            }
            DeclarationKind::OpaqueType => symbol.kind = DocumentSymbolKind::Type,
            DeclarationKind::Import(_)
            | DeclarationKind::Export(_)
            | DeclarationKind::Malformed => {
                return None;
            }
        }
        Some(symbol)
    }

    fn associated_symbol(gcx: Gcx<'_>, declaration: &AssociatedDeclaration) -> DocumentSymbolInfo {
        let kind = match declaration.kind {
            AssociatedDeclarationKind::Function(_) => DocumentSymbolKind::Method,
            AssociatedDeclarationKind::Constant(_) => DocumentSymbolKind::Constant,
            AssociatedDeclarationKind::Type(_) => DocumentSymbolKind::TypeAlias,
            AssociatedDeclarationKind::Property(_) => DocumentSymbolKind::Property,
        };
        DocumentSymbolInfo {
            name: gcx.symbol_text(declaration.identifier.symbol).to_string(),
            detail: signature_candidate_for_definition(gcx, declaration.id).map(|item| item.label),
            kind,
            span: declaration.span,
            selection_span: declaration.identifier.span,
            children: Vec::new(),
        }
    }

    fn field_symbol(gcx: Gcx<'_>, field: &FieldDefinition) -> DocumentSymbolInfo {
        DocumentSymbolInfo {
            name: gcx.symbol_text(field.identifier.symbol).to_string(),
            detail: None,
            kind: DocumentSymbolKind::Field,
            span: field.span,
            selection_span: field.identifier.span,
            children: Vec::new(),
        }
    }

    fn variant_symbol(gcx: Gcx<'_>, variant: &Variant) -> DocumentSymbolInfo {
        let children = match &variant.kind {
            hir::VariantKind::Unit => Vec::new(),
            hir::VariantKind::Tuple(fields) => fields
                .iter()
                .map(|field| field_symbol(gcx, field))
                .collect(),
        };
        DocumentSymbolInfo {
            name: gcx.symbol_text(variant.identifier.symbol).to_string(),
            detail: None,
            kind: DocumentSymbolKind::EnumMember,
            span: variant.span,
            selection_span: variant.identifier.span,
            children,
        }
    }

    let mut items = Vec::new();
    module_symbols(gcx, &package.root, &mut items);
    DocumentSymbolData { items }
}

#[derive(Debug, Clone, Copy)]
struct SemanticClassification {
    kind: SemanticTokenKind,
    readonly: bool,
    static_member: bool,
    async_member: bool,
    default_library: bool,
}

fn semantic_classification_for_definition(
    gcx: Gcx<'_>,
    def_id: DefinitionID,
) -> Option<SemanticClassification> {
    let kind = match gcx.definition_kind(def_id) {
        DefinitionKind::Module | DefinitionKind::Namespace => SemanticTokenKind::Namespace,
        DefinitionKind::Struct => SemanticTokenKind::Struct,
        DefinitionKind::Enum => SemanticTokenKind::Enum,
        DefinitionKind::Interface => SemanticTokenKind::Interface,
        DefinitionKind::TypeAlias | DefinitionKind::OpaqueType => SemanticTokenKind::Type,
        DefinitionKind::TypeParameter | DefinitionKind::ConstParameter => {
            SemanticTokenKind::TypeParameter
        }
        DefinitionKind::Function | DefinitionKind::VariantConstructor(_) => {
            SemanticTokenKind::Function
        }
        DefinitionKind::AssociatedFunction | DefinitionKind::AssociatedOperator => {
            SemanticTokenKind::Method
        }
        DefinitionKind::Field | DefinitionKind::AssociatedProperty => SemanticTokenKind::Property,
        DefinitionKind::Constant
        | DefinitionKind::AssociatedConstant
        | DefinitionKind::ModuleVariable => SemanticTokenKind::Variable,
        DefinitionKind::Variant => SemanticTokenKind::EnumMember,
        DefinitionKind::Impl | DefinitionKind::Import | DefinitionKind::Export => return None,
        DefinitionKind::AssociatedType => SemanticTokenKind::Type,
    };
    let definition_kind = gcx.definition_kind(def_id);
    Some(SemanticClassification {
        kind,
        readonly: matches!(
            definition_kind,
            DefinitionKind::Constant
                | DefinitionKind::AssociatedConstant
                | DefinitionKind::Variant
                | DefinitionKind::TypeParameter
                | DefinitionKind::ConstParameter
        ),
        static_member: matches!(
            definition_kind,
            DefinitionKind::AssociatedFunction
                | DefinitionKind::AssociatedConstant
                | DefinitionKind::AssociatedProperty
                | DefinitionKind::AssociatedOperator
                | DefinitionKind::AssociatedType
        ),
        async_member: matches!(
            definition_kind,
            DefinitionKind::Function | DefinitionKind::AssociatedFunction
        ) && gcx.definition_is_async(def_id),
        default_library: gcx.is_std_package(def_id.package()),
    })
}

struct LocalSemanticVisitor {
    classifications: FxHashMap<hir::NodeID, SemanticClassification>,
    definition_readonly: FxHashMap<DefinitionID, bool>,
}

impl LocalSemanticVisitor {
    fn record_pattern(&mut self, pattern: &Pattern, kind: SemanticTokenKind, readonly: bool) {
        match &pattern.kind {
            PatternKind::Binding { .. } => {
                self.classifications.insert(
                    pattern.id,
                    SemanticClassification {
                        kind,
                        readonly,
                        static_member: false,
                        async_member: false,
                        default_library: false,
                    },
                );
            }
            PatternKind::Tuple(items, _) | PatternKind::Or(items, _) => {
                for item in items {
                    self.record_pattern(item, kind, readonly);
                }
            }
            PatternKind::Reference { pattern, .. } => self.record_pattern(pattern, kind, readonly),
            PatternKind::PathTuple { fields, .. } => {
                for field in fields {
                    self.record_pattern(field, kind, readonly);
                }
            }
            _ => {}
        }
    }
}

impl HirVisitor for LocalSemanticVisitor {
    fn visit_declaration(&mut self, node: &Declaration) {
        if let DeclarationKind::StaticVariable(variable) = &node.kind {
            self.definition_readonly
                .insert(node.id, variable.mutability == hir::Mutability::Immutable);
        }
        walk_declaration(self, node)
    }

    fn visit_field_definition(&mut self, node: &FieldDefinition) {
        self.definition_readonly
            .insert(node.def_id, node.mutability == hir::Mutability::Immutable);
        hir::walk_field_definition(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &AssociatedDeclaration,
        context: hir::AssocContext,
    ) {
        if let AssociatedDeclarationKind::Property(property) = &node.kind {
            self.definition_readonly
                .insert(node.id, property.setter_id.is_none());
        }
        walk_assoc_declaration(self, node, context)
    }

    fn visit_function_parameter(&mut self, node: &hir::FunctionParameter) {
        self.classifications.insert(
            node.id,
            SemanticClassification {
                kind: SemanticTokenKind::Parameter,
                readonly: true,
                static_member: false,
                async_member: false,
                default_library: false,
            },
        );
        hir::walk_function_parameter(self, node)
    }

    fn visit_local(&mut self, node: &hir::Local) {
        self.record_pattern(
            &node.pattern,
            SemanticTokenKind::Variable,
            node.mutability == hir::Mutability::Immutable,
        );
        hir::walk_local(self, node)
    }

    fn visit_expression(&mut self, node: &Expression) {
        if let ExpressionKind::Closure(closure) = &node.kind {
            for parameter in &closure.params {
                self.record_pattern(&parameter.pattern, SemanticTokenKind::Parameter, true);
            }
        }
        walk_expression(self, node)
    }
}

fn collect_semantic_token_data<'ctx>(
    gcx: Gcx<'ctx>,
    package: &hir::Package,
    results: Option<&TypeCheckResults<'ctx>>,
) -> SemanticTokenData {
    let references = collect_reference_data(gcx, package, results);
    let mut local_visitor = LocalSemanticVisitor {
        classifications: FxHashMap::default(),
        definition_readonly: FxHashMap::default(),
    };
    local_visitor.visit_package(package);

    let mut items = Vec::new();
    for group in references.groups {
        let classification =
            match group.key {
                ReferenceKey::Definition(def_id) => {
                    semantic_classification_for_definition(gcx, def_id).map(|mut classification| {
                        if let Some(readonly) = local_visitor.definition_readonly.get(&def_id) {
                            classification.readonly = *readonly;
                        }
                        classification
                    })
                }
                ReferenceKey::Local(id) => local_visitor.classifications.get(&id).copied().or(
                    Some(SemanticClassification {
                        kind: SemanticTokenKind::Variable,
                        readonly: true,
                        static_member: false,
                        async_member: false,
                        default_library: false,
                    }),
                ),
            };
        let Some(classification) = classification else {
            continue;
        };
        for reference in group.items {
            items.push(SemanticTokenInfo {
                span: reference.span,
                kind: classification.kind,
                modifiers: SemanticTokenModifiers {
                    declaration: reference.is_declaration,
                    readonly: classification.readonly,
                    static_member: classification.static_member,
                    async_member: classification.async_member,
                    default_library: classification.default_library,
                },
            });
        }
    }
    items.sort_by(|lhs, rhs| compare_navigation_spans(lhs.span, rhs.span));
    items.dedup_by(|lhs, rhs| lhs.span == rhs.span);
    SemanticTokenData { items }
}

struct InlayHintVisitor<'ctx, 'results> {
    gcx: Gcx<'ctx>,
    results: Option<&'results TypeCheckResults<'ctx>>,
    items: Vec<InlayHintInfo>,
}

impl<'ctx, 'results> InlayHintVisitor<'ctx, 'results> {
    fn push_pattern_type_hints(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Binding { name, .. } => {
                let Some(ty) = self
                    .results
                    .and_then(|results| results.try_node_type(pattern.id))
                else {
                    return;
                };
                if ty.is_error() || ty.is_infer() || ty.contains_inference() {
                    return;
                }
                self.items.push(InlayHintInfo {
                    position: name.span.end,
                    file: name.span.file,
                    label: format!(": {}", ty.format(self.gcx)),
                    kind: InlayHintKind::Type,
                });
            }
            PatternKind::Tuple(items, _) | PatternKind::Or(items, _) => {
                for item in items {
                    self.push_pattern_type_hints(item);
                }
            }
            PatternKind::Reference { pattern, .. } => self.push_pattern_type_hints(pattern),
            PatternKind::PathTuple { fields, .. } => {
                for field in fields {
                    self.push_pattern_type_hints(field);
                }
            }
            _ => {}
        }
    }

    fn push_parameter_hints(&mut self, node: &Expression) {
        let (arguments, def_id, is_method) = match &node.kind {
            ExpressionKind::Call { callee, arguments } => {
                let def_id = self
                    .results
                    .and_then(|results| results.overload_source(node.id))
                    .or_else(|| {
                        expression_resolution_for_ide(self.gcx, self.results, callee)
                            .and_then(|resolution| resolution.definition_id())
                    });
                (arguments, def_id, false)
            }
            ExpressionKind::MethodCall { arguments, .. } => (
                arguments,
                self.results
                    .and_then(|results| results.overload_source(node.id)),
                true,
            ),
            _ => return,
        };
        let Some(signature) = def_id.and_then(|id| self.gcx.try_get_signature(id)) else {
            return;
        };
        let mut parameters = signature.inputs.as_slice();
        if is_method
            && parameters
                .first()
                .is_some_and(|parameter| self.gcx.symbol_text(parameter.name).as_ref() == "self")
        {
            parameters = &parameters[1..];
        }

        for (index, (argument, parameter)) in arguments.iter().zip(parameters).enumerate() {
            if argument.label.is_some() || (signature.is_variadic && index + 1 == parameters.len())
            {
                continue;
            }
            let name = self.gcx.symbol_text(parameter.name);
            if name.as_ref() == "_" || name.as_ref() == "self" {
                continue;
            }
            self.items.push(InlayHintInfo {
                position: argument.expression.span.start,
                file: argument.expression.span.file,
                label: format!("{name}:"),
                kind: InlayHintKind::Parameter,
            });
        }
    }
}

impl<'ctx, 'results> HirVisitor for InlayHintVisitor<'ctx, 'results> {
    fn visit_local(&mut self, node: &hir::Local) {
        if node.ty.is_none() {
            self.push_pattern_type_hints(&node.pattern);
        }
        hir::walk_local(self, node)
    }

    fn visit_expression(&mut self, node: &Expression) {
        if let ExpressionKind::Closure(closure) = &node.kind {
            for parameter in &closure.params {
                if parameter.ty.is_none() {
                    self.push_pattern_type_hints(&parameter.pattern);
                }
            }
        }
        self.push_parameter_hints(node);
        walk_expression(self, node)
    }
}

fn collect_inlay_hint_data<'ctx>(
    gcx: Gcx<'ctx>,
    package: &hir::Package,
    results: Option<&TypeCheckResults<'ctx>>,
) -> InlayHintData {
    let mut visitor = InlayHintVisitor {
        gcx,
        results,
        items: Vec::new(),
    };
    visitor.visit_package(package);
    visitor.items.sort_by(|lhs, rhs| {
        lhs.file
            .cmp(&rhs.file)
            .then_with(|| compare_positions(lhs.position, rhs.position))
            .then_with(|| lhs.label.cmp(&rhs.label))
    });
    visitor.items.dedup_by(|lhs, rhs| {
        lhs.file == rhs.file && lhs.position == rhs.position && lhs.label == rhs.label
    });
    InlayHintData {
        items: visitor.items,
    }
}

fn collect_ide_artifacts<'ctx>(
    gcx: Gcx<'ctx>,
    package: &hir::Package,
    results: Option<&TypeCheckResults<'ctx>>,
    module_targets: &FxHashMap<DefinitionID, Span>,
    status: AnalysisStatus,
) -> IdeArtifacts {
    IdeArtifacts {
        navigation: collect_navigation_data(gcx, package, results, module_targets),
        references: collect_reference_data(gcx, package, results),
        document_symbols: collect_document_symbol_data(gcx, package),
        semantic_tokens: collect_semantic_token_data(gcx, package, results),
        inlay_hints: collect_inlay_hint_data(gcx, package, results),
        signatures: collect_signature_help_data(gcx, package, results),
        completions: collect_completion_data(gcx, package, results),
        status,
    }
}

pub fn signature_help_at(
    snapshot: &AnalysisSnapshot,
    _source_text: &str,
    file_id: FileID,
    position: Position,
) -> Option<SignatureHelpResult> {
    let site_index = find_signature_site_index(&snapshot.signatures, file_id, position)?;
    let site = &snapshot.signatures.sites[site_index];
    let active_parameter = active_signature_parameter(site, position);
    let clamped_parameter = site
        .signatures
        .first()
        .map(|signature| {
            if signature.parameters.is_empty() {
                0
            } else {
                active_parameter.min(signature.parameters.len() - 1)
            }
        })
        .unwrap_or(0);
    Some(SignatureHelpResult {
        signatures: site.signatures.clone(),
        active_signature: 0,
        active_parameter: clamped_parameter,
    })
}

pub fn completion_at(
    snapshot: &AnalysisSnapshot,
    _source_text: &str,
    file_id: FileID,
    position: Position,
) -> Vec<CompletionInfo> {
    if let Some(site_index) =
        find_member_completion_site_index(&snapshot.completions, file_id, position)
    {
        return sorted_completion_items(
            snapshot.completions.member_sites[site_index].items.clone(),
        );
    }

    let Some(scope_index) = find_completion_scope_index(&snapshot.completions, file_id, position)
    else {
        return Vec::new();
    };
    sorted_completion_items(snapshot.completions.scopes[scope_index].items.clone())
}

pub fn references_at(
    snapshot: &AnalysisSnapshot,
    file_id: FileID,
    position: Position,
    include_declaration: bool,
) -> Vec<ReferenceInfo> {
    let Some(key) = reference_key_at(&snapshot.references, file_id, position) else {
        return Vec::new();
    };
    let Some(group) = snapshot
        .references
        .groups
        .iter()
        .find(|group| group.key == key)
    else {
        return Vec::new();
    };

    group
        .items
        .iter()
        .filter(|item| include_declaration || !item.is_declaration)
        .cloned()
        .collect()
}

pub fn document_highlights_at(
    snapshot: &AnalysisSnapshot,
    file_id: FileID,
    position: Position,
) -> Vec<ReferenceInfo> {
    references_at(snapshot, file_id, position, true)
        .into_iter()
        .filter(|item| item.span.file == file_id)
        .collect()
}

pub fn document_symbols_for_file(
    snapshot: &AnalysisSnapshot,
    file_id: FileID,
) -> Vec<DocumentSymbolInfo> {
    fn filter_symbol(symbol: &DocumentSymbolInfo, file_id: FileID) -> Option<DocumentSymbolInfo> {
        if symbol.span.file != file_id {
            return None;
        }
        let mut symbol = symbol.clone();
        symbol.children = symbol
            .children
            .iter()
            .filter_map(|child| filter_symbol(child, file_id))
            .collect();
        Some(symbol)
    }

    snapshot
        .document_symbols
        .items
        .iter()
        .filter_map(|symbol| filter_symbol(symbol, file_id))
        .collect()
}

pub fn semantic_tokens_for_file(
    snapshot: &AnalysisSnapshot,
    file_id: FileID,
) -> Vec<SemanticTokenInfo> {
    snapshot
        .semantic_tokens
        .items
        .iter()
        .filter(|item| item.span.file == file_id)
        .copied()
        .collect()
}

pub fn inlay_hints_in_range(
    snapshot: &AnalysisSnapshot,
    file_id: FileID,
    start: Position,
    end: Position,
) -> Vec<InlayHintInfo> {
    snapshot
        .inlay_hints
        .items
        .iter()
        .filter(|item| {
            item.file == file_id
                && compare_positions(item.position, start) != Ordering::Less
                && compare_positions(item.position, end) != Ordering::Greater
        })
        .cloned()
        .collect()
}

pub fn reference_span_at(
    snapshot: &AnalysisSnapshot,
    file_id: FileID,
    position: Position,
) -> Option<Span> {
    let index = reference_mention_index_at(&snapshot.references, file_id, position)?;
    Some(snapshot.references.mentions[index].span)
}

fn reference_key_at(
    data: &ReferenceData,
    file_id: FileID,
    position: Position,
) -> Option<ReferenceKey> {
    let index = reference_mention_index_at(data, file_id, position)?;
    Some(data.mentions[index].key)
}

fn reference_mention_index_at(
    data: &ReferenceData,
    file_id: FileID,
    position: Position,
) -> Option<usize> {
    let spans: Vec<_> = data.mentions.iter().map(|mention| mention.span).collect();
    find_innermost_span_index(&spans, &data.parents, file_id, position)
}

fn find_completion_scope_index(
    data: &CompletionData,
    file_id: FileID,
    position: Position,
) -> Option<usize> {
    find_deepest_matching_span(
        data.scopes
            .iter()
            .enumerate()
            .map(|(index, scope)| (index, scope.span)),
        file_id,
        position,
    )
}

fn find_member_completion_site_index(
    data: &CompletionData,
    file_id: FileID,
    position: Position,
) -> Option<usize> {
    find_deepest_matching_span(
        data.member_sites
            .iter()
            .enumerate()
            .map(|(index, site)| (index, site.span)),
        file_id,
        position,
    )
}

fn find_deepest_matching_span(
    spans: impl Iterator<Item = (usize, Span)>,
    file_id: FileID,
    position: Position,
) -> Option<usize> {
    spans
        .filter(|(_, span)| span_contains_position(*span, file_id, position))
        .max_by(|(_, lhs), (_, rhs)| compare_navigation_spans(*lhs, *rhs))
        .map(|(index, _)| index)
}

fn sorted_completion_items(mut items: Vec<CompletionInfo>) -> Vec<CompletionInfo> {
    items.sort_by(|lhs, rhs| {
        lhs.label
            .cmp(&rhs.label)
            .then_with(|| completion_kind_order(lhs.kind).cmp(&completion_kind_order(rhs.kind)))
    });
    items
}

fn completion_kind_order(kind: CompletionKind) -> u8 {
    match kind {
        CompletionKind::Function => 0,
        CompletionKind::Method => 1,
        CompletionKind::Variable => 2,
        CompletionKind::Field => 3,
        CompletionKind::Property => 4,
        CompletionKind::Struct => 5,
        CompletionKind::Enum => 6,
        CompletionKind::Interface => 7,
        CompletionKind::Variant => 8,
        CompletionKind::TypeAlias => 9,
        CompletionKind::TypeParameter => 10,
        CompletionKind::Type => 11,
        CompletionKind::Module => 12,
        CompletionKind::Namespace => 13,
        CompletionKind::Package => 14,
        CompletionKind::Constant => 15,
        CompletionKind::Keyword => 16,
        CompletionKind::Unknown => 17,
    }
}

fn find_innermost_span_index(
    spans: &[Span],
    parents: &[Option<usize>],
    file_id: FileID,
    position: Position,
) -> Option<usize> {
    let index = spans.partition_point(|span| {
        span.file < file_id
            || (span.file == file_id
                && compare_positions(span.start, position) != Ordering::Greater)
    });
    if index == 0 {
        return None;
    }

    let mut current = index - 1;
    loop {
        let span = spans[current];
        if span.file == file_id && span_contains_position(span, file_id, position) {
            return Some(current);
        }
        current = parents[current]?;
    }
}

fn find_signature_site_index(
    data: &SignatureHelpData,
    file_id: FileID,
    position: Position,
) -> Option<usize> {
    let spans: Vec<_> = data.sites.iter().map(|site| site.span).collect();
    find_innermost_span_index(&spans, &data.parents, file_id, position)
}

fn active_signature_parameter(site: &SignatureHelpSite, position: Position) -> usize {
    for (index, argument) in site.arguments.iter().enumerate() {
        if compare_positions(position, argument.end) != Ordering::Greater {
            return index;
        }
    }
    site.arguments.len()
}

fn span_contains_position(span: Span, file_id: FileID, position: Position) -> bool {
    span.file == file_id
        && compare_positions(span.start, position) != Ordering::Greater
        && compare_positions(span.end, position) != Ordering::Less
}

fn expression_resolution_for_ide<'ctx>(
    gcx: Gcx<'ctx>,
    results: Option<&TypeCheckResults<'ctx>>,
    node: &Expression,
) -> Option<Resolution> {
    results
        .and_then(|results| results.overload_source(node.id))
        .map(|def_id| Resolution::Definition(def_id, gcx.definition_kind(def_id)))
        .or_else(|| results.and_then(|results| results.value_resolution(node.id)))
        .or_else(|| expression_fallback_resolution(node))
}

fn expression_fallback_resolution(node: &Expression) -> Option<Resolution> {
    match &node.kind {
        ExpressionKind::Path(path) => resolved_path_resolution(path),
        _ => None,
    }
}

fn pattern_fallback_resolution(node: &Pattern) -> Option<Resolution> {
    match &node.kind {
        PatternKind::Member(path) => pattern_path_resolution(path),
        PatternKind::PathTuple { path, .. } => pattern_path_resolution(path),
        _ => None,
    }
}

fn resolved_path_resolution(path: &ResolvedPath) -> Option<Resolution> {
    match path {
        ResolvedPath::Resolved(path) => Some(path.resolution.clone()),
        ResolvedPath::Relative(..) => None,
    }
}

fn pattern_path_resolution(path: &PatternPath) -> Option<Resolution> {
    match path {
        PatternPath::Qualified { path } => resolved_path_resolution(path),
        PatternPath::Inferred { .. } => None,
    }
}

fn pattern_navigation_span(node: &Pattern) -> Span {
    match &node.kind {
        PatternKind::Binding { name, .. } => name.span,
        PatternKind::Member(PatternPath::Inferred { name, .. }) => name.span,
        PatternKind::PathTuple {
            path: PatternPath::Inferred { name, .. },
            ..
        } => name.span,
        PatternKind::Member(PatternPath::Qualified {
            path: ResolvedPath::Resolved(path),
        })
        | PatternKind::PathTuple {
            path:
                PatternPath::Qualified {
                    path: ResolvedPath::Resolved(path),
                },
            ..
        } => path
            .segments
            .last()
            .map(|segment| segment.span)
            .unwrap_or(node.span),
        _ => node.span,
    }
}

fn compare_navigation_spans(lhs: Span, rhs: Span) -> Ordering {
    lhs.file
        .cmp(&rhs.file)
        .then_with(|| compare_positions(lhs.start, rhs.start))
        .then_with(|| compare_positions(rhs.end, lhs.end))
}

fn compare_positions(lhs: crate::span::Position, rhs: crate::span::Position) -> Ordering {
    lhs.line
        .cmp(&rhs.line)
        .then_with(|| lhs.offset.cmp(&rhs.offset))
}

fn compare_reference_keys(lhs: ReferenceKey, rhs: ReferenceKey) -> Ordering {
    match (lhs, rhs) {
        (ReferenceKey::Definition(lhs), ReferenceKey::Definition(rhs)) => lhs.cmp(&rhs),
        (ReferenceKey::Local(lhs), ReferenceKey::Local(rhs)) => lhs.cmp(&rhs),
        (ReferenceKey::Definition(_), ReferenceKey::Local(_)) => Ordering::Less,
        (ReferenceKey::Local(_), ReferenceKey::Definition(_)) => Ordering::Greater,
    }
}

fn build_parent_links(spans: impl Iterator<Item = Span>) -> Vec<Option<usize>> {
    let spans: Vec<_> = spans.collect();
    let mut parents = vec![None; spans.len()];
    let mut stack: Vec<usize> = Vec::new();
    let mut current_file: Option<FileID> = None;

    for (index, span) in spans.iter().copied().enumerate() {
        if current_file != Some(span.file) {
            current_file = Some(span.file);
            stack.clear();
        }

        while let Some(&parent_index) = stack.last() {
            if span_encloses(spans[parent_index], span) {
                break;
            }
            stack.pop();
        }

        parents[index] = stack.last().copied();
        stack.push(index);
    }

    parents
}

fn span_encloses(parent: Span, child: Span) -> bool {
    parent.file == child.file
        && compare_positions(parent.start, child.start) != Ordering::Greater
        && compare_positions(parent.end, child.end) != Ordering::Less
}

fn is_std_package_root(package_root: &Path, std_path: Option<PathBuf>) -> Result<bool, String> {
    if let Ok(std_root) = resolve_std_path(std_path)
        && package_root == std_root
    {
        return Ok(true);
    }

    let manifest = Manifest::parse(package_root.join(MANIFEST_FILE))?;
    let package_name = normalize_module_path(&manifest.package.name)?;
    Ok(package_name == STD_PACKAGE_PATH)
}

fn struct_literal_field_name(field: &ExpressionField) -> Option<crate::span::Symbol> {
    if let Some(label) = &field.label {
        return Some(label.identifier.symbol);
    }

    match &field.expression.kind {
        ExpressionKind::Path(ResolvedPath::Resolved(path)) => path
            .segments
            .last()
            .map(|segment| segment.identifier.symbol),
        _ => None,
    }
}

fn struct_literal_field_navigation_span(field: &ExpressionField) -> Span {
    if let Some(label) = &field.label {
        return label.span;
    }

    match &field.expression.kind {
        ExpressionKind::Path(ResolvedPath::Resolved(path)) => path
            .segments
            .last()
            .map(|segment| segment.span)
            .unwrap_or(field.expression.span),
        _ => field.expression.span,
    }
}

fn build_module_target_map(
    module: &Module,
    file_paths: &FxHashMap<FileID, PathBuf>,
) -> FxHashMap<DefinitionID, Span> {
    let mut targets = FxHashMap::default();
    populate_module_targets(module, file_paths, &mut targets);
    targets
}

fn populate_module_targets(
    module: &Module,
    file_paths: &FxHashMap<FileID, PathBuf>,
    targets: &mut FxHashMap<DefinitionID, Span>,
) {
    if let Some(file_id) = module
        .files
        .iter()
        .copied()
        .min_by(|lhs, rhs| file_paths.get(lhs).cmp(&file_paths.get(rhs)))
    {
        let target = module
            .declarations
            .iter()
            .filter(|declaration| declaration.span.file == file_id)
            .map(|declaration| declaration.span)
            .min_by(|lhs, rhs| compare_navigation_spans(*lhs, *rhs))
            .unwrap_or_else(|| Span::empty(file_id));
        targets.insert(module.id, target);
    }

    for submodule in &module.submodules {
        populate_module_targets(submodule, file_paths, targets);
    }
}

fn compile_std_for_ide<'a>(
    ctx: &'a CompilerContext<'a>,
    std_path: Option<PathBuf>,
) -> Result<(), String> {
    let src = resolve_std_path(std_path)?;
    let attached = attached_std_paths(ctx)?;

    let index = PackageIndex::new(0);
    let config = ctx.store.arenas.configs.alloc(Config {
        index,
        name: "std".into(),
        identifier: STD_PREFIX.into(),
        src,
        dependencies: Default::default(),
        kind: PackageKind::Library,
        executable_out: None,
        no_std_prelude: true,
        is_script: false,
        profile: BuildProfile::Release,
        codegen: Default::default(),
        overflow_checks: false,
        debug: DebugOptions {
            dump_mir: false,
            dump_llvm: false,
            timings: false,
            debug_info: Default::default(),
        },
        harness_mode: Default::default(),
        std_mode: StdMode::BootstrapStd,
        is_std_provider: true,
    });

    let compiler = Compiler::new(ctx, config);

    let object_path = attached
        .object
        .exists()
        .then_some(attached.object.as_path());

    match metadata::try_load_package_metadata_from_paths(
        compiler.context,
        ReuseMode::SemanticDependency,
        &attached.metadata,
        object_path,
    ) {
        MetadataLoadStatus::Hit(hit) => {
            metadata::hydrate_loaded_metadata(
                compiler.context,
                &hit,
                ReuseMode::SemanticDependency,
            )
            .map_err(|e| {
                format!(
                    "failed to hydrate std metadata: {}\nRun `taro check --build-std` to rebuild.",
                    e
                )
            })?;
            Ok(())
        }
        MetadataLoadStatus::Miss(reason) => Err(format!(
            "attached std metadata unavailable: {}\nExpected: {}\nRun `taro check --build-std` to rebuild.",
            reason,
            attached.metadata.display()
        )),
    }
}

fn resolve_std_path(std_path: Option<PathBuf>) -> Result<PathBuf, String> {
    if let Some(path) = std_path {
        return path
            .canonicalize()
            .map_err(|e| format!("std path '{}' is invalid: {}", path.display(), e));
    }

    let home = crate::package::utils::language_home()?;
    let std_root = home.join(STD_PREFIX);
    std_root
        .canonicalize()
        .map_err(|e| format!("{} is invalid: {}", std_root.display(), e))
}

struct AttachedStdPaths {
    metadata: PathBuf,
    object: PathBuf,
}

fn attached_std_paths(ctx: &CompilerContext<'_>) -> Result<AttachedStdPaths, String> {
    let home = crate::package::utils::language_home()?;
    let target = ctx
        .store
        .target_layout
        .triple()
        .as_str()
        .to_string_lossy()
        .into_owned();
    let dir = home
        .join("lib")
        .join("taro")
        .join("std")
        .join(target.as_str());
    Ok(AttachedStdPaths {
        metadata: dir.join("std.taro_meta"),
        object: dir.join("std.o"),
    })
}

fn ide_target_dir(file_path: &Path) -> PathBuf {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    file_path.hash(&mut hasher);
    let hash = format!("{:x}", hasher.finish());

    std::env::temp_dir()
        .join("taro-ide")
        .join(hash)
        .join("debug")
}

#[cfg(test)]
mod tests {
    use super::{
        AnalysisSnapshot, NavigationData, build_module_target_map, collect_ide_artifacts,
        collect_navigation_data, compare_positions, is_std_package_root,
    };
    use crate::{
        PackageIndex,
        compile::{
            Compiler, IdeAnalysis, IdeAnalysisMode,
            config::{BuildProfile, Config, DebugOptions, PackageKind, StdMode},
            context::{CompilerArenas, CompilerContext, CompilerStore, Gcx},
        },
        constants::{STD_PACKAGE_PATH, STD_PREFIX},
        diagnostics::DiagCtx,
        ide_completion::COMPLETION_PROBE_IDENTIFIER,
        interner,
        span::Position,
    };
    use rustc_hash::FxHashMap;
    use std::cmp::Ordering;
    use std::fs::{create_dir_all, write};
    use std::path::{Path, PathBuf};
    use std::rc::Rc;
    use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};

    static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

    fn temp_dir(name: &str) -> PathBuf {
        let unique = TEMP_COUNTER.fetch_add(1, AtomicOrdering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "taro-ide-{name}-{}-{}-{}",
            std::process::id(),
            unique,
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

    fn write_manifest(path: &Path, name: &str, no_std_prelude: bool) {
        write_file(
            &path.join("package.toml"),
            &format!(
                "[package]\nname = \"{name}\"\nkind = \"library\"\nno_std_prelude = {no_std_prelude}\n"
            ),
        );
    }

    fn analyze_navigation_source(source: &str) -> NavigationData {
        interner::reset_session();

        let root = temp_dir("navigation");
        let output_root = root.join("target");
        create_dir_all(&output_root).expect("output root");

        let file = root.join("main.tr");
        write_file(&file, source);
        let file = file.canonicalize().expect("canonical file");

        let dcx = Rc::new(DiagCtx::new(PathBuf::from(".")));
        let arenas = CompilerArenas::new();
        let store = CompilerStore::new(&arenas, output_root, &dcx, None, BuildProfile::Debug)
            .unwrap_or_else(|_| panic!("store"));
        let icx = CompilerContext::new(dcx, store);
        let config = icx.store.arenas.configs.alloc(Config {
            name: "script".into(),
            identifier: "script-navigation".into(),
            src: file,
            dependencies: FxHashMap::default(),
            index: PackageIndex::new(1),
            kind: PackageKind::Executable,
            executable_out: None,
            no_std_prelude: true,
            is_script: true,
            profile: BuildProfile::Debug,
            codegen: Default::default(),
            overflow_checks: false,
            debug: DebugOptions {
                dump_mir: false,
                dump_llvm: false,
                timings: false,
                debug_info: Default::default(),
            },
            harness_mode: Default::default(),
            std_mode: StdMode::BootstrapStd,
            is_std_provider: false,
        });

        let gcx = Gcx::new(&icx, config);
        let mut compiler = Compiler::new(&icx, config);
        let (package, results) = compiler.analyze().unwrap_or_else(|_| panic!("analyze"));
        let file_paths = icx.dcx.all_file_mappings().into_iter().collect();
        let module_targets = build_module_target_map(&package.root, &file_paths);
        collect_navigation_data(gcx, &package, Some(&results), &module_targets)
    }

    fn analyze_signature_source(source: &str) -> (AnalysisSnapshot, String, crate::span::FileID) {
        interner::reset_session();

        let root = temp_dir("completion");
        let output_root = root.join("target");
        create_dir_all(&output_root).expect("output root");

        let file = root.join("main.tr");
        write_file(&file, source);

        let dcx = Rc::new(DiagCtx::new(PathBuf::from(".")));
        let arenas = CompilerArenas::new();
        let store = CompilerStore::new(&arenas, output_root, &dcx, None, BuildProfile::Debug)
            .unwrap_or_else(|_| panic!("store"));
        let icx = CompilerContext::new(dcx.clone(), store);
        let config = icx.store.arenas.configs.alloc(Config {
            name: "script".into(),
            identifier: "script-signature".into(),
            src: file.clone(),
            dependencies: FxHashMap::default(),
            index: PackageIndex::new(1),
            kind: PackageKind::Executable,
            executable_out: None,
            no_std_prelude: true,
            is_script: true,
            profile: BuildProfile::Debug,
            codegen: Default::default(),
            overflow_checks: false,
            debug: DebugOptions {
                dump_mir: false,
                dump_llvm: false,
                timings: false,
                debug_info: Default::default(),
            },
            harness_mode: Default::default(),
            std_mode: StdMode::BootstrapStd,
            is_std_provider: false,
        });

        let gcx = Gcx::new(&icx, config);
        let mut compiler = Compiler::new(&icx, config);
        let IdeAnalysis {
            package,
            results,
            status,
        } = compiler
            .analyze_for_ide(IdeAnalysisMode::OnType)
            .unwrap_or_else(|_| panic!("analyze"));
        let file_paths = icx.dcx.all_file_mappings().into_iter().collect();
        let module_targets = build_module_target_map(&package.root, &file_paths);
        let artifacts = collect_ide_artifacts(
            gcx,
            &package,
            results.as_ref(),
            &module_targets,
            super::analysis_status(status),
        );
        let file_mappings: Vec<_> = icx
            .dcx
            .all_file_mappings()
            .into_iter()
            .map(|(file, path)| super::FileMapping { file, path })
            .collect();
        let file_lookup = file_mappings
            .iter()
            .map(|mapping| (mapping.path.clone(), mapping.file))
            .collect();
        let file_id = file_mappings
            .iter()
            .find(|mapping| paths_equivalent(&mapping.path, &file))
            .map(|mapping| mapping.file)
            .expect("file id");

        (
            AnalysisSnapshot {
                diagnostics: Vec::new(),
                navigation: artifacts.navigation,
                references: artifacts.references,
                document_symbols: artifacts.document_symbols,
                semantic_tokens: artifacts.semantic_tokens,
                inlay_hints: artifacts.inlay_hints,
                signatures: artifacts.signatures,
                completions: artifacts.completions,
                status: artifacts.status,
                file_mappings,
                file_lookup,
            },
            source.to_string(),
            file_id,
        )
    }

    fn analyze_package_completion_with_status(
        package_name: &str,
        entry_relative: &str,
        files: &[(&str, &str)],
    ) -> (AnalysisSnapshot, String, crate::span::FileID, bool) {
        let root = temp_dir("package-completion");
        write_manifest(&root, package_name, true);
        for (path, contents) in files {
            write_file(&root.join(path), contents);
        }

        let output_root = root.join("target");
        create_dir_all(&output_root).expect("output root");
        let entry_path = root
            .join(entry_relative)
            .canonicalize()
            .expect("canonical entry");
        let entry_text = std::fs::read_to_string(&entry_path).expect("entry text");

        let dcx = Rc::new(DiagCtx::new(PathBuf::from(".")));
        let arenas = CompilerArenas::new();
        let store = CompilerStore::new(&arenas, output_root, &dcx, None, BuildProfile::Debug)
            .unwrap_or_else(|_| panic!("store"));
        let icx = CompilerContext::new(dcx.clone(), store);
        let display_name = package_name.rsplit('/').next().unwrap_or(package_name);
        let is_std_provider = package_name == STD_PACKAGE_PATH;
        let config = icx.store.arenas.configs.alloc(Config {
            name: display_name.into(),
            identifier: if is_std_provider {
                STD_PREFIX.into()
            } else {
                format!("{display_name}-test").into()
            },
            src: root.clone(),
            dependencies: FxHashMap::default(),
            index: PackageIndex::new(1),
            kind: PackageKind::Library,
            executable_out: None,
            no_std_prelude: true,
            is_script: false,
            profile: BuildProfile::Debug,
            codegen: Default::default(),
            overflow_checks: false,
            debug: DebugOptions {
                dump_mir: false,
                dump_llvm: false,
                timings: false,
                debug_info: Default::default(),
            },
            harness_mode: Default::default(),
            std_mode: if is_std_provider {
                StdMode::BootstrapStd
            } else {
                StdMode::FullStd
            },
            is_std_provider,
        });

        let gcx = Gcx::new(&icx, config);
        let mut compiler = Compiler::new(&icx, config);
        let IdeAnalysis {
            package,
            results,
            status,
        } = compiler
            .analyze_for_ide(IdeAnalysisMode::OnType)
            .unwrap_or_else(|_| panic!("package analyze"));
        let file_paths = icx.dcx.all_file_mappings().into_iter().collect();
        let module_targets = build_module_target_map(&package.root, &file_paths);
        let artifacts = collect_ide_artifacts(
            gcx,
            &package,
            results.as_ref(),
            &module_targets,
            super::analysis_status(status),
        );
        let file_mappings: Vec<_> = icx
            .dcx
            .all_file_mappings()
            .into_iter()
            .map(|(file, path)| super::FileMapping { file, path })
            .collect();
        let file_lookup = file_mappings
            .iter()
            .map(|mapping| (mapping.path.clone(), mapping.file))
            .collect();
        let snapshot = AnalysisSnapshot {
            diagnostics: Vec::new(),
            navigation: artifacts.navigation,
            references: artifacts.references,
            document_symbols: artifacts.document_symbols,
            semantic_tokens: artifacts.semantic_tokens,
            inlay_hints: artifacts.inlay_hints,
            signatures: artifacts.signatures,
            completions: artifacts.completions,
            status: artifacts.status,
            file_mappings,
            file_lookup,
        };
        let file_id = snapshot
            .file_mappings
            .iter()
            .find(|mapping| paths_equivalent(&mapping.path, &entry_path))
            .map(|mapping| mapping.file)
            .expect("entry file id");
        (snapshot, entry_text, file_id, results.is_some())
    }

    fn start_position(source: &str, needle: &str, occurrence: usize) -> Position {
        let byte_index = source
            .match_indices(needle)
            .nth(occurrence - 1)
            .map(|(index, _)| index)
            .expect("needle occurrence");
        let prefix = &source[..byte_index];
        let line = prefix.bytes().filter(|byte| *byte == b'\n').count();
        let line_start = prefix.rfind('\n').map(|index| index + 1).unwrap_or(0);
        let offset = source[line_start..byte_index].chars().count();
        Position { line, offset }
    }

    fn span_contains(span: crate::span::Span, position: Position) -> bool {
        compare_positions(span.start, position) != Ordering::Greater
            && compare_positions(span.end, position) != Ordering::Less
    }

    fn find_hover_at<'a>(
        navigation: &'a NavigationData,
        position: Position,
    ) -> Option<&'a super::HoverInfo> {
        let index = navigation.hovers.partition_point(|hover| {
            compare_positions(hover.span.start, position) != Ordering::Greater
        });
        if index == 0 {
            return None;
        }

        let mut current = index - 1;
        loop {
            let hover = &navigation.hovers[current];
            if span_contains(hover.span, position) {
                return Some(hover);
            }
            current = navigation.hover_parents[current]?;
        }
    }

    fn find_hover_in_file<'a>(
        navigation: &'a NavigationData,
        file_id: crate::span::FileID,
        position: Position,
    ) -> Option<&'a super::HoverInfo> {
        let index = navigation.hovers.partition_point(|hover| {
            hover.span.file < file_id
                || (hover.span.file == file_id
                    && compare_positions(hover.span.start, position) != Ordering::Greater)
        });
        if index == 0 {
            return None;
        }

        let mut current = index - 1;
        loop {
            let hover = &navigation.hovers[current];
            if hover.span.file == file_id && span_contains(hover.span, position) {
                return Some(hover);
            }
            current = navigation.hover_parents[current]?;
        }
    }

    fn find_definition_at<'a>(
        navigation: &'a NavigationData,
        position: Position,
    ) -> Option<&'a super::DefinitionInfo> {
        let index = navigation.definitions.partition_point(|definition| {
            compare_positions(definition.source.start, position) != Ordering::Greater
        });
        if index == 0 {
            return None;
        }

        let mut current = index - 1;
        loop {
            let definition = &navigation.definitions[current];
            if span_contains(definition.source, position) {
                return Some(definition);
            }
            current = navigation.definition_parents[current]?;
        }
    }

    fn find_definition_in_file<'a>(
        navigation: &'a NavigationData,
        file_id: crate::span::FileID,
        position: Position,
    ) -> Option<&'a super::DefinitionInfo> {
        let index = navigation.definitions.partition_point(|definition| {
            definition.source.file < file_id
                || (definition.source.file == file_id
                    && compare_positions(definition.source.start, position) != Ordering::Greater)
        });
        if index == 0 {
            return None;
        }

        let mut current = index - 1;
        loop {
            let definition = &navigation.definitions[current];
            if definition.source.file == file_id && span_contains(definition.source, position) {
                return Some(definition);
            }
            current = navigation.definition_parents[current]?;
        }
    }

    fn end_position(source: &str, needle: &str, occurrence: usize) -> Position {
        let byte_index = source
            .match_indices(needle)
            .nth(occurrence - 1)
            .map(|(index, _)| index + needle.len())
            .expect("needle occurrence");
        let prefix = &source[..byte_index];
        let line = prefix.bytes().filter(|byte| *byte == b'\n').count();
        let line_start = prefix.rfind('\n').map(|index| index + 1).unwrap_or(0);
        let offset = source[line_start..byte_index].chars().count();
        Position { line, offset }
    }

    fn signature_help_at_position(
        snapshot: &AnalysisSnapshot,
        source: &str,
        file_id: crate::span::FileID,
        position: Position,
    ) -> super::SignatureHelpResult {
        super::signature_help_at(snapshot, source, file_id, position).expect("signature help")
    }

    fn completion_labels_at_position(
        snapshot: &AnalysisSnapshot,
        source: &str,
        file_id: crate::span::FileID,
        position: Position,
    ) -> Vec<String> {
        super::completion_at(snapshot, source, file_id, position)
            .into_iter()
            .map(|item| item.label)
            .collect()
    }

    fn reference_spans_at_position(
        snapshot: &AnalysisSnapshot,
        file_id: crate::span::FileID,
        position: Position,
        include_declaration: bool,
    ) -> Vec<crate::span::Span> {
        super::references_at(snapshot, file_id, position, include_declaration)
            .into_iter()
            .map(|reference| reference.span)
            .collect()
    }

    fn text_for_span<'a>(source: &'a str, span: crate::span::Span) -> &'a str {
        assert_eq!(span.start.line, span.end.line);
        let line = source.lines().nth(span.start.line).expect("span line");
        let start = line
            .char_indices()
            .nth(span.start.offset)
            .map(|(index, _)| index)
            .unwrap_or(line.len());
        let end = line
            .char_indices()
            .nth(span.end.offset)
            .map(|(index, _)| index)
            .unwrap_or(line.len());
        &line[start..end]
    }

    fn paths_equivalent(lhs: &Path, rhs: &Path) -> bool {
        lhs == rhs
            || lhs.canonicalize().ok() == rhs.canonicalize().ok()
            || (lhs.file_name() == rhs.file_name() && lhs.parent() == rhs.parent())
    }

    #[test]
    fn document_highlights_reuse_same_file_reference_groups() {
        let source =
            "func main() {\n    let value = 1\n    let copy = value\n    let other = value\n}\n";
        let (snapshot, source, file_id) = analyze_signature_source(source);
        let highlights =
            super::document_highlights_at(&snapshot, file_id, start_position(&source, "value", 2));

        assert_eq!(highlights.len(), 3);
        assert!(highlights.iter().all(|item| item.span.file == file_id));
        assert_eq!(
            highlights
                .iter()
                .map(|item| text_for_span(&source, item.span))
                .collect::<Vec<_>>(),
            vec!["value", "value", "value"]
        );
    }

    #[test]
    fn document_symbols_preserve_declaration_hierarchy() {
        let source = "struct Point {\n    x: uint32\n}\n\nimpl Point {\n    func value(self) -> uint32 { self.x }\n}\n\nfunc main() {}\n";
        let (snapshot, _, file_id) = analyze_signature_source(source);
        let symbols = super::document_symbols_for_file(&snapshot, file_id);

        let point = symbols
            .iter()
            .find(|item| item.name == "Point")
            .expect("Point");
        assert_eq!(point.kind, super::DocumentSymbolKind::Struct);
        assert_eq!(point.children.len(), 1);
        assert_eq!(point.children[0].name, "x");
        let implementation = symbols
            .iter()
            .find(|item| item.name == "impl Point")
            .expect("impl Point");
        assert_eq!(implementation.children.len(), 1);
        assert_eq!(implementation.children[0].name, "value");
        assert_eq!(
            implementation.children[0].kind,
            super::DocumentSymbolKind::Method
        );
    }

    #[test]
    fn semantic_tokens_classify_declarations_and_uses() {
        let source = "struct Point {\n    x: uint32\n}\n\nfunc read(_ point: Point) -> uint32 { point.x }\nfunc main() {\n    let point = Point { x: 1 }\n    let value = read(point)\n}\n";
        let (snapshot, source, file_id) = analyze_signature_source(source);
        let tokens = super::semantic_tokens_for_file(&snapshot, file_id);

        assert!(tokens.iter().any(|item| {
            text_for_span(&source, item.span) == "Point"
                && item.kind == super::SemanticTokenKind::Struct
                && item.modifiers.declaration
        }));
        assert!(tokens.iter().any(|item| {
            text_for_span(&source, item.span) == "read"
                && item.kind == super::SemanticTokenKind::Function
                && !item.modifiers.declaration
        }));
        assert!(tokens.iter().any(|item| {
            text_for_span(&source, item.span) == "point"
                && item.kind == super::SemanticTokenKind::Parameter
                && item.modifiers.readonly
        }));
    }

    #[test]
    fn inlay_hints_cover_inferred_locals_and_unlabeled_arguments() {
        let source = "func consume(_ value: uint32) {}\nfunc main() {\n    let count = 1 as uint32\n    consume(count)\n    let explicit: uint32 = count\n}\n";
        let (snapshot, source, file_id) = analyze_signature_source(source);
        let hints = super::inlay_hints_in_range(
            &snapshot,
            file_id,
            Position { line: 0, offset: 0 },
            Position {
                line: source.lines().count(),
                offset: 0,
            },
        );

        assert!(hints.iter().any(|hint| hint.label == ": uint32"));
        assert!(hints.iter().any(|hint| hint.label == "value:"));
        assert!(!hints.iter().any(|hint| {
            hint.kind == super::InlayHintKind::Type
                && hint.position == end_position(&source, "explicit", 1)
        }));

        let call_line_hints = super::inlay_hints_in_range(
            &snapshot,
            file_id,
            Position { line: 3, offset: 0 },
            Position {
                line: 3,
                offset: usize::MAX,
            },
        );
        assert_eq!(
            call_line_hints
                .iter()
                .map(|hint| hint.label.as_str())
                .collect::<Vec<_>>(),
            vec!["value:"]
        );
    }

    #[test]
    fn std_package_identity_matches_manifest_name() {
        let root = temp_dir("std-manifest-identity");
        write_manifest(&root, "github.com/taro/std", true);
        write_file(
            &root.join("src").join("main.tr"),
            "enum Heading { case north }\n",
        );

        let mismatched_std_root = temp_dir("other-std-root");
        assert!(is_std_package_root(&root, Some(mismatched_std_root)).expect("std identity"));
    }

    #[test]
    fn non_std_package_is_not_misidentified() {
        let root = temp_dir("non-std-package");
        write_manifest(&root, "github.com/example/pkg", false);
        write_file(
            &root.join("src").join("main.tr"),
            "enum Heading { case north }\n",
        );

        let mismatched_std_root = temp_dir("other-std-root");
        assert!(!is_std_package_root(&root, Some(mismatched_std_root)).expect("non-std identity"));
    }

    #[test]
    fn type_annotation_identifier_gets_hover() {
        let source = "func main() {\n    let a = Heading.north\n    let b: Heading = Heading.south\n}\n\nenum Heading {\n    case north, south, east, west\n}\n";
        let navigation = analyze_navigation_source(source);

        let heading_annotation = start_position(source, "Heading", 2);
        let hover = find_hover_at(&navigation, heading_annotation).expect("hover");
        assert!(hover.contents.contains("Heading"), "{}", hover.contents);
    }

    #[test]
    fn heading_segment_in_member_access_goes_to_enum_definition() {
        let source = "func main() {\n    let a = Heading.north\n    let b: Heading = Heading.south\n}\n\nenum Heading {\n    case north, south, east, west\n}\n";
        let navigation = analyze_navigation_source(source);

        let heading_use = start_position(source, "Heading", 1);
        let heading_definition = start_position(source, "Heading", 4);
        let definition = find_definition_at(&navigation, heading_use).expect("definition");

        assert_eq!(definition.target.start.line, heading_definition.line);
        assert_eq!(definition.target.start.offset, heading_definition.offset);
    }

    #[test]
    fn variant_segment_in_member_access_goes_to_variant_definition() {
        let source = "func main() {\n    let a = Heading.north\n    let b: Heading = Heading.south\n}\n\nenum Heading {\n    case north, south, east, west\n}\n";
        let navigation = analyze_navigation_source(source);

        let north_use = start_position(source, "north", 1);
        let north_definition = start_position(source, "north", 2);
        let definition = find_definition_at(&navigation, north_use).expect("definition");

        assert_eq!(definition.target.start.line, north_definition.line);
        assert_eq!(definition.target.start.offset, north_definition.offset);
    }

    #[test]
    fn field_member_goes_to_field_definition() {
        let source = "struct Foo { bar: uint32 }\n\nfunc main() {\n    let foo = Foo { bar: 10 }\n    let value = foo.bar\n}\n";
        let navigation = analyze_navigation_source(source);

        let field_use = start_position(source, "bar", 2);
        let field_definition = start_position(source, "bar", 1);
        let definition = find_definition_at(&navigation, field_use).expect("definition");

        assert_eq!(definition.target.start.line, field_definition.line);
        assert_eq!(definition.target.start.offset, field_definition.offset);
    }

    #[test]
    fn struct_literal_field_goes_to_field_definition() {
        let source =
            "struct Foo { bar: uint32 }\n\nfunc main() {\n    let foo = Foo { bar: 10 }\n}\n";
        let navigation = analyze_navigation_source(source);

        let field_use = start_position(source, "bar", 2);
        let field_definition = start_position(source, "bar", 1);
        let definition = find_definition_at(&navigation, field_use).expect("definition");

        assert_eq!(definition.target.start.line, field_definition.line);
        assert_eq!(definition.target.start.offset, field_definition.offset);
    }

    #[test]
    fn references_include_local_declaration_and_uses_without_shadow_leaks() {
        let source = "func main() {\n    let value = 1\n    let first = value\n    if true {\n        let value = 2\n        let second = value\n    }\n    let third = value\n}\n";
        let (snapshot, source_text, file_id) = analyze_signature_source(source);

        let outer_definition = start_position(&source_text, "value", 1);
        let outer_first_use = start_position(&source_text, "value", 2);
        let inner_definition = start_position(&source_text, "value", 3);
        let inner_use = start_position(&source_text, "value", 4);
        let outer_second_use = start_position(&source_text, "value", 5);
        let references = reference_spans_at_position(&snapshot, file_id, outer_definition, true);

        assert_eq!(references.len(), 3, "{references:?}");
        assert!(
            references
                .iter()
                .any(|span| span_contains(*span, outer_definition))
        );
        assert!(
            references
                .iter()
                .any(|span| span_contains(*span, outer_first_use))
        );
        assert!(
            references
                .iter()
                .any(|span| span_contains(*span, outer_second_use))
        );
        assert!(
            !references
                .iter()
                .any(|span| span_contains(*span, inner_definition))
        );
        assert!(
            !references
                .iter()
                .any(|span| span_contains(*span, inner_use))
        );
    }

    #[test]
    fn references_include_fields_and_struct_literal_labels() {
        let source = "struct Foo { bar: uint32 }\n\nfunc main() {\n    let foo = Foo { bar: 1 }\n    let value = foo.bar\n}\n";
        let (snapshot, source_text, file_id) = analyze_signature_source(source);

        let field_definition = start_position(&source_text, "bar", 1);
        let literal_label = start_position(&source_text, "bar", 2);
        let member_use = start_position(&source_text, "bar", 3);
        let references = reference_spans_at_position(&snapshot, file_id, field_definition, true);

        assert_eq!(references.len(), 3, "{references:?}");
        assert!(
            references
                .iter()
                .any(|span| span_contains(*span, field_definition))
        );
        assert!(
            references
                .iter()
                .any(|span| span_contains(*span, literal_label))
        );
        assert!(
            references
                .iter()
                .any(|span| span_contains(*span, member_use))
        );
    }

    #[test]
    fn references_include_enum_variant_declaration_and_uses() {
        let source =
            "enum Heading { case north, south }\n\nfunc main() {\n    let dir = Heading.north\n}\n";
        let (snapshot, source_text, file_id) = analyze_signature_source(source);

        let variant_definition = start_position(&source_text, "north", 1);
        let variant_use = start_position(&source_text, "north", 2);
        let references = reference_spans_at_position(&snapshot, file_id, variant_definition, true);

        assert_eq!(references.len(), 2, "{references:?}");
        assert!(
            references
                .iter()
                .any(|span| span_contains(*span, variant_definition))
        );
        assert!(
            references
                .iter()
                .any(|span| span_contains(*span, variant_use))
        );
    }

    #[test]
    fn references_include_function_parameter_declaration_and_uses() {
        let source = "func identity(value: uint32) -> uint32 {\n    return value\n}\n";
        let (snapshot, source_text, file_id) = analyze_signature_source(source);

        let parameter_definition = start_position(&source_text, "value", 1);
        let parameter_use = start_position(&source_text, "value", 2);
        let references =
            reference_spans_at_position(&snapshot, file_id, parameter_definition, true);

        assert_eq!(references.len(), 2, "{references:?}");
        assert!(
            references
                .iter()
                .any(|span| span_contains(*span, parameter_definition))
        );
        assert!(
            references
                .iter()
                .any(|span| span_contains(*span, parameter_use))
        );
    }

    #[test]
    fn navigation_falls_back_when_typecheck_results_drop() {
        let source = "enum Heading {\n    case north\n}\n\nfunc main() {\n    let dir = Heading.north\n}\n\nfunc broken() {\n    let value: uint32 = \"no\"\n}\n";
        let (snapshot, source_text, file_id, has_results) = analyze_package_completion_with_status(
            "github.com/example/fallback",
            "src/main.tr",
            &[("src/main.tr", source)],
        );

        assert!(
            !has_results,
            "expected typecheck failure to drop IDE results"
        );
        assert!(
            snapshot
                .file_mappings
                .iter()
                .any(|mapping| mapping.file == file_id)
        );

        let heading_use = start_position(&source_text, "Heading", 2);
        let hover = find_hover_at(&snapshot.navigation, heading_use).expect("fallback hover");
        let definition =
            find_definition_at(&snapshot.navigation, heading_use).expect("fallback definition");

        assert!(hover.contents.contains("Heading"), "{}", hover.contents);
        assert_eq!(
            definition.target.start,
            start_position(&source_text, "Heading", 1)
        );
    }

    #[test]
    fn signature_help_tracks_active_argument() {
        let source =
            "func helper(alpha: uint32, beta: uint32) {}\n\nfunc main() {\n    helper(1, 2)\n}\n";
        let (snapshot, source_text, file_id) = analyze_signature_source(source);
        let help = signature_help_at_position(
            &snapshot,
            &source_text,
            file_id,
            end_position(source, "1, ", 1),
        );

        assert_eq!(help.active_parameter, 1);
        assert_eq!(help.signatures.len(), 1);
        assert!(help.signatures[0].label.contains("uint32"));
        assert_eq!(help.signatures[0].parameters.len(), 2);
    }

    #[test]
    fn lexical_completion_includes_locals_declarations_and_builtin_types() {
        let source = "struct Foo { bar: uint32 }\n\nfunc helper() {}\n\nfunc main() {\n    let local = Foo { bar: 1 }\n    local\n}\n";
        let (snapshot, source_text, file_id) = analyze_signature_source(source);
        let labels = completion_labels_at_position(
            &snapshot,
            &source_text,
            file_id,
            start_position(source, "local", 2),
        );

        assert!(labels.contains(&"local".to_string()), "{labels:?}");
        assert!(labels.contains(&"helper".to_string()), "{labels:?}");
        assert!(labels.contains(&"Foo".to_string()), "{labels:?}");
        assert!(labels.contains(&"uint32".to_string()), "{labels:?}");
    }

    #[test]
    fn member_completion_includes_struct_fields() {
        let source = "struct Foo { bar: uint32 }\n\nfunc main() {\n    let foo = Foo { bar: 1 }\n    let value = foo.bar\n}\n";
        let (snapshot, source_text, file_id) = analyze_signature_source(source);
        let labels = completion_labels_at_position(
            &snapshot,
            &source_text,
            file_id,
            start_position(source, "bar", 3),
        );

        assert!(labels.contains(&"bar".to_string()), "{labels:?}");
    }

    #[test]
    fn static_member_completion_includes_enum_variants() {
        let source =
            "enum Heading { case north, south }\n\nfunc main() {\n    let dir = Heading.north\n}\n";
        let (snapshot, source_text, file_id) = analyze_signature_source(source);
        let labels = completion_labels_at_position(
            &snapshot,
            &source_text,
            file_id,
            start_position(source, "north", 2),
        );

        assert!(labels.contains(&"north".to_string()), "{labels:?}");
        assert!(labels.contains(&"south".to_string()), "{labels:?}");
    }

    #[test]
    fn probe_member_completion_includes_struct_fields() {
        let source = "struct Foo { bar: uint32 }\n\nfunc main() {\n    let foo = Foo { bar: 1 }\n    let value = foo.__taro_completion_probe\n}\n";
        let (snapshot, source_text, file_id) = analyze_signature_source(source);
        assert!(snapshot.status.typed_available, "{:?}", snapshot.status);

        let labels = completion_labels_at_position(
            &snapshot,
            &source_text,
            file_id,
            end_position(source, COMPLETION_PROBE_IDENTIFIER, 1),
        );

        assert!(labels.contains(&"bar".to_string()), "{labels:?}");
    }

    #[test]
    fn probe_member_completion_includes_fields_after_call_receiver() {
        let source = "struct Foo { bar: uint32 }\n\nfunc makeFoo() -> Foo {\n    return Foo { bar: 1 }\n}\n\nfunc main() {\n    let value = makeFoo().__taro_completion_probe\n}\n";
        let (snapshot, source_text, file_id) = analyze_signature_source(source);
        assert!(snapshot.status.typed_available, "{:?}", snapshot.status);

        let labels = completion_labels_at_position(
            &snapshot,
            &source_text,
            file_id,
            end_position(source, COMPLETION_PROBE_IDENTIFIER, 1),
        );

        assert!(labels.contains(&"bar".to_string()), "{labels:?}");
    }

    #[test]
    fn probe_static_completion_includes_enum_variants() {
        let source = "enum Heading { case north, south }\n\nfunc main() {\n    let dir = Heading.__taro_completion_probe\n}\n";
        let (snapshot, source_text, file_id) = analyze_signature_source(source);
        assert!(snapshot.status.typed_available, "{:?}", snapshot.status);

        let labels = completion_labels_at_position(
            &snapshot,
            &source_text,
            file_id,
            end_position(source, COMPLETION_PROBE_IDENTIFIER, 1),
        );

        assert!(labels.contains(&"north".to_string()), "{labels:?}");
        assert!(labels.contains(&"south".to_string()), "{labels:?}");
    }

    #[test]
    fn completion_falls_back_when_typecheck_results_drop() {
        let source = "enum Heading {\n    case north\n}\n\nfunc main() {\n    let dir = Heading.north\n}\n\nfunc broken() {\n    let value: uint32 = \"no\"\n}\n";
        let (snapshot, source_text, file_id, has_results) = analyze_package_completion_with_status(
            "github.com/example/completion-fallback",
            "src/main.tr",
            &[("src/main.tr", source)],
        );

        assert!(
            !has_results,
            "expected typecheck failure to drop IDE results"
        );
        let labels = completion_labels_at_position(
            &snapshot,
            &source_text,
            file_id,
            start_position(&source_text, "Heading", 2),
        );

        assert!(labels.contains(&"Heading".to_string()), "{labels:?}");
    }

    #[test]
    // This deliberately analyzes the real standard library, so its cost grows
    // with std and belongs in an explicit integration run rather than every
    // compiler unit-test invocation.
    #[ignore = "slow real-std integration coverage; run explicitly when changing IDE package analysis"]
    fn real_std_package_navigation_is_available() {
        let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("workspace root")
            .to_path_buf();
        let root = repo_root.join("std");
        let entry_path = root.join("src/lib.tr").canonicalize().expect("entry path");
        let source = std::fs::read_to_string(&entry_path).expect("entry text");

        let snapshot = super::analyze_owner_for_ide(
            super::AnalysisOwner::Package(root),
            super::AnalysisRequest {
                mode: super::AnalysisMode::OnSave,
                overlays: Vec::new(),
            },
            None,
        )
        .expect("snapshot");

        assert!(
            snapshot.status.hir_available,
            "diagnostics: {:?}",
            snapshot
                .diagnostics
                .iter()
                .map(|diagnostic| diagnostic.message.clone())
                .collect::<Vec<_>>()
        );

        let file_id = snapshot
            .file_mappings
            .iter()
            .find(|mapping| paths_equivalent(&mapping.path, &entry_path))
            .map(|mapping| mapping.file)
            .expect("entry file id");
        let format_printf_use = start_position(&source, "formatPrintf", 1);
        let hover =
            find_hover_in_file(&snapshot.navigation, file_id, format_printf_use).expect("hover");
        let definition = find_definition_in_file(&snapshot.navigation, file_id, format_printf_use)
            .expect("definition");

        assert!(hover.contents.contains("Display"), "{}", hover.contents);
        assert_ne!(definition.target.file, file_id);
    }
}
