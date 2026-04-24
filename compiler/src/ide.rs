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
        DefinitionID, Expression, ExpressionField, ExpressionKind, HirVisitor, Module, PathSegment,
        Pattern, PatternKind, PatternPath, Resolution, ResolvedPath, StructLiteral, Type, UseTree,
        UseTreeAlias, UseTreeKind, walk_assoc_declaration, walk_declaration, walk_expression,
        walk_path_segment, walk_pattern, walk_type, walk_use_tree,
    },
    interner,
    metadata::{self, MetadataLoadStatus, ReuseMode},
    package::{discover, manifest::Manifest, readonly, utils::normalize_module_path},
    sema::{
        models::{AdtKind, StructField, Ty, TyKind},
        resolve::models::DefinitionKind,
        tycheck::results::TypeCheckResults,
    },
    span::{FileID, Position, Span},
};
use rustc_hash::FxHashMap;
use std::cmp::Ordering;
use std::path::{Path, PathBuf};
use std::rc::Rc;

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

#[derive(Debug, Clone, Default)]
pub struct AnalysisSnapshot {
    pub diagnostics: Vec<DiagnosticRecord>,
    pub navigation: NavigationData,
    pub signatures: SignatureHelpData,
    pub status: AnalysisStatus,
    pub file_mappings: Vec<FileMapping>,
    pub file_lookup: FxHashMap<PathBuf, FileID>,
}

#[derive(Debug, Clone, Default)]
struct IdeArtifacts {
    navigation: NavigationData,
    signatures: SignatureHelpData,
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
            signatures: artifacts.signatures,
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
                signatures: SignatureHelpData::default(),
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
        overflow_checks: false,
        debug: DebugOptions {
            dump_mir: false,
            dump_llvm: false,
            timings: false,
        },
        test_mode: false,
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
        if !is_root && package.kind != PackageKind::Library {
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
            overflow_checks: false,
            debug: DebugOptions {
                dump_mir: false,
                dump_llvm: false,
                timings: false,
            },
            test_mode: false,
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
            let Some(index) = results.field_index(field.expression.id) else {
                continue;
            };
            let Some(field_def) = self.struct_field_for_ty(struct_ty, index) else {
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
            let Some(index) = results.field_index(field.expression.id) else {
                continue;
            };
            let Some(field_def) = self.struct_field_for_ty(struct_ty, index) else {
                continue;
            };
            self.nav_data.definitions.push(DefinitionInfo {
                source: struct_literal_field_navigation_span(field),
                target: self.gcx.definition_ident(field_def.def_id).span,
            });
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

fn collect_ide_artifacts<'ctx>(
    gcx: Gcx<'ctx>,
    package: &hir::Package,
    results: Option<&TypeCheckResults<'ctx>>,
    module_targets: &FxHashMap<DefinitionID, Span>,
    status: AnalysisStatus,
) -> IdeArtifacts {
    IdeArtifacts {
        navigation: collect_navigation_data(gcx, package, results, module_targets),
        signatures: collect_signature_help_data(gcx, package, results),
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
        overflow_checks: false,
        debug: DebugOptions {
            dump_mir: false,
            dump_llvm: false,
            timings: false,
        },
        test_mode: false,
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
            overflow_checks: false,
            debug: DebugOptions {
                dump_mir: false,
                dump_llvm: false,
                timings: false,
            },
            test_mode: false,
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
            overflow_checks: false,
            debug: DebugOptions {
                dump_mir: false,
                dump_llvm: false,
                timings: false,
            },
            test_mode: false,
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
                signatures: artifacts.signatures,
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
            overflow_checks: false,
            debug: DebugOptions {
                dump_mir: false,
                dump_llvm: false,
                timings: false,
            },
            test_mode: false,
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
            signatures: artifacts.signatures,
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

    fn paths_equivalent(lhs: &Path, rhs: &Path) -> bool {
        lhs == rhs
            || lhs.canonicalize().ok() == rhs.canonicalize().ok()
            || (lhs.file_name() == rhs.file_name() && lhs.parent() == rhs.parent())
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
