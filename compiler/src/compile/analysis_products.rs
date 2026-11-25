//! Semantic values that can leave the compiler session.

use std::{collections::BTreeSet, path::PathBuf, sync::Arc};

use rustc_hash::FxHashMap;

use crate::{
    diagnostics::{Applicability, Diagnostic, DiagnosticLevel},
    hir::{self, DefinitionID, ExpressionKind, HirVisitor, Mutability},
    sema::{
        models::{
            AdtKind, AliasKind, ClosureKind, Const, ConstKind, ConstValue, FloatTy,
            FunctionPointerEffects, GenericArgument, GenericArguments, IntTy, Ty, TyKind, UIntTy,
        },
        resolve::models::DefinitionKind,
        tycheck::results::TypeCheckResults,
    },
    span::{Position, Span},
};

use super::{
    Compiler,
    context::Gcx,
    declarations::{
        self, BodyIdentity, BodyLocalAnchor, BodyRecord, BodyRelativeRange, DeclarationRecord,
    },
};

/// A source range in the package revision from which it was captured.
/// Columns count Unicode scalar values, as they do in the lexer.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct SourceRange {
    pub path: PathBuf,
    pub start: Position,
    pub end: Position,
}

impl SourceRange {
    pub(crate) fn capture(gcx: Gcx<'_>, span: Span) -> Option<Self> {
        Some(Self {
            path: gcx.dcx().file_path(span.file)?,
            start: span.start,
            end: span.end,
        })
    }
}

/// A declaration address within one revision. The package identifier and
/// exact source range disambiguate overloads without retaining compiler IDs.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct DeclarationKey {
    pub package: String,
    pub name: String,
    pub kind: DefinitionKind,
    pub source: SourceRange,
}

impl DeclarationKey {
    pub(crate) fn capture(gcx: Gcx<'_>, id: DefinitionID) -> Option<Self> {
        let ident = gcx.try_definition_ident(id)?;
        Some(Self {
            package: gcx.package_ident(id.package())?.into(),
            name: gcx.symbol_text(ident.symbol).into(),
            kind: gcx.try_definition_kind(id)?,
            source: SourceRange::capture(gcx, ident.span)?,
        })
    }

    fn navigation_target(gcx: Gcx<'_>, id: DefinitionID) -> Option<Self> {
        let target = Self::capture(gcx, id)?;
        // Implicit directory modules have no source identifier.
        (target.source.start < target.source.end).then_some(target)
    }
}

/// Literal contents and resolvable declarations in place of interner slots.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum OwnedConstant {
    Bytes(Box<[u8]>),
    Integer(i128),
    Bool(bool),
    Rune(char),
    String(String),
    FloatBits(u64),
    Unit,
    EnumUnitVariant(DeclarationKey),
    Array(Box<[OwnedConstant]>),
}

impl OwnedConstant {
    pub(crate) fn capture(gcx: Gcx<'_>, value: ConstValue) -> Option<Self> {
        let interner = gcx.interner();
        Some(match value {
            ConstValue::Bytes(bytes) => Self::Bytes(Box::from(&*interner.bytes(bytes))),
            ConstValue::Integer(value) => Self::Integer(value),
            ConstValue::Bool(value) => Self::Bool(value),
            ConstValue::Rune(value) => Self::Rune(value),
            ConstValue::String(name) => Self::String(gcx.symbol_text(name).into()),
            ConstValue::Float(value) => Self::FloatBits(value.to_bits()),
            ConstValue::Unit => Self::Unit,
            ConstValue::EnumUnitVariant(id) => {
                Self::EnumUnitVariant(DeclarationKey::capture(gcx, id)?)
            }
            ConstValue::Array(array) => Self::Array(
                interner
                    .const_elements(array)
                    .iter()
                    .map(|&value| Self::capture(gcx, value))
                    .collect::<Option<_>>()?,
            ),
        })
    }
}

/// The compiler's type shape with owner-local definitions copied to source
/// addresses. A synthetic declaration may have no source address.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum TypeShape {
    Bool,
    Rune,
    String,
    Int(IntTy),
    UInt(UIntTy),
    Float(FloatTy),
    Array {
        element: Box<TypeShape>,
        len: Box<ConstantArgument>,
    },
    Nominal {
        kind: AdtKind,
        declaration: Option<DeclarationKey>,
        arguments: Box<[Argument]>,
    },
    Pointer(Box<TypeShape>, Mutability),
    Reference(Box<TypeShape>),
    Tuple(Box<[TupleElement]>),
    Function {
        inputs: Box<[TypeShape]>,
        output: Box<TypeShape>,
        effects: FunctionPointerEffects,
    },
    Interfaces(Box<[InterfaceShape]>),
    Alias {
        kind: AliasKind,
        declaration: Option<DeclarationKey>,
        arguments: Box<[Argument]>,
    },
    Parameter {
        index: usize,
        name: String,
    },
    ExistentialSelf(u32),
    Closure {
        declaration: Option<DeclarationKey>,
        kind: ClosureKind,
        arguments: Box<[Argument]>,
        inputs: Box<[TypeShape]>,
        output: Box<TypeShape>,
    },
    Opaque(Option<DeclarationKey>),
    Unresolved,
    Error,
    Never,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct TupleElement {
    pub label: Option<String>,
    pub ty: TypeShape,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct InterfaceShape {
    pub declaration: Option<DeclarationKey>,
    pub arguments: Box<[Argument]>,
    pub bindings: Box<[(String, TypeShape)]>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Argument {
    Type(TypeShape),
    Constant(ConstantArgument),
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ConstantArgument {
    pub ty: TypeShape,
    pub value: ConstantArgumentValue,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ConstantArgumentValue {
    Literal(OwnedConstant),
    Parameter { index: usize, name: String },
    Unresolved,
}

impl TypeShape {
    pub(crate) fn capture<'ctx>(gcx: Gcx<'ctx>, ty: Ty<'ctx>) -> Self {
        let declaration = |def| DeclarationKey::capture(gcx, def);
        let owned = |ty| Self::capture(gcx, ty);
        let boxed = |ty| Box::new(owned(ty));
        let arguments = |arguments: GenericArguments<'ctx>| {
            arguments
                .iter()
                .map(|argument| match *argument {
                    GenericArgument::Type(ty) => Argument::Type(owned(ty)),
                    GenericArgument::Const(value) => {
                        Argument::Constant(ConstantArgument::capture(gcx, value))
                    }
                })
                .collect()
        };
        match ty.kind() {
            TyKind::Bool => Self::Bool,
            TyKind::Rune => Self::Rune,
            TyKind::String => Self::String,
            TyKind::Int(kind) => Self::Int(kind),
            TyKind::UInt(kind) => Self::UInt(kind),
            TyKind::Float(kind) => Self::Float(kind),
            TyKind::Array { element, len } => Self::Array {
                element: boxed(element),
                len: Box::new(ConstantArgument::capture(gcx, len)),
            },
            TyKind::Adt(adt, args) => Self::Nominal {
                kind: adt.kind,
                declaration: declaration(adt.id),
                arguments: arguments(args),
            },
            TyKind::Pointer(ty, mutability) => Self::Pointer(boxed(ty), mutability),
            TyKind::Reference(ty) => Self::Reference(boxed(ty)),
            TyKind::Tuple(elements) => {
                let labels = ty.tuple_labels();
                Self::Tuple(
                    elements
                        .iter()
                        .enumerate()
                        .map(|(index, &element)| TupleElement {
                            label: labels
                                .iter()
                                .find(|(position, _)| *position == index)
                                .map(|(_, label)| gcx.symbol_text(label).into()),
                            ty: owned(element),
                        })
                        .collect(),
                )
            }
            TyKind::FnPointer {
                inputs,
                output,
                effects,
            } => Self::Function {
                inputs: inputs.iter().copied().map(owned).collect(),
                output: boxed(output),
                effects,
            },
            TyKind::BoxedExistential { interfaces } => Self::Interfaces(
                interfaces
                    .iter()
                    .map(|interface| InterfaceShape {
                        declaration: declaration(interface.id),
                        arguments: arguments(interface.arguments),
                        bindings: interface
                            .bindings
                            .iter()
                            .map(|binding| {
                                (gcx.symbol_text(binding.name).into(), owned(binding.ty))
                            })
                            .collect(),
                    })
                    .collect(),
            ),
            TyKind::Alias { kind, def_id, args } => Self::Alias {
                kind,
                declaration: declaration(def_id),
                arguments: arguments(args),
            },
            TyKind::Parameter(parameter) => Self::Parameter {
                index: parameter.index,
                name: gcx.symbol_text(parameter.name).into(),
            },
            TyKind::ExistentialSelf(index) => Self::ExistentialSelf(index),
            TyKind::Closure {
                closure_def_id,
                kind,
                captured_generics,
                inputs,
                output,
            } => Self::Closure {
                declaration: declaration(closure_def_id),
                kind,
                arguments: arguments(captured_generics),
                inputs: inputs.iter().copied().map(owned).collect(),
                output: boxed(output),
            },
            TyKind::Opaque(definition) => Self::Opaque(declaration(definition)),
            TyKind::Infer(_) => Self::Unresolved,
            TyKind::Error => Self::Error,
            TyKind::Never => Self::Never,
        }
    }
}

impl ConstantArgument {
    fn capture<'ctx>(gcx: Gcx<'ctx>, argument: Const<'ctx>) -> Self {
        let value = match argument.kind {
            ConstKind::Value(value) => OwnedConstant::capture(gcx, value).map_or(
                ConstantArgumentValue::Unresolved,
                ConstantArgumentValue::Literal,
            ),
            ConstKind::Param(parameter) => ConstantArgumentValue::Parameter {
                index: parameter.index,
                name: gcx.symbol_text(parameter.name).into(),
            },
            ConstKind::Infer(_) => ConstantArgumentValue::Unresolved,
        };
        Self {
            ty: TypeShape::capture(gcx, argument.ty),
            value,
        }
    }
}

/// Successful semantic facts and diagnostics, tagged with the input revision.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct AnalysisProduct {
    pub revision: u64,
    pub complete: bool,
    pub syntax_uncertainty: SyntaxUncertainty,
    pub declarations: Vec<DeclarationRecord>,
    pub bodies: Vec<BodyRecord>,
    pub occurrences: Vec<TypedOccurrence>,
    pub missing_members: Vec<MissingMember>,
    pub diagnostics: Vec<AnalysisDiagnostic>,
}

/// Syntax damage that may conceal declaration boundaries.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SyntaxUncertainty {
    None,
    Files(Box<[PathBuf]>),
    Package,
}

impl SyntaxUncertainty {
    fn capture(gcx: Gcx<'_>, diagnostics: &[Diagnostic]) -> Self {
        let mut files = BTreeSet::new();
        for diagnostic in diagnostics {
            if diagnostic.level != DiagnosticLevel::Error
                || diagnostic.code == Some(crate::parse::MISSING_MEMBER_NAME_DIAGNOSTIC)
            {
                continue;
            }
            let Some(path) = diagnostic
                .span
                .and_then(|span| gcx.dcx().file_path(span.file))
            else {
                return Self::Package;
            };
            files.insert(path);
        }
        if files.is_empty() {
            Self::None
        } else {
            Self::Files(files.into_iter().collect())
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MissingMember {
    pub insertion: SourceRange,
    pub receiver: TypeShape,
    pub items: Vec<MemberCompletion>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MemberCompletion {
    pub name: String,
    pub is_method: bool,
    pub detail: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct TypedOccurrence {
    pub source: SourceRange,
    pub ty: TypeShape,
    pub declaration: Option<DeclarationKey>,
    pub anchor: Option<BodyLocalAnchor>,
    pub local_declaration: Option<LocalDeclaration>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct LocalDeclaration {
    pub source: SourceRange,
    pub anchor: BodyLocalAnchor,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct AnalysisDiagnostic {
    pub source: Option<SourceRange>,
    pub body_range: Option<BodyRelativeRange>,
    pub level: DiagnosticLevel,
    pub message: String,
    pub code: Option<usize>,
    pub notes: Vec<AnalysisDiagnostic>,
    pub suggestion: Option<AnalysisSuggestion>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct AnalysisSuggestion {
    pub source: SourceRange,
    pub body_range: Option<BodyRelativeRange>,
    pub message: String,
    pub replacement: String,
    pub applicability: Applicability,
}

impl AnalysisDiagnostic {
    pub(super) fn capture(gcx: Gcx<'_>, diagnostic: Diagnostic, bodies: &[BodyRecord]) -> Self {
        let relative = |range: &SourceRange| bodies.iter().find_map(|body| body.relative(range));
        let source = diagnostic
            .span
            .and_then(|span| SourceRange::capture(gcx, span));
        Self {
            body_range: source.as_ref().and_then(relative),
            source,
            level: diagnostic.level,
            message: diagnostic.message,
            code: diagnostic.code,
            notes: diagnostic
                .children
                .into_iter()
                .map(|note| Self::capture(gcx, note, bodies))
                .collect(),
            suggestion: diagnostic.suggestion.and_then(|suggestion| {
                let source = SourceRange::capture(gcx, suggestion.span)?;
                Some(AnalysisSuggestion {
                    body_range: relative(&source),
                    source,
                    message: suggestion.message,
                    replacement: suggestion.replacement,
                    applicability: suggestion.applicability,
                })
            }),
        }
    }
}

pub(super) fn capture_function<'ctx>(
    gcx: Gcx<'ctx>,
    declaration: &hir::Declaration,
    types: &TypeCheckResults<'ctx>,
) -> Option<(DeclarationRecord, BodyRecord, Vec<TypedOccurrence>)> {
    let hir::DeclarationKind::Function(function) = &declaration.kind else {
        return None;
    };
    let record = declarations::collect_function(gcx, declaration.id, function)?;
    let records = FxHashMap::from_iter([(declaration.id, record.clone())]);
    let mut occurrences = Vec::new();
    let mut bodies = Vec::new();
    let mut missing_members = Vec::new();
    hir::walk_declaration(
        &mut OccurrenceCollector {
            gcx,
            types,
            occurrences: &mut occurrences,
            missing_members: &mut missing_members,
            declarations: &records,
            bodies: &mut bodies,
            current_body: None,
            locals: FxHashMap::default(),
        },
        declaration,
    );
    let body = bodies.pop()?;
    Some((record, body, occurrences))
}

impl Compiler<'_> {
    /// Analyze one revision in a fresh scratch session and copy out its facts.
    /// The returned product can be delivered after the scratch session drops.
    pub fn analyze_owned(&mut self, revision: u64) -> AnalysisProduct {
        self.capture_analysis(revision, false, None)
    }

    /// Recover syntax for editor requests. Semantic answers carry the damage
    /// information needed to invalidate affected declarations conservatively.
    pub fn analyze_partial_owned(&mut self, revision: u64) -> AnalysisProduct {
        self.capture_analysis(revision, true, None)
    }

    /// Record the configured package inputs that a later selected-body check
    /// must reproduce before reusing facts from this check.
    pub fn analyze_partial_owned_with_fingerprint(
        &mut self,
        revision: u64,
    ) -> (AnalysisProduct, Option<blake3::Hash>) {
        let mut fingerprint = None;
        let product = self.capture_analysis(revision, true, Some(&mut fingerprint));
        let fingerprint = if product.complete { fingerprint } else { None };
        (product, fingerprint)
    }

    fn capture_analysis(
        &mut self,
        revision: u64,
        recover_syntax: bool,
        fingerprint: Option<&mut Option<blake3::Hash>>,
    ) -> AnalysisProduct {
        let gcx = self.context;
        let diagnostics = gcx.dcx();
        let revision = diagnostics
            .sources()
            .workspace_revision()
            .unwrap_or(revision);
        diagnostics.enable_recording();
        let (result, syntax_diagnostics) = if recover_syntax {
            self.analyze_recovering(fingerprint)
        } else {
            (self.analyze(), Vec::new())
        };
        let syntax_uncertainty = SyntaxUncertainty::capture(gcx, &syntax_diagnostics);
        for diagnostic in syntax_diagnostics {
            diagnostics.emit(diagnostic);
        }
        let mut occurrences = Vec::new();
        let mut missing_members = Vec::new();
        let mut declarations = Vec::new();
        let mut bodies = Vec::new();
        if let Ok((package, types)) = &result {
            let map = declarations::collect(gcx, package);
            hir::walk_package(
                &mut OccurrenceCollector {
                    gcx,
                    types,
                    occurrences: &mut occurrences,
                    missing_members: &mut missing_members,
                    declarations: &map,
                    bodies: &mut bodies,
                    current_body: None,
                    locals: FxHashMap::default(),
                },
                package,
            );
            declarations.extend(map.into_values());
        }
        let complete = result.is_ok() && !diagnostics.has_error();
        let diagnostics = diagnostics
            .take_recorded_diagnostics()
            .into_iter()
            .map(|diagnostic| AnalysisDiagnostic::capture(gcx, diagnostic, &bodies))
            .collect();
        AnalysisProduct {
            revision,
            complete,
            syntax_uncertainty,
            declarations,
            bodies,
            occurrences,
            missing_members,
            diagnostics,
        }
    }
}

struct OccurrenceCollector<'result, 'ctx> {
    gcx: Gcx<'ctx>,
    types: &'result TypeCheckResults<'ctx>,
    occurrences: &'result mut Vec<TypedOccurrence>,
    missing_members: &'result mut Vec<MissingMember>,
    declarations: &'result FxHashMap<DefinitionID, DeclarationRecord>,
    bodies: &'result mut Vec<BodyRecord>,
    current_body: Option<BodyTraversal>,
    locals: FxHashMap<hir::NodeID, LocalDeclaration>,
}

struct BodyTraversal {
    identity: Arc<BodyIdentity>,
    definition: DefinitionID,
    next_ordinal: u32,
}

impl<'ctx> OccurrenceCollector<'_, 'ctx> {
    fn next_anchor(&mut self) -> Option<BodyLocalAnchor> {
        let body = self.current_body.as_mut()?;
        let ordinal = body.next_ordinal;
        body.next_ordinal = ordinal.checked_add(1).expect("body traversal exhausted");
        Some(BodyLocalAnchor {
            body: Arc::clone(&body.identity),
            ordinal,
        })
    }

    fn record(
        &mut self,
        ty: Option<Ty<'ctx>>,
        span: Span,
        definition: Option<DefinitionID>,
        local_declaration: Option<LocalDeclaration>,
        anchor: Option<BodyLocalAnchor>,
    ) {
        let declaration = definition.and_then(|id| DeclarationKey::navigation_target(self.gcx, id));
        if (ty.is_some() || declaration.is_some() || local_declaration.is_some())
            && let Some(source) = SourceRange::capture(self.gcx, span)
        {
            #[cfg(test)]
            self.gcx
                .dcx()
                .analysis_work
                .copied_occurrences
                .update(|count| count + 1);
            self.occurrences.push(TypedOccurrence {
                source,
                ty: ty.map_or(TypeShape::Unresolved, |ty| TypeShape::capture(self.gcx, ty)),
                declaration,
                anchor,
                local_declaration,
            });
        }
    }

    fn resolved_definition(&self, resolution: &hir::Resolution) -> Option<DefinitionID> {
        match resolution {
            hir::Resolution::StdItem(item) => self.gcx.std_item_def(*item),
            _ => resolution.definition_id(),
        }
    }

    fn record_literal_fields(&mut self, literal: &hir::StructLiteral, ty: Option<Ty<'ctx>>) {
        let Some(definition) = ty.and_then(|ty| self.gcx.source_struct_definition(ty)) else {
            return;
        };
        for field in &literal.fields {
            // Shorthand fields are also local variable reads. Keep their local target.
            if let Some(label) = field.label
                && let Some(field) = definition
                    .fields
                    .iter()
                    .find(|field| field.name == label.identifier.symbol)
            {
                self.record(
                    Some(field.ty),
                    label.identifier.span,
                    Some(field.def_id),
                    None,
                    None,
                );
            }
        }
    }

    fn record_local(&mut self, id: hir::NodeID, span: Span) {
        let anchor = self.next_anchor();
        if let Some(anchor) = &anchor
            && let Some(source) = SourceRange::capture(self.gcx, span)
        {
            self.locals.insert(
                id,
                LocalDeclaration {
                    source,
                    anchor: anchor.clone(),
                },
            );
        }
        self.record(self.types.try_node_type(id), span, None, None, anchor);
    }

    fn start_body(&mut self, id: DefinitionID, node: &hir::Function) -> Option<BodyTraversal> {
        let declaration = self.declarations.get(&id)?;
        let span = node.block.as_ref()?.span;
        let source = SourceRange::capture(self.gcx, span)?;
        let text = self.gcx.dcx().source_text(span)?;
        let identity = Arc::new(BodyIdentity {
            owner: declaration.anchor.clone(),
            content: blake3::hash(text.as_bytes()),
        });
        self.bodies.push(BodyRecord {
            identity: Arc::clone(&identity),
            declaration: declaration.location.clone(),
            source,
        });
        Some(BodyTraversal {
            identity,
            definition: id,
            next_ordinal: 0,
        })
    }
}

impl HirVisitor for OccurrenceCollector<'_, '_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) {
        if matches!(node.kind, hir::DeclarationKind::Struct(_)) {
            self.record(
                self.gcx.try_get_type(node.id),
                node.identifier.span,
                Some(node.id),
                None,
                None,
            );
        }
        hir::walk_declaration(self, node);
    }

    fn visit_field_definition(&mut self, node: &hir::FieldDefinition) {
        self.record(
            self.gcx.try_get_type(node.def_id),
            node.identifier.span,
            Some(node.def_id),
            None,
            None,
        );
        hir::walk_field_definition(self, node);
    }

    fn visit_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        context: hir::FunctionContext,
    ) {
        let body = self.start_body(id, node);
        let previous = std::mem::replace(&mut self.current_body, body);
        hir::walk_function(self, id, node, context);
        self.current_body = previous;
    }

    fn visit_function_parameter(&mut self, parameter: &hir::FunctionParameter) {
        self.record_local(parameter.id, parameter.name.span);
        hir::walk_function_parameter(self, parameter);
    }

    fn visit_path_segment(&mut self, segment: &hir::PathSegment) {
        // This also visits the type qualifier of a relative path. Function
        // sets have no single declaration until the solver selects an overload.
        if let Some(id) = self.resolved_definition(&segment.resolution) {
            self.record(
                self.gcx.try_get_type(id),
                segment.identifier.span,
                Some(id),
                None,
                None,
            );
        }
        hir::walk_path_segment(self, segment);
    }

    fn visit_expression(&mut self, expression: &hir::Expression) {
        let anchor = self.next_anchor();
        if let ExpressionKind::MissingMember { target, insertion } = &expression.kind {
            if let Some(receiver) = self.types.try_node_type(target.id)
                && !receiver.is_error()
                && !receiver.is_infer()
                && let Some(site) = SourceRange::capture(self.gcx, *insertion)
            {
                let mut items = Vec::new();
                if let Some(owner) = &self.current_body {
                    let addressable = self
                        .types
                        .missing_member_receivers
                        .get(&expression.id)
                        .copied()
                        .unwrap_or(false);
                    (items, _) = self.gcx.dcx().with_deferred_diagnostics(|| {
                        crate::sema::tycheck::solve::completion::members(
                            self.gcx,
                            owner.definition,
                            receiver,
                            addressable,
                            *insertion,
                        )
                    });
                }
                self.missing_members.push(MissingMember {
                    insertion: site,
                    receiver: TypeShape::capture(self.gcx, receiver),
                    items,
                });
            }
            hir::walk_expression(self, expression);
            return;
        }
        let target = match &expression.kind {
            ExpressionKind::Call { callee, .. } => callee,
            _ => expression,
        };
        let ty = self.types.try_node_type(expression.id);
        let (span, resolved) = match &target.kind {
            ExpressionKind::MethodCall { name, .. }
            | ExpressionKind::Member { name, .. }
            | ExpressionKind::InferredMember { name } => (name.span, None),
            ExpressionKind::TupleAccess(_, index) => (index.value.span, None),
            ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => (
                path.segments
                    .last()
                    .map_or(path.span, |segment| segment.identifier.span),
                Some(&path.resolution),
            ),
            ExpressionKind::Path(hir::ResolvedPath::Relative(_, segment)) => {
                (segment.identifier.span, Some(&segment.resolution))
            }
            ExpressionKind::StructLiteral(literal) => {
                self.record_literal_fields(literal, ty);
                match &literal.path {
                    hir::ConstructorPath::Qualified {
                        path: hir::ResolvedPath::Resolved(path),
                    } => (
                        path.segments
                            .last()
                            .map_or(path.span, |segment| segment.identifier.span),
                        Some(&path.resolution),
                    ),
                    hir::ConstructorPath::Qualified {
                        path: hir::ResolvedPath::Relative(_, segment),
                    } => (segment.identifier.span, Some(&segment.resolution)),
                    hir::ConstructorPath::Inferred { name, .. } => (name.span, None),
                }
            }
            _ => (expression.span, None),
        };
        let resolved = self
            .types
            .value_resolution(expression.id)
            .or_else(|| resolved.cloned());
        let definition = self
            .types
            .field_definition(target.id)
            .or_else(|| self.types.overload_source(expression.id))
            .or_else(|| self.resolved_definition(resolved.as_ref()?));
        let local = match resolved {
            Some(hir::Resolution::LocalVariable(binding)) => self.locals.get(&binding).cloned(),
            _ => None,
        };
        self.record(ty, span, definition, local, anchor);
        hir::walk_expression(self, expression);
    }

    fn visit_pattern(&mut self, pattern: &hir::Pattern) {
        if let hir::PatternKind::Binding { name } = pattern.kind {
            self.record_local(pattern.id, name.span);
        }
        hir::walk_pattern(self, pattern);
    }
}

#[cfg(test)]
mod tests {
    use super::{
        AnalysisProduct, DiagnosticLevel, IntTy, OwnedConstant, SyntaxUncertainty, TypeShape,
    };
    use crate::{
        compile::config::HarnessMode, hir::DeclarationKind, sema::models::ConstValue,
        test_support::with_source_compiler,
    };
    use std::rc::Rc;

    #[test]
    fn nested_literal_products_survive_session_replacement() {
        let (reply, owner) = with_source_compiler(
            &[("old.tr", "enum Marker { case present }")],
            false,
            HarnessMode::None,
            |compiler| {
                let (package, _) = compiler.analyze().unwrap_or_else(|_| {
                    panic!(
                        "analysis failed: {:?}",
                        compiler.context.dcx().take_recorded_diagnostics()
                    )
                });
                let variant = package
                    .root
                    .declarations
                    .iter()
                    .find_map(|decl| match &decl.kind {
                        DeclarationKind::Enum(decl) => decl.variants.first(),
                        _ => None,
                    })
                    .expect("analyzed variant");
                let gcx = compiler.context;
                let interner = gcx.interner();
                let inner = interner.intern_const_array(vec![
                    ConstValue::String(interner.intern("old name")),
                    ConstValue::Bytes(interner.intern_bytes(&[0, 255])),
                    ConstValue::EnumUnitVariant(variant.ctor_def_id),
                ]);
                let array = interner.intern_const_array(vec![ConstValue::Array(inner)]);
                (
                    OwnedConstant::capture(gcx, ConstValue::Array(array)).expect("copy answer"),
                    Rc::downgrade(&gcx.dcx().symbols),
                )
            },
        );
        assert!(owner.upgrade().is_none());

        with_source_compiler(
            &[("new.tr", "enum Marker { case missing }")],
            false,
            HarnessMode::None,
            |compiler| {
                assert!(compiler.analyze().is_ok());
                let interner = compiler.context.interner();
                let bytes = interner.intern_bytes(&[111]);
                interner.intern_const_array(vec![ConstValue::Bytes(bytes)]);

                let OwnedConstant::Array(outer) = reply else {
                    panic!("expected outer constant array");
                };
                let [OwnedConstant::Array(inner)] = &*outer else {
                    panic!("expected nested constant array");
                };
                let [
                    OwnedConstant::String(name),
                    OwnedConstant::Bytes(bytes),
                    OwnedConstant::EnumUnitVariant(variant),
                ] = &**inner
                else {
                    panic!("expected name, bytes and enum declaration");
                };
                assert_eq!(name, "old name");
                assert_eq!(&**bytes, &[0, 255]);
                assert_eq!(variant.name, "present");
                assert!(variant.source.path.ends_with("src/old.tr"));
            },
        );
    }

    #[test]
    fn exported_answers_keep_their_original_revision_and_destination() {
        let declarations = include_str!("analysis_oracle/dispatch.tr");
        let calls = include_str!("analysis_oracle/calls.tr");
        let analyze = |revision, calls: &str| {
            let (reply, owner) = with_source_compiler(
                &[("dispatch.tr", declarations), ("calls.tr", calls)],
                false,
                HarnessMode::None,
                |compiler| {
                    (
                        compiler.analyze_owned(revision),
                        Rc::downgrade(&compiler.context.dcx().symbols),
                    )
                },
            );
            assert!(owner.upgrade().is_none());
            reply
        };
        let old = analyze(17, calls);
        let new = analyze(
            18,
            &calls.replace("Cell[int64] = cell", "Cell[int32] = cell"),
        );
        let label_lines = |reply: &AnalysisProduct| {
            assert!(reply.complete, "{:?}", reply.diagnostics);
            reply
                .occurrences
                .iter()
                .filter_map(|occurrence| {
                    let declaration = occurrence.declaration.as_ref()?;
                    (declaration.name == "label").then(|| {
                        assert_eq!(occurrence.ty, TypeShape::Int(IntTy::I32));
                        assert!(occurrence.source.path.ends_with("src/calls.tr"));
                        assert!(declaration.source.path.ends_with("src/dispatch.tr"));
                        declaration.source.start.line
                    })
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(old.revision, 17);
        assert_eq!(new.revision, 18);
        let old_lines = label_lines(&old);
        let new_lines = label_lines(&new);
        assert_eq!(old_lines.len(), 2);
        assert_eq!(new_lines.len(), 2);
        assert_ne!(old_lines[0], old_lines[1]);
        assert_eq!(new_lines, vec![old_lines[0]; 2]);

        let broken = analyze(19, "func broken() { missingName() }");
        assert!(!broken.complete);
        assert!(broken.occurrences.is_empty());
        assert!(broken.diagnostics.iter().any(|diagnostic| {
            diagnostic.level == DiagnosticLevel::Error
                && diagnostic.message.contains("missingName")
                && diagnostic
                    .source
                    .as_ref()
                    .is_some_and(|source| source.path.ends_with("src/calls.tr"))
        }));
    }

    #[test]
    fn incomplete_members_keep_receiver_types_and_sibling_answers() {
        let damaged = "struct Board { value: int32 }\n\
                       func edit(_ board: Board) -> int32 { board. }";
        let sibling = "func helper() -> int32 { 1 }\nfunc caller() -> int32 { helper() }";
        let check = |source: &str, partial| {
            with_source_compiler(
                &[("edit.tr", source), ("sibling.tr", sibling)],
                false,
                HarnessMode::None,
                |compiler| {
                    if partial {
                        compiler.analyze_partial_owned(7)
                    } else {
                        compiler.analyze_owned(7)
                    }
                },
            )
        };

        let result = check(damaged, true);
        assert!(!result.complete);
        assert_eq!(result.syntax_uncertainty, SyntaxUncertainty::None);
        let [member] = result.missing_members.as_slice() else {
            panic!("missing receiver facts: {:?}", result.diagnostics);
        };
        assert!(member.insertion.path.ends_with("src/edit.tr"));
        assert_eq!(member.insertion.start.line, 1);
        assert_eq!(member.insertion.start, member.insertion.end);
        assert!(matches!(&member.receiver,
            TypeShape::Nominal { declaration: Some(declaration), .. }
                if declaration.name == "Board"));
        assert!(result.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == Some(crate::parse::MISSING_MEMBER_NAME_DIAGNOSTIC)
                && diagnostic.source.as_ref() == Some(&member.insertion)
        }));
        assert!(result.occurrences.iter().any(|occurrence| {
            occurrence.source.path.ends_with("src/sibling.tr")
                && occurrence
                    .declaration
                    .as_ref()
                    .is_some_and(|declaration| declaration.name == "helper")
        }));

        let strict = check(damaged, false);
        assert!(!strict.complete);
        assert!(strict.occurrences.is_empty());
        assert!(strict.missing_members.is_empty());
        let repaired = check(&damaged.replace("board. ", "board.value "), true);
        assert!(repaired.complete, "{:?}", repaired.diagnostics);
        assert!(repaired.missing_members.is_empty());
        assert!(repaired.diagnostics.is_empty());
    }

    #[test]
    fn member_completion_checks_scope_and_receiver_place() {
        let source = r#"
struct Board {
    value: int32
    private hidden: int32
}
extend Board {
    public func show() -> int32 { self.value }
    private func secret() -> int32 { self.hidden }
    public static func reset() {}
}
extend &Board {
    public func borrowed() -> int32 { self.value }
}
func missing(_ board: Board) {
    board.
}
"#;
        with_source_compiler(
            &[("main.tr", source)],
            false,
            HarnessMode::None,
            |compiler| {
                let result = compiler.analyze_partial_owned(1);
                let [member] = result.missing_members.as_slice() else {
                    panic!("missing receiver facts: {:?}", result.diagnostics);
                };
                let items = member
                    .items
                    .iter()
                    .map(|item| (item.name.as_str(), item.is_method))
                    .collect::<Vec<_>>();
                assert_eq!(
                    items,
                    [("borrowed", true), ("show", true), ("value", false)]
                );
            },
        );
    }

    #[test]
    fn incomplete_optional_members_keep_the_unwrapped_receiver_type() {
        use crate::{
            PackageIndex,
            compile::Compiler,
            hir::StdItem,
            sema::std_items::{StdItemEntry, StdItemRegistry},
            test_support::TempDir,
        };
        use std::fs;

        let std_root = TempDir::new("optional-recovery");
        fs::create_dir(std_root.join("src")).unwrap();
        fs::write(
            std_root.join("src/lib.tr"),
            "public enum Optional[T] { case none, some(T) }",
        )
        .unwrap();

        with_source_compiler(
            &[(
                "main.tr",
                "struct Board { value: int32 }\n\
                 func edit(_ board: Board?) -> int32? { board?. }",
            )],
            false,
            HarnessMode::None,
            |compiler| {
                let gcx = compiler.context;
                let mut config = gcx.config.clone();
                config.src = std_root.to_path_buf();
                config.index = PackageIndex::new(0);
                config.identifier = "std".into();
                let config = gcx.store.arenas.configs.alloc(config);
                let mut std = Compiler::new(*gcx, config);
                let (package, _) = std.analyze().unwrap_or_else(|_| {
                    panic!(
                        "optional fixture: {:?}",
                        gcx.dcx().take_recorded_diagnostics()
                    )
                });
                let declaration = &package.root.declarations[0];
                let DeclarationKind::Enum(optional) = &declaration.kind else {
                    panic!("expected an enum");
                };
                let none = &optional.variants[0];
                let some = &optional.variants[1];
                let entries = [
                    (StdItem::Optional, declaration.id),
                    (StdItem::OptionalNoneVariant, none.def_id),
                    (StdItem::OptionalNoneCtor, none.ctor_def_id),
                    (StdItem::OptionalSomeVariant, some.def_id),
                    (StdItem::OptionalSomeCtor, some.ctor_def_id),
                ];
                let registry = StdItemRegistry::from_entries(entries.map(|(item, id)| {
                    (
                        item,
                        StdItemEntry {
                            def_id: id,
                            def_kind: gcx.definition_kind(id),
                            span: gcx.definition_ident(id).span,
                        },
                    )
                }));
                gcx.store.std_provider_index.set(Some(config.index));
                gcx.store
                    .std_items
                    .borrow_mut()
                    .replace((config.index, registry));

                let result = compiler.analyze_partial_owned(1);
                assert!(!result.complete);
                let [member] = result.missing_members.as_slice() else {
                    panic!("missing receiver facts: {:?}", result.diagnostics);
                };
                assert!(matches!(&member.receiver,
                    TypeShape::Nominal { declaration: Some(declaration), .. }
                        if declaration.name == "Board"));
                assert_eq!(
                    member
                        .items
                        .iter()
                        .map(|item| item.name.as_str())
                        .collect::<Vec<_>>(),
                    ["value"]
                );
                assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
                assert_eq!(
                    result.diagnostics[0].code,
                    Some(crate::parse::MISSING_MEMBER_NAME_DIAGNOSTIC)
                );
            },
        )
    }

    #[test]
    fn syntax_damage_without_a_declaration_boundary_is_marked_uncertain() {
        for damaged in ["this is not a declaration", "\"unterminated"] {
            with_source_compiler(
                &[
                    ("bad.tr", damaged),
                    ("healthy.tr", "func healthy() -> int32 { 42 }"),
                ],
                false,
                HarnessMode::None,
                |compiler| {
                    let result = compiler.analyze_partial_owned(12);
                    assert!(!result.complete);
                    let SyntaxUncertainty::Files(files) = result.syntax_uncertainty else {
                        panic!("expected uncertainty for bad.tr: {:?}", result.diagnostics);
                    };
                    assert_eq!(files.len(), 1);
                    assert!(files[0].ends_with("src/bad.tr"));
                    assert!(
                        result.occurrences.iter().any(|occurrence| {
                            occurrence.source.path.ends_with("src/healthy.tr")
                                && occurrence.ty == TypeShape::Int(IntTy::I32)
                        }),
                        "{:?}",
                        result.diagnostics
                    );
                },
            );
        }
    }

    #[test]
    fn an_incomplete_const_function_cannot_send_a_recovery_hole_to_mir() {
        with_source_compiler(
            &[(
                "const.tr",
                "const func broken(_ value: int32) -> int32 { value. }\n\
                 const RESULT: int32 = broken(1)",
            )],
            false,
            HarnessMode::None,
            |compiler| {
                let result = compiler.analyze_partial_owned(13);
                assert!(!result.complete);
                assert!(result.missing_members.is_empty());
                assert!(matches!(
                    result.syntax_uncertainty,
                    SyntaxUncertainty::Files(_)
                ));
                assert!(
                    result
                        .diagnostics
                        .iter()
                        .any(|diagnostic| { diagnostic.message.contains("expected identifier") })
                );
            },
        )
    }

    #[test]
    fn exported_diagnostics_keep_notes_and_suggestions() {
        use crate::diagnostics::{Applicability, Diagnostic, Suggestion};
        use crate::span::{Position, Span};

        with_source_compiler(
            &[("source.tr", "func read() -> int32 { 42 }")],
            false,
            HarnessMode::None,
            |compiler| {
                let gcx = compiler.context;
                let source = gcx.config.src.join("src/source.tr");
                let file = gcx.dcx().add_file_mapping(source.clone());
                let span = Span {
                    file,
                    start: Position { line: 0, offset: 5 },
                    end: Position { line: 0, offset: 9 },
                };
                let mut diagnostic =
                    Diagnostic::new("example warning".into(), Some(span), DiagnosticLevel::Warn);
                diagnostic.code = Some(17);
                diagnostic.children.push(Diagnostic::new(
                    "name declared here".into(),
                    Some(span),
                    DiagnosticLevel::Info,
                ));
                diagnostic.suggestion = Some(Suggestion {
                    message: "use a clearer name".into(),
                    span,
                    replacement: "readValue".into(),
                    applicability: Applicability::MachineApplicable,
                });
                gcx.dcx().emit(diagnostic);

                let result = compiler.analyze_partial_owned(14);
                assert!(result.complete, "{:?}", result.diagnostics);
                let [diagnostic] = result.diagnostics.as_slice() else {
                    panic!("expected one warning");
                };
                assert_eq!(diagnostic.code, Some(17));
                assert_eq!(diagnostic.level, DiagnosticLevel::Warn);
                assert_eq!(diagnostic.notes[0].message, "name declared here");
                assert_eq!(diagnostic.notes[0].source.as_ref().unwrap().path, source);
                let suggestion = diagnostic.suggestion.as_ref().unwrap();
                assert_eq!(suggestion.replacement, "readValue");
                assert_eq!(suggestion.applicability, Applicability::MachineApplicable);
                assert_eq!(suggestion.source.start, span.start);
                assert_eq!(suggestion.source.end, span.end);
            },
        )
    }
}
