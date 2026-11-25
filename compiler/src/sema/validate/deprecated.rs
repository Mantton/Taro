//! Deprecation attribute validation and use-site diagnostics.
//!
//! `@deprecated` attributes travel in `TypeDatabase::def_to_attributes` through
//! package metadata, so downstream consumers see identical warnings and
//! machine-applicable replacement suggestions on both cold and warm builds.

use rustc_hash::FxHashSet;

use crate::{
    compile::context::GlobalContext,
    diagnostics::{Applicability, Suggestion},
    hir::{self, Attribute, AttributeArg, DefinitionID, HirVisitor, KnownAttribute, Literal, Resolution},
    sema::tycheck::results::TypeCheckResults,
    span::Span,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeprecationInfo {
    pub message: Option<String>,
    pub replacement: Option<String>,
    pub advisory: bool,
}

fn is_valid_replacement_identifier(text: &str) -> bool {
    let mut chars = text.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

pub(crate) fn validate_attributes(gcx: GlobalContext<'_>, attributes: &[Attribute]) {
    let mut seen = false;
    for attr in attributes
        .iter()
        .filter(|attr| attr.as_known(gcx) == Some(KnownAttribute::Deprecated))
    {
        if seen {
            gcx.dcx()
                .emit_error("duplicate @deprecated attribute".into(), Some(attr.span));
            continue;
        }
        seen = true;

        let Some(args) = attr.args.as_ref() else {
            continue;
        };

        let mut seen_message = false;
        let mut seen_replace = false;
        let mut seen_advisory = false;
        for arg in &args.items {
            match arg {
                AttributeArg::Literal {
                    value: Literal::String(_),
                    span,
                } => {
                    if seen_message {
                        gcx.dcx().emit_error(
                            "duplicate deprecation message in @deprecated".into(),
                            Some(*span),
                        );
                    }
                    seen_message = true;
                }
                AttributeArg::KeyValue { key, value, span } => {
                    let key_name = key.symbol.as_str();
                    match (key_name, value) {
                        ("message", Literal::String(_)) => {
                            if seen_message {
                                gcx.dcx().emit_error(
                                    "duplicate deprecation message in @deprecated".into(),
                                    Some(*span),
                                );
                            }
                            seen_message = true;
                        }
                        ("replace", Literal::String(sym)) => {
                            if seen_replace {
                                gcx.dcx().emit_error(
                                    "duplicate replacement in @deprecated".into(),
                                    Some(*span),
                                );
                            }
                            if sym.as_str().trim().is_empty() {
                                gcx.dcx().emit_error(
                                    "@deprecated replace value cannot be empty".into(),
                                    Some(*span),
                                );
                            }
                            seen_replace = true;
                        }
                        ("message" | "replace", _) => {
                            gcx.dcx().emit_error(
                                format!("@deprecated '{key_name}' must be a string literal"),
                                Some(*span),
                            );
                        }
                        _ => {
                            gcx.dcx().emit_error(
                                format!(
                                    "unknown @deprecated argument '{key_name}'; expected 'message', 'replace', or 'advisory'"
                                ),
                                Some(*span),
                            );
                        }
                    }
                }
                AttributeArg::Flag { key, span } => {
                    if key.symbol.as_str() == "advisory" {
                        if seen_advisory {
                            gcx.dcx().emit_error(
                                "duplicate 'advisory' flag in @deprecated".into(),
                                Some(*span),
                            );
                        }
                        seen_advisory = true;
                    } else {
                        gcx.dcx().emit_error(
                            format!(
                                "unknown @deprecated flag '{}'; expected 'advisory'",
                                key.symbol.as_str()
                            ),
                            Some(*span),
                        );
                    }
                }
                AttributeArg::Literal { span, .. } => {
                    gcx.dcx().emit_error(
                        "@deprecated positional argument must be a string literal".into(),
                        Some(*span),
                    );
                }
            }
        }
    }
}

pub fn deprecation_info(gcx: GlobalContext<'_>, def_id: DefinitionID) -> Option<DeprecationInfo> {
    let attrs = gcx.attributes_of(def_id);
    let attr = attrs
        .iter()
        .find(|attr| attr.as_known(gcx) == Some(KnownAttribute::Deprecated))?;

    let mut message = None;
    let mut replacement = None;
    let mut advisory = false;

    if let Some(args) = attr.args.as_ref() {
        for arg in &args.items {
            match arg {
                AttributeArg::Literal {
                    value: Literal::String(sym),
                    ..
                } => {
                    message = Some(gcx.symbol_text(*sym).to_string());
                }
                AttributeArg::KeyValue {
                    key,
                    value: Literal::String(sym),
                    ..
                } => match key.symbol.as_str() {
                    "message" => message = Some(gcx.symbol_text(*sym).to_string()),
                    "replace" => replacement = Some(gcx.symbol_text(*sym).to_string()),
                    _ => {}
                },
                AttributeArg::Flag { key, .. } if key.symbol.as_str() == "advisory" => {
                    advisory = true;
                }
                _ => {}
            }
        }
    }

    Some(DeprecationInfo {
        message,
        replacement,
        advisory,
    })
}

pub fn run<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
    results: &TypeCheckResults<'ctx>,
) {
    let mut actor = Actor {
        gcx,
        results,
        emitted: FxHashSet::default(),
    };
    hir::walk_package(&mut actor, package);
}

struct Actor<'ctx, 'results> {
    gcx: GlobalContext<'ctx>,
    results: &'results TypeCheckResults<'ctx>,
    emitted: FxHashSet<(DefinitionID, Span)>,
}

impl<'ctx> Actor<'ctx, '_> {
    fn check_def_use(&mut self, def_id: DefinitionID, ident_span: Span, fallback_name: &str) {
        if !self.emitted.insert((def_id, ident_span)) {
            return;
        }
        let Some(info) = deprecation_info(self.gcx, def_id) else {
            return;
        };

        let display_name = self
            .gcx
            .try_definition_ident(def_id)
            .map(|id| self.gcx.symbol_text(id.symbol).to_string())
            .unwrap_or_else(|| fallback_name.to_string());

        let diagnostic_message = match (&info.message, &info.replacement) {
            (Some(msg), Some(rep)) => {
                format!("'{display_name}' is deprecated: {msg} (use '{rep}')")
            }
            (Some(msg), None) => format!("'{display_name}' is deprecated: {msg}"),
            (None, Some(rep)) => format!("'{display_name}' is deprecated: use '{rep}' instead"),
            (None, None) => format!("'{display_name}' is deprecated"),
        };

        let suggestion = info.replacement.map(|rep| {
            let applicability = if !info.advisory && is_valid_replacement_identifier(&rep) {
                Applicability::MachineApplicable
            } else {
                Applicability::MaybeIncorrect
            };
            let help_msg = match applicability {
                Applicability::MachineApplicable => format!("replace '{display_name}' with '{rep}'"),
                Applicability::MaybeIncorrect => {
                    format!("consider replacing '{display_name}' with '{rep}'")
                }
            };
            Suggestion {
                message: help_msg,
                span: ident_span,
                replacement: rep,
                applicability,
            }
        });

        self.gcx
            .dcx()
            .emit_warning_with_suggestion(diagnostic_message, Some(ident_span), suggestion);
    }

    fn resolve_def_from_resolution(&self, resolution: &Resolution) -> Option<DefinitionID> {
        match resolution {
            Resolution::Definition(id, _) => Some(*id),
            _ => None,
        }
    }

    fn resolve_def_from_path(&self, path: &hir::ResolvedPath) -> Option<DefinitionID> {
        match path {
            hir::ResolvedPath::Resolved(p) => self.resolve_def_from_resolution(&p.resolution),
            hir::ResolvedPath::Relative(_, seg) => {
                self.resolve_def_from_resolution(&seg.resolution)
            }
        }
    }

    fn path_leaf_span_and_name(path: &hir::ResolvedPath, fallback: Span) -> (Span, String) {
        match path {
            hir::ResolvedPath::Resolved(p) => p
                .segments
                .last()
                .map(|seg| (seg.identifier.span, seg.identifier.symbol.as_str().to_string()))
                .unwrap_or((fallback, String::new())),
            hir::ResolvedPath::Relative(_, seg) => {
                (seg.identifier.span, seg.identifier.symbol.as_str().to_string())
            }
        }
    }

    fn callee_leaf_span_and_name(callee: &hir::Expression) -> Option<(Span, String)> {
        match &callee.kind {
            hir::ExpressionKind::Path(path) => {
                Some(Self::path_leaf_span_and_name(path, callee.span))
            }
            hir::ExpressionKind::Member { name, .. } => {
                Some((name.span, name.symbol.as_str().to_string()))
            }
            _ => None,
        }
    }
}

impl<'ctx> HirVisitor for Actor<'ctx, '_> {
    fn visit_expression(&mut self, node: &hir::Expression) -> Self::Result {
        match &node.kind {
            hir::ExpressionKind::Call { callee, .. } => {
                let def_id = self
                    .results
                    .overload_source(node.id)
                    .or_else(|| {
                        self.results
                            .selected_method_calls
                            .get(&node.id)
                            .map(|(id, _)| *id)
                    })
                    .or_else(|| {
                        self.results
                            .interface_call(node.id)
                            .map(|info| info.method_id)
                    });
                if let (Some(def_id), Some((ident_span, name))) =
                    (def_id, Self::callee_leaf_span_and_name(callee))
                {
                    self.check_def_use(def_id, ident_span, &name);
                }
            }
            hir::ExpressionKind::MethodCall { name, .. } => {
                let def_id = self
                    .results
                    .overload_source(node.id)
                    .or_else(|| {
                        self.results
                            .selected_method_calls
                            .get(&node.id)
                            .map(|(id, _)| *id)
                    })
                    .or_else(|| {
                        self.results
                            .interface_call(node.id)
                            .map(|info| info.method_id)
                    })
                    .or_else(|| {
                        self.results
                            .value_resolution(node.id)
                            .and_then(|r| self.resolve_def_from_resolution(&r))
                    });
                if let Some(def_id) = def_id {
                    self.check_def_use(def_id, name.span, name.symbol.as_str());
                }
            }
            hir::ExpressionKind::Path(path) => {
                let (ident_span, name) = Self::path_leaf_span_and_name(path, node.span);
                let def_id = self
                    .results
                    .overload_source(node.id)
                    .or_else(|| {
                        self.results
                            .value_resolution(node.id)
                            .and_then(|r| self.resolve_def_from_resolution(&r))
                    })
                    .or_else(|| self.resolve_def_from_path(path));
                if let Some(def_id) = def_id {
                    self.check_def_use(def_id, ident_span, &name);
                }
            }
            hir::ExpressionKind::Member { name, .. } => {
                let def_id = self
                    .results
                    .overload_source(node.id)
                    .or_else(|| {
                        self.results
                            .value_resolution(node.id)
                            .and_then(|r| self.resolve_def_from_resolution(&r))
                    });
                if let Some(def_id) = def_id {
                    self.check_def_use(def_id, name.span, name.symbol.as_str());
                }
            }
            hir::ExpressionKind::StructLiteral(lit) => {
                if let hir::ConstructorPath::Qualified { path } = &lit.path {
                    let (ident_span, name) = Self::path_leaf_span_and_name(path, node.span);
                    if let Some(def_id) = self.resolve_def_from_path(path) {
                        self.check_def_use(def_id, ident_span, &name);
                    }
                }
            }
            _ => {}
        }
        hir::walk_expression(self, node);
    }

    fn visit_type(&mut self, node: &hir::Type) -> Self::Result {
        if let hir::TypeKind::Nominal(path) = &node.kind {
            let (ident_span, name) = Self::path_leaf_span_and_name(path, node.span);
            if let Some(def_id) = self.resolve_def_from_path(path) {
                self.check_def_use(def_id, ident_span, &name);
            }
        }
        hir::walk_type(self, node);
    }
}
