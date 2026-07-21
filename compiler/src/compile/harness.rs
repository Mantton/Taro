use crate::{
    compile::context::GlobalContext,
    hir::{self, DeclarationKind, KnownAttribute},
};

/// Name and tag selection shared by generated test and benchmark harnesses.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct HarnessSelection {
    name_filter: Option<String>,
    tags: Vec<String>,
}

impl HarnessSelection {
    pub fn new(name_filter: Option<String>, tags: Vec<String>) -> Self {
        let name_filter = name_filter
            .as_deref()
            .and_then(normalize_filter_component)
            .map(normalize_qualified_name_for_matching);

        let mut normalized_tags = Vec::new();
        for tag in tags {
            let Some(tag) = normalize_filter_component(&tag) else {
                continue;
            };
            let normalized = tag.to_ascii_lowercase();
            if !normalized_tags
                .iter()
                .any(|existing| existing == &normalized)
            {
                normalized_tags.push(normalized);
            }
        }

        Self {
            name_filter,
            tags: normalized_tags,
        }
    }

    pub fn matches(&self, display_name: &str, tags: &[String]) -> bool {
        let name_matches = if let Some(filter) = &self.name_filter {
            normalize_qualified_name_for_matching(display_name).contains(filter)
        } else {
            true
        };
        if !name_matches {
            return false;
        }

        if self.tags.is_empty() {
            return true;
        }

        tags.iter()
            .filter_map(|tag| normalize_filter_component(tag))
            .map(|tag| tag.to_ascii_lowercase())
            .any(|tag| self.tags.iter().any(|wanted| wanted == &tag))
    }

    pub fn is_empty(&self) -> bool {
        self.name_filter.is_none() && self.tags.is_empty()
    }

    pub fn normalized_name_filter(&self) -> Option<&str> {
        self.name_filter.as_deref()
    }

    pub fn normalized_tags(&self) -> &[String] {
        &self.tags
    }
}

/// Parse tags declared on a namespace or one marked harness function.
pub fn collect_decl_tags(
    decl: &hir::Declaration,
    gcx: GlobalContext<'_>,
    has_case_marker: bool,
    marker_name: &str,
) -> crate::error::CompileResult<Vec<String>> {
    let tags_allowed = matches!(&decl.kind, DeclarationKind::Namespace(_))
        || (matches!(&decl.kind, DeclarationKind::Function(_)) && has_case_marker);

    let mut tags = Vec::new();
    for attr in &decl.attributes {
        if attr.as_known(gcx) != Some(KnownAttribute::Tag) {
            continue;
        }

        if !tags_allowed {
            gcx.dcx().emit_error(
                format!("@tag can only be applied to namespaces or @{marker_name} functions")
                    .into(),
                Some(attr.span),
            );
            return Err(crate::error::ReportedError);
        }

        let parsed_tags = parse_tag_attribute(attr, gcx)?;
        merge_unique_tags_case_insensitive(&mut tags, parsed_tags);
    }

    Ok(tags)
}

fn parse_tag_attribute(
    attr: &hir::Attribute,
    gcx: GlobalContext<'_>,
) -> crate::error::CompileResult<Vec<String>> {
    let Some(args) = attr.args.as_ref() else {
        gcx.dcx().emit_error(
            "@tag requires at least one argument".into(),
            Some(attr.span),
        );
        return Err(crate::error::ReportedError);
    };

    if args.items.is_empty() {
        gcx.dcx().emit_error(
            "@tag requires at least one argument".into(),
            Some(args.span),
        );
        return Err(crate::error::ReportedError);
    }

    let mut tags = Vec::new();
    for arg in &args.items {
        match arg {
            hir::AttributeArg::Literal { value, span } => {
                let hir::Literal::String(sym) = value else {
                    gcx.dcx().emit_error(
                        "@tag arguments must be string literals, e.g. @tag(\"smoke\", \"slow\")"
                            .into(),
                        Some(*span),
                    );
                    return Err(crate::error::ReportedError);
                };

                let value = gcx.symbol_text(*sym).to_string();
                if normalize_filter_component(&value).is_none() {
                    gcx.dcx()
                        .emit_error("@tag names must not be empty".into(), Some(*span));
                    return Err(crate::error::ReportedError);
                }
                if value.contains('\0') {
                    gcx.dcx().emit_error(
                        "@tag names must not contain a NUL character".into(),
                        Some(*span),
                    );
                    return Err(crate::error::ReportedError);
                }
                tags.push(value);
            }
            hir::AttributeArg::Flag { key, .. } => {
                gcx.dcx().emit_error(
                    "@tag only supports string literal arguments, e.g. @tag(\"smoke\")".into(),
                    Some(key.span),
                );
                return Err(crate::error::ReportedError);
            }
            hir::AttributeArg::KeyValue { key, .. } => {
                gcx.dcx().emit_error(
                    "@tag only supports string literal arguments, e.g. @tag(\"smoke\")".into(),
                    Some(key.span),
                );
                return Err(crate::error::ReportedError);
            }
        }
    }
    Ok(tags)
}

pub fn merge_unique_tags_case_insensitive(target: &mut Vec<String>, additions: Vec<String>) {
    for tag in additions {
        let normalized = tag.to_ascii_lowercase();
        if target
            .iter()
            .any(|existing| existing.to_ascii_lowercase() == normalized)
        {
            continue;
        }
        target.push(tag);
    }
}

fn normalize_filter_component(value: &str) -> Option<&str> {
    let trimmed = value.trim();
    if trimmed.is_empty() {
        None
    } else {
        Some(trimmed)
    }
}

fn normalize_qualified_name_for_matching(value: &str) -> String {
    value.replace("::", ".").to_ascii_lowercase()
}

#[cfg(test)]
mod tests {
    use super::HarnessSelection;

    #[test]
    fn selection_matches_case_insensitive_names_and_separators() {
        let selection = HarnessSelection::new(Some("Core.Math.Add".into()), vec![]);
        assert!(selection.matches("core::math::add", &[]));
    }

    #[test]
    fn selection_combines_name_and_any_requested_tag() {
        let selection = HarnessSelection::new(
            Some("core.math".into()),
            vec!["SMOKE".into(), "slow".into()],
        );
        assert!(selection.matches("core::math::add", &["smoke".into()]));
        assert!(selection.matches("core::math::add", &["SLOW".into()]));
        assert!(!selection.matches("core::math::add", &["unit".into()]));
        assert!(!selection.matches("core::io::add", &["smoke".into()]));
    }
}
