use crate::{
    compile::context::GlobalContext,
    hir::{self, DeclarationKind, KnownAttribute},
};

/// Compile-time test selection options used by `taro test`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TestSelection {
    name_filter: Option<String>,
    tags: Vec<String>,
}

impl TestSelection {
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

    pub fn matches(&self, test: &TestCase) -> bool {
        let name_matches = if let Some(filter) = &self.name_filter {
            normalize_qualified_name_for_matching(&test.display_name).contains(filter)
        } else {
            true
        };
        if !name_matches {
            return false;
        }

        if self.tags.is_empty() {
            return true;
        }

        test.tags
            .iter()
            .filter_map(|tag| normalize_filter_component(tag))
            .map(|tag| tag.to_ascii_lowercase())
            .any(|tag| self.tags.iter().any(|wanted| wanted == &tag))
    }

    pub fn is_empty(&self) -> bool {
        self.name_filter.is_none() && self.tags.is_empty()
    }
}

/// Metadata for a single discovered test function.
#[derive(Debug, Clone)]
pub struct TestCase {
    /// DefinitionID of the test function
    pub id: hir::DefinitionID,
    /// Display name for test output (e.g., "module::test_name")
    pub display_name: String,
    /// Whether this test must be run through the async runtime.
    pub is_async: bool,
    /// Whether this test is marked `@skip`
    pub skipped: bool,
    /// Reason string from `@skip("reason")`, if any
    pub skip_reason: Option<String>,
    /// Whether this test is marked `@expectPanic`
    pub expect_panic: bool,
    /// Expected panic message from `@expectPanic("message")`, if any
    pub expected_panic_message: Option<String>,
    /// Tags inherited from namespaces and declared on this test function.
    pub tags: Vec<String>,
}

pub fn filter_tests(mut tests: Vec<TestCase>, selection: &TestSelection) -> Vec<TestCase> {
    if selection.is_empty() {
        return tests;
    }
    tests.retain(|test| selection.matches(test));
    tests
}

/// Walk the HIR package and collect all `@test`-annotated functions.
/// Validates that test functions have `() -> void` signatures.
pub fn collect_tests(
    package: &hir::Package,
    gcx: GlobalContext<'_>,
) -> crate::error::CompileResult<Vec<TestCase>> {
    let mut tests = Vec::new();
    let mut path = Vec::new();
    let inherited_tags = Vec::new();
    collect_from_module(&package.root, gcx, &mut path, &inherited_tags, &mut tests)?;
    Ok(tests)
}

fn collect_from_module(
    module: &hir::Module,
    gcx: GlobalContext<'_>,
    path: &mut Vec<String>,
    inherited_tags: &[String],
    tests: &mut Vec<TestCase>,
) -> crate::error::CompileResult<()> {
    for decl in &module.declarations {
        collect_from_declaration(decl, gcx, path, inherited_tags, tests)?;
    }
    for sub in &module.submodules {
        let name = gcx.symbol_text(sub.name).to_string();
        path.push(name);
        collect_from_module(sub, gcx, path, inherited_tags, tests)?;
        path.pop();
    }
    Ok(())
}

fn collect_from_declaration(
    decl: &hir::Declaration,
    gcx: GlobalContext<'_>,
    path: &mut Vec<String>,
    inherited_tags: &[String],
    tests: &mut Vec<TestCase>,
) -> crate::error::CompileResult<()> {
    let has_test = decl
        .attributes
        .iter()
        .any(|a| a.as_known(gcx) == Some(KnownAttribute::Test));
    let declared_tags = collect_decl_tags(decl, gcx, has_test)?;

    match &decl.kind {
        DeclarationKind::Function(func) if has_test => {
            // Validate: test functions must take no parameters
            if !func.signature.prototype.inputs.is_empty() {
                gcx.dcx().emit_error(
                    "@test functions must take no parameters".into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }

            // Validate: test functions must return void (no return type annotation)
            if func.signature.prototype.output.is_some() {
                gcx.dcx()
                    .emit_error("@test functions must return void".into(), Some(decl.span));
                return Err(crate::error::ReportedError);
            }

            // Validate: test functions must not have generic parameters
            if func.generics.type_parameters.is_some() {
                gcx.dcx().emit_error(
                    "@test functions must not be generic".into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }

            let fn_name = gcx.symbol_text(decl.identifier.symbol).to_string();
            let display_name = if path.is_empty() {
                fn_name
            } else {
                format!("{}::{}", path.join("::"), fn_name)
            };

            let mut skipped = false;
            let mut skip_reason = None;
            let mut expect_panic = false;
            let mut expected_panic_message = None;
            let mut tags = inherited_tags.to_vec();
            merge_unique_tags_case_insensitive(&mut tags, declared_tags);

            for attr in &decl.attributes {
                match attr.as_known(gcx) {
                    Some(KnownAttribute::Skip) => {
                        skipped = true;
                        skip_reason = attr.first_string_arg(gcx);
                    }
                    Some(KnownAttribute::ExpectPanic) => {
                        expect_panic = true;
                        expected_panic_message = attr.first_string_arg(gcx);
                    }
                    _ => {}
                }
            }

            tests.push(TestCase {
                id: decl.id,
                display_name,
                is_async: func.is_async,
                skipped,
                skip_reason,
                expect_panic,
                expected_panic_message,
                tags,
            });
        }
        DeclarationKind::Namespace(ns) => {
            // Recurse into namespaces for hierarchical test naming
            let ns_name = gcx.symbol_text(decl.identifier.symbol).to_string();
            let mut namespace_tags = inherited_tags.to_vec();
            merge_unique_tags_case_insensitive(&mut namespace_tags, declared_tags);
            path.push(ns_name);
            for inner_decl in &ns.declarations {
                collect_from_declaration(inner_decl, gcx, path, &namespace_tags, tests)?;
            }
            path.pop();
        }
        _ => {
            if has_test {
                gcx.dcx().emit_error(
                    "@test can only be applied to functions".into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }
        }
    }
    Ok(())
}

fn collect_decl_tags(
    decl: &hir::Declaration,
    gcx: GlobalContext<'_>,
    has_test: bool,
) -> crate::error::CompileResult<Vec<String>> {
    let tags_allowed = matches!(&decl.kind, DeclarationKind::Namespace(_))
        || (matches!(&decl.kind, DeclarationKind::Function(_)) && has_test);

    let mut tags = Vec::new();
    for attr in &decl.attributes {
        if attr.as_known(gcx) != Some(KnownAttribute::Tag) {
            continue;
        }

        if !tags_allowed {
            gcx.dcx().emit_error(
                "@tag can only be applied to namespaces or @test functions".into(),
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

fn merge_unique_tags_case_insensitive(target: &mut Vec<String>, additions: Vec<String>) {
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
    use super::{TestCase, TestSelection, filter_tests};
    use crate::{
        PackageIndex,
        sema::resolve::models::{DefinitionID, DefinitionIndex},
    };

    fn test_case(name: &str, tags: &[&str]) -> TestCase {
        TestCase {
            id: DefinitionID::new(PackageIndex::new(0), DefinitionIndex::from_raw(0)),
            display_name: name.to_string(),
            is_async: false,
            skipped: false,
            skip_reason: None,
            expect_panic: false,
            expected_panic_message: None,
            tags: tags.iter().map(|t| (*t).to_string()).collect(),
        }
    }

    #[test]
    fn filter_matches_case_insensitive_dot_and_colon_separators() {
        let selection = TestSelection::new(Some("Core.Math.Add".into()), vec![]);
        let test = test_case("core::math::add", &[]);
        assert!(selection.matches(&test));
    }

    #[test]
    fn tag_matching_is_case_insensitive_and_any_match() {
        let selection = TestSelection::new(None, vec!["SMOKE".into(), "slow".into()]);
        assert!(selection.matches(&test_case("x::a", &["smoke"])));
        assert!(selection.matches(&test_case("x::a", &["SLOW"])));
        assert!(!selection.matches(&test_case("x::a", &["unit"])));
    }

    #[test]
    fn filter_and_tag_use_and_logic() {
        let selection = TestSelection::new(Some("core.math".into()), vec!["smoke".into()]);
        assert!(selection.matches(&test_case("core::math::add", &["smoke"])));
        assert!(!selection.matches(&test_case("core::math::add", &["slow"])));
        assert!(!selection.matches(&test_case("core::io::add", &["smoke"])));
    }

    #[test]
    fn filter_tests_returns_zero_for_no_match() {
        let selection = TestSelection::new(Some("does.not.exist".into()), vec!["smoke".into()]);
        let filtered = filter_tests(vec![test_case("core::math::add", &["smoke"])], &selection);
        assert!(filtered.is_empty());
    }

    #[test]
    fn empty_selection_returns_all_tests() {
        let selection = TestSelection::new(None, vec![]);
        let tests = vec![test_case("core::math::add", &[])];
        let filtered = filter_tests(tests.clone(), &selection);
        assert_eq!(filtered.len(), tests.len());
    }
}
