use crate::{
    compile::{
        context::GlobalContext,
        harness::{HarnessSelection, collect_decl_tags, merge_unique_tags_case_insensitive},
    },
    hir::{self, DeclarationKind, KnownAttribute, Mutability, StdItem},
    sema::models::TyKind,
};

/// Runtime benchmark selection used by `taro bench`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BenchmarkSelection {
    inner: HarnessSelection,
}

impl BenchmarkSelection {
    pub fn new(name_filter: Option<String>, tags: Vec<String>) -> Self {
        Self {
            inner: HarnessSelection::new(name_filter, tags),
        }
    }

    pub fn matches(&self, benchmark: &BenchmarkCase) -> bool {
        self.inner.matches(&benchmark.display_name, &benchmark.tags)
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn normalized_name_filter(&self) -> Option<&str> {
        self.inner.normalized_name_filter()
    }

    pub fn normalized_tags(&self) -> &[String] {
        self.inner.normalized_tags()
    }
}

/// Metadata for one `@bench` function embedded in the generated harness.
#[derive(Debug, Clone)]
pub struct BenchmarkCase {
    pub id: hir::DefinitionID,
    pub display_name: String,
    pub skipped: bool,
    pub skip_reason: Option<String>,
    pub tags: Vec<String>,
}

pub fn filter_benchmarks(
    mut benchmarks: Vec<BenchmarkCase>,
    selection: &BenchmarkSelection,
) -> Vec<BenchmarkCase> {
    if selection.is_empty() {
        return benchmarks;
    }
    benchmarks.retain(|benchmark| selection.matches(benchmark));
    benchmarks
}

/// Discover and validate every benchmark in the analyzed root package.
pub fn collect_benchmarks(
    package: &hir::Package,
    gcx: GlobalContext<'_>,
) -> crate::error::CompileResult<Vec<BenchmarkCase>> {
    let mut benchmarks = Vec::new();
    let mut path = Vec::new();
    collect_from_module(&package.root, gcx, &mut path, &[], &mut benchmarks)?;
    Ok(benchmarks)
}

fn collect_from_module(
    module: &hir::Module,
    gcx: GlobalContext<'_>,
    path: &mut Vec<String>,
    inherited_tags: &[String],
    benchmarks: &mut Vec<BenchmarkCase>,
) -> crate::error::CompileResult<()> {
    for decl in &module.declarations {
        collect_from_declaration(decl, gcx, path, inherited_tags, benchmarks)?;
    }
    for submodule in &module.submodules {
        path.push(gcx.symbol_text(submodule.name).to_string());
        collect_from_module(submodule, gcx, path, inherited_tags, benchmarks)?;
        path.pop();
    }
    Ok(())
}

fn collect_from_declaration(
    decl: &hir::Declaration,
    gcx: GlobalContext<'_>,
    path: &mut Vec<String>,
    inherited_tags: &[String],
    benchmarks: &mut Vec<BenchmarkCase>,
) -> crate::error::CompileResult<()> {
    let has_bench = decl
        .attributes
        .iter()
        .any(|attribute| attribute.as_known(gcx) == Some(KnownAttribute::Bench));
    let has_expect_panic = decl
        .attributes
        .iter()
        .any(|attribute| attribute.as_known(gcx) == Some(KnownAttribute::ExpectPanic));
    let declared_tags = collect_decl_tags(decl, gcx, has_bench, "bench")?;

    if has_expect_panic {
        gcx.dcx().emit_error(
            "@expectPanic is only supported by @test functions, not benchmarks".into(),
            Some(decl.span),
        );
        return Err(crate::error::ReportedError);
    }

    match &decl.kind {
        DeclarationKind::Function(function) if has_bench => {
            if function.is_async {
                gcx.dcx().emit_error(
                    "@bench functions must be synchronous".into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }
            if function.generics.type_parameters.is_some() {
                gcx.dcx().emit_error(
                    "@bench functions must not be generic".into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }
            if function.signature.prototype.output.is_some() {
                gcx.dcx()
                    .emit_error("@bench functions must return void".into(), Some(decl.span));
                return Err(crate::error::ReportedError);
            }
            if function.signature.prototype.inputs.len() != 1 {
                gcx.dcx().emit_error(
                    "@bench functions must take exactly one `&mut std.bench.Benchmark` parameter"
                        .into(),
                    Some(decl.span),
                );
                return Err(crate::error::ReportedError);
            }
            let parameter = &function.signature.prototype.inputs[0];
            if parameter.default_value.is_some() || parameter.is_variadic {
                gcx.dcx().emit_error(
                    "the @bench Benchmark parameter cannot be defaulted or variadic".into(),
                    Some(parameter.span),
                );
                return Err(crate::error::ReportedError);
            }

            let signature = gcx.get_signature(decl.id);
            let benchmark_id = gcx.std_item_def(StdItem::Benchmark);
            let correct_parameter = signature.inputs.first().is_some_and(|parameter| {
                let TyKind::Reference(inner, Mutability::Mutable) = parameter.ty.kind() else {
                    return false;
                };
                matches!(inner.kind(), TyKind::Adt(definition, args)
                    if Some(definition.id) == benchmark_id && args.is_empty())
            });
            if !correct_parameter {
                gcx.dcx().emit_error(
                    "@bench functions must take `&mut std.bench.Benchmark`".into(),
                    Some(parameter.span),
                );
                return Err(crate::error::ReportedError);
            }

            let function_name = gcx.symbol_text(decl.identifier.symbol).to_string();
            let display_name = if path.is_empty() {
                function_name
            } else {
                format!("{}::{function_name}", path.join("::"))
            };
            let mut tags = inherited_tags.to_vec();
            merge_unique_tags_case_insensitive(&mut tags, declared_tags);
            let skip_reason = decl
                .attributes
                .iter()
                .find(|attribute| attribute.as_known(gcx) == Some(KnownAttribute::Skip))
                .and_then(|attribute| attribute.first_string_arg(gcx));
            let skipped = decl
                .attributes
                .iter()
                .any(|attribute| attribute.as_known(gcx) == Some(KnownAttribute::Skip));

            benchmarks.push(BenchmarkCase {
                id: decl.id,
                display_name,
                skipped,
                skip_reason,
                tags,
            });
        }
        DeclarationKind::Namespace(namespace) => {
            let mut namespace_tags = inherited_tags.to_vec();
            merge_unique_tags_case_insensitive(&mut namespace_tags, declared_tags);
            path.push(gcx.symbol_text(decl.identifier.symbol).to_string());
            for inner in &namespace.declarations {
                collect_from_declaration(inner, gcx, path, &namespace_tags, benchmarks)?;
            }
            path.pop();
        }
        _ if has_bench => {
            gcx.dcx().emit_error(
                "@bench can only be applied to functions".into(),
                Some(decl.span),
            );
            return Err(crate::error::ReportedError);
        }
        _ => {}
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{BenchmarkCase, BenchmarkSelection, filter_benchmarks};
    use crate::{
        PackageIndex,
        sema::resolve::models::{DefinitionID, DefinitionIndex},
    };

    fn benchmark(name: &str, tags: &[&str]) -> BenchmarkCase {
        BenchmarkCase {
            id: DefinitionID::new(PackageIndex::new(0), DefinitionIndex::from_raw(0)),
            display_name: name.into(),
            skipped: false,
            skip_reason: None,
            tags: tags.iter().map(|tag| (*tag).into()).collect(),
        }
    }

    #[test]
    fn filters_names_and_tags_with_test_harness_semantics() {
        let selection = BenchmarkSelection::new(Some("json.parse".into()), vec!["SMOKE".into()]);
        assert_eq!(
            filter_benchmarks(
                vec![
                    benchmark("json::parseSmall", &["smoke"]),
                    benchmark("json::encodeSmall", &["smoke"]),
                ],
                &selection,
            )
            .len(),
            1
        );
    }
}
