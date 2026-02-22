use crate::{
    compile::context::GlobalContext,
    hir::{self, DeclarationKind, KnownAttribute},
};

/// Metadata for a single discovered test function.
#[derive(Debug, Clone)]
pub struct TestCase {
    /// DefinitionID of the test function
    pub id: hir::DefinitionID,
    /// Display name for test output (e.g., "module::test_name")
    pub display_name: String,
    /// Whether this test is marked `@skip`
    pub skipped: bool,
    /// Reason string from `@skip("reason")`, if any
    pub skip_reason: Option<String>,
    /// Whether this test is marked `@expectPanic`
    pub expect_panic: bool,
    /// Expected panic message from `@expectPanic("message")`, if any
    pub expected_panic_message: Option<String>,
}

/// Walk the HIR package and collect all `@test`-annotated functions.
/// Validates that test functions have `() -> void` signatures.
pub fn collect_tests(
    package: &hir::Package,
    gcx: GlobalContext<'_>,
) -> crate::error::CompileResult<Vec<TestCase>> {
    let mut tests = Vec::new();
    let mut path = Vec::new();
    collect_from_module(&package.root, gcx, &mut path, &mut tests)?;
    Ok(tests)
}

fn collect_from_module(
    module: &hir::Module,
    gcx: GlobalContext<'_>,
    path: &mut Vec<String>,
    tests: &mut Vec<TestCase>,
) -> crate::error::CompileResult<()> {
    for decl in &module.declarations {
        collect_from_declaration(decl, gcx, path, tests)?;
    }
    for sub in &module.submodules {
        let name = gcx.symbol_text(sub.name.clone()).to_string();
        path.push(name);
        collect_from_module(sub, gcx, path, tests)?;
        path.pop();
    }
    Ok(())
}

fn collect_from_declaration(
    decl: &hir::Declaration,
    gcx: GlobalContext<'_>,
    path: &mut Vec<String>,
    tests: &mut Vec<TestCase>,
) -> crate::error::CompileResult<()> {
    let has_test = decl
        .attributes
        .iter()
        .any(|a| a.as_known(gcx) == Some(KnownAttribute::Test));

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

            let fn_name = gcx.symbol_text(decl.identifier.symbol.clone()).to_string();
            let display_name = if path.is_empty() {
                fn_name
            } else {
                format!("{}::{}", path.join("::"), fn_name)
            };

            let mut skipped = false;
            let mut skip_reason = None;
            let mut expect_panic = false;
            let mut expected_panic_message = None;

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
                skipped,
                skip_reason,
                expect_panic,
                expected_panic_message,
            });
        }
        DeclarationKind::Namespace(ns) => {
            // Recurse into namespaces for hierarchical test naming
            let ns_name = gcx.symbol_text(decl.identifier.symbol.clone()).to_string();
            path.push(ns_name);
            for inner_decl in &ns.declarations {
                collect_from_declaration(inner_decl, gcx, path, tests)?;
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
