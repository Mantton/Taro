//! Unused `Result` values.
//!
//! An expression whose value is thrown away and whose type is std's `Result`
//! (found through the `Result` language item, so aliases count) silently
//! drops an error. This pass warns about it unless the author handles the
//! value, propagates it with `!`, binds it to `_`, or calls a function marked
//! `@discardableResult`. It also checks that `@discardableResult` is only
//! written on functions that return a `Result`.
//!
//! A value is thrown away when it is an expression statement, the tail of a
//! block whose value is itself thrown away, or the tail of a body whose
//! destination is unit (a unit function, a loop, `defer`, a `guard` else).
//! Each such position is examined once, so every dropped value warns once.

use crate::{
    compile::context::GlobalContext,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor, KnownAttribute, Resolution},
    sema::{
        models::{Ty, TyKind},
        tycheck::results::TypeCheckResults,
    },
    span::Span,
};

pub fn run<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
    results: &TypeCheckResults<'ctx>,
) {
    let mut actor = Actor {
        gcx,
        results,
        warn: gcx.config.lint_warnings,
    };
    hir::walk_package(&mut actor, package);
}

/// Whether `id` carries `@discardableResult`. Attributes travel through
/// package metadata, so this also answers for definitions in dependencies.
pub fn is_discardable(gcx: GlobalContext<'_>, id: DefinitionID) -> bool {
    gcx.attributes_of(id)
        .iter()
        .any(|attribute| attribute.as_known(gcx) == Some(KnownAttribute::DiscardableResult))
}

pub fn unused_result_message<'ctx>(gcx: GlobalContext<'ctx>, ty: Ty<'ctx>) -> String {
    format!(
        "unused '{}'; handle it, propagate it with `!`, or discard it with `_ = ...`",
        ty.format(gcx)
    )
}

struct Actor<'ctx, 'results> {
    gcx: GlobalContext<'ctx>,
    results: &'results TypeCheckResults<'ctx>,
    /// Lints report only for the package being compiled, never a dependency.
    warn: bool,
}

impl<'ctx> Actor<'ctx, '_> {
    fn validate_attribute(&self, id: DefinitionID, attributes: &hir::AttributeList) {
        let Some(attribute) = attributes.iter().find(|attribute| {
            attribute.as_known(self.gcx) == Some(KnownAttribute::DiscardableResult)
        }) else {
            return;
        };
        let output = self.gcx.function_body_output(id);
        if output.is_error() || self.gcx.result_parts(output).is_some() {
            return;
        }
        self.gcx.dcx().emit_error(
            format!(
                "@discardableResult requires a function that returns 'Result'; '{}' returns '{}'",
                self.gcx.symbol_text(self.gcx.definition_ident(id).symbol),
                output.format(self.gcx)
            ),
            Some(attribute.span),
        );
    }

    /// `expression`'s value is thrown away.
    fn discarded(&self, expression: &hir::Expression) {
        if !self.warn {
            return;
        }
        match &expression.kind {
            // A block's value is its tail; point at the tail itself.
            hir::ExpressionKind::Block(block) | hir::ExpressionKind::UnsafeBlock(block) => {
                self.discarded_tail(block);
                return;
            }
            // Lowering-made matches (`for`, optional chaining) have no source
            // of their own; their arms carry the user's expressions.
            hir::ExpressionKind::Match(node) if node.source.desugared => {
                for arm in &node.arms {
                    self.discarded(&arm.body);
                }
                return;
            }
            _ => {}
        }

        let Some(ty) = self.results.try_node_type(expression.id) else {
            return;
        };
        if ty.is_error() {
            return;
        }
        if self.gcx.result_parts(ty).is_some() {
            // When every other branch diverges, the one live branch is the
            // dropped value; point there. This also keeps a `while` body's
            // warning off the loop that lowering wrapped around it.
            if let Some(branch) = self.sole_live_branch(expression) {
                self.discarded(branch);
            } else if !self.is_discardable_call(expression) {
                self.warn_unused(ty, expression.span);
            }
            return;
        }

        // A unit `if` or `match` may still drop a `Result` in one branch,
        // for example the body of a `while` loop.
        match &expression.kind {
            hir::ExpressionKind::If(node) => {
                self.discarded(&node.then_block);
                if let Some(else_block) = &node.else_block {
                    self.discarded(else_block);
                }
            }
            hir::ExpressionKind::Match(node) => {
                for arm in &node.arms {
                    self.discarded(&arm.body);
                }
            }
            _ => {}
        }
    }

    /// The only branch of an `if` or `match` that does not diverge.
    fn sole_live_branch<'e>(&self, expression: &'e hir::Expression) -> Option<&'e hir::Expression> {
        let branches: Vec<&hir::Expression> = match &expression.kind {
            hir::ExpressionKind::If(node) => std::iter::once(&*node.then_block)
                .chain(node.else_block.as_deref())
                .collect(),
            hir::ExpressionKind::Match(node) => node.arms.iter().map(|arm| &*arm.body).collect(),
            _ => return None,
        };
        let mut live = branches.into_iter().filter(|branch| {
            !self
                .results
                .try_node_type(branch.id)
                .is_some_and(|ty| matches!(ty.kind(), TyKind::Never))
        });
        let branch = live.next()?;
        live.next().is_none().then_some(branch)
    }

    fn discarded_tail(&self, block: &hir::Block) {
        if let Some(tail) = block.tail.as_deref() {
            self.discarded(tail);
        }
    }

    fn warn_unused(&self, ty: Ty<'ctx>, span: Span) {
        let ty = crate::sema::tycheck::utils::normalize_aliases(self.gcx, ty);
        self.gcx
            .dcx()
            .emit_warning(unused_result_message(self.gcx, ty), Some(span));
    }

    fn is_discardable_call(&self, expression: &hir::Expression) -> bool {
        match &expression.kind {
            hir::ExpressionKind::Await(inner) => self.is_discardable_call(inner),
            hir::ExpressionKind::MethodCall { .. } => self
                .results
                .overload_source(expression.id)
                .is_some_and(|id| is_discardable(self.gcx, id)),
            hir::ExpressionKind::Call { callee, .. } => self
                .results
                .overload_source(expression.id)
                .or_else(|| self.callee_definition(callee))
                .is_some_and(|id| is_discardable(self.gcx, id)),
            _ => false,
        }
    }

    fn callee_definition(&self, callee: &hir::Expression) -> Option<DefinitionID> {
        if let Some(id) = self.results.overload_source(callee.id) {
            return Some(id);
        }
        let resolution = match (self.results.value_resolution(callee.id), &callee.kind) {
            (Some(resolution), _) => resolution,
            (None, hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))) => {
                path.resolution.clone()
            }
            _ => return None,
        };
        match resolution {
            Resolution::Definition(
                id,
                DefinitionKind::Function | DefinitionKind::AssociatedFunction,
            ) => Some(id),
            _ => None,
        }
    }
}

impl<'ctx> HirVisitor for Actor<'ctx, '_> {
    fn visit_declaration(&mut self, node: &hir::Declaration) -> Self::Result {
        if matches!(node.kind, hir::DeclarationKind::Function(_)) {
            self.validate_attribute(node.id, &node.attributes);
        }
        hir::walk_declaration(self, node)
    }

    fn visit_assoc_declaration(
        &mut self,
        node: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) -> Self::Result {
        if matches!(node.kind, hir::AssociatedDeclarationKind::Function(_)) {
            self.validate_attribute(node.id, &node.attributes);
        }
        hir::walk_assoc_declaration(self, node, context)
    }

    fn visit_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        context: hir::FunctionContext,
    ) -> Self::Result {
        // Mirrors the checker: a unit body evaluates and discards its tail.
        if let Some(body) = &node.block {
            let unit_body = matches!(context, hir::FunctionContext::Initializer(_))
                || self.gcx.function_body_output(id) == self.gcx.types.void;
            if unit_body {
                self.discarded_tail(body);
            }
        }
        hir::walk_function(self, id, node, context)
    }

    fn visit_statement(&mut self, node: &hir::Statement) -> Self::Result {
        match &node.kind {
            hir::StatementKind::Expression(expression) => self.discarded(expression),
            hir::StatementKind::Loop { block, .. } | hir::StatementKind::Defer(_, block) => {
                self.discarded_tail(block)
            }
            hir::StatementKind::Guard { else_block, .. } => self.discarded_tail(else_block),
            hir::StatementKind::Declaration(_) | hir::StatementKind::Variable(_) => {}
            hir::StatementKind::ComptimeFor { .. } | hir::StatementKind::ComptimeIf { .. } => {
                if let Some(blocks) = self.results.comptime_expansions.get(&node.id) {
                    for block in blocks {
                        self.discarded_tail(block);
                        hir::walk_block(self, block);
                    }
                }
                return;
            }
        }
        hir::walk_statement(self, node)
    }

    fn visit_expression(&mut self, node: &hir::Expression) -> Self::Result {
        if let hir::ExpressionKind::Loop { block, .. } = &node.kind {
            self.discarded_tail(block);
        }
        hir::walk_expression(self, node)
    }
}

#[cfg(test)]
mod tests {
    use crate::{diagnostics::Diagnostic, hir::StdItem};

    const PRELUDE: &str = r#"
enum Result[T, E] {
    case ok(T)
    case err(E)
}
type Outcome = Result[int32, string]
func fails() -> Result[int32, string] { .ok(1) }
func aliased() -> Outcome { .ok(2) }
@discardableResult
func quiet() -> Result[int32, string] { .ok(3) }
struct Probe {}
extend Probe {
    func check() -> Result[int32, string] { .ok(4) }
    @discardableResult
    func log() -> Result[int32, string] { .ok(5) }
}
"#;

    fn diagnostics(body: &str) -> Vec<Diagnostic> {
        crate::test_support::with_lint_warnings(|| {
            crate::test_support::analyze_language_item_script(
                &format!("{PRELUDE}{body}"),
                false,
                &[(StdItem::Result, "Result")],
            )
        })
    }

    fn unused(diagnostics: &[Diagnostic]) -> usize {
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.message.starts_with("unused 'Result["))
            .count()
    }

    #[test]
    fn dropped_results_warn_once_per_statement() {
        let diagnostics = diagnostics(
            r#"
func main() {
    fails()
    aliased()
    Probe {}.check()
    if true { fails() } else { fails() }
    loop { fails(); break }
    tail()
}
func tail() {
    fails()
}
"#,
        );
        assert_eq!(unused(&diagnostics), 6, "{diagnostics:#?}");
        assert_eq!(diagnostics.len(), 6, "{diagnostics:#?}");
        assert!(
            diagnostics.iter().all(|diagnostic| diagnostic.message
                == "unused 'Result[int32, string]'; handle it, propagate it with `!`, or discard it with `_ = ...`"),
            "{diagnostics:#?}"
        );
    }

    #[test]
    fn consumed_discarded_and_discardable_results_are_silent() {
        let diagnostics = diagnostics(
            r#"
func main() {
    _ = fails()
    var _ = fails()
    _ := fails()
    match fails() {
        case .ok(_) => {}
        case .err(_) => {}
    }
    var _value = { fails() }
    quiet()
    Probe {}.log()
}
func forward() -> Result[int32, string] {
    var _value = fails()!
    return fails()
}
func tail() -> Result[int32, string] {
    fails()
}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }

    #[test]
    fn discardable_result_requires_a_result_return() {
        let diagnostics = diagnostics(
            r#"
@discardableResult
func count() -> int32 { 1 }
func main() {}
"#,
        );
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(
            diagnostics[0].message,
            "@discardableResult requires a function that returns 'Result'; 'count' returns 'int32'"
        );
    }
}
