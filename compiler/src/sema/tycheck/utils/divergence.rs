//! A narrow syntactic divergence fact used before THIR control-flow analysis.
//! An unconditional loop without a break targeting it cannot produce unit.
use crate::{
    hir::{self, HirVisitor},
    span::Symbol,
};

pub(crate) fn ends_in_unbroken_loop(block: &hir::Block) -> bool {
    let (label, block) = match (block.tail.as_deref(), block.statements.last()) {
        (
            Some(hir::Expression {
                kind: hir::ExpressionKind::Loop { label, block },
                ..
            }),
            _,
        ) => (label, block),
        (
            None,
            Some(hir::Statement {
                kind: hir::StatementKind::Loop { label, block },
                ..
            }),
        ) => (label, block),
        _ => return false,
    };
    struct Exits {
        labels: Vec<Option<Symbol>>,
        found: bool,
    }
    impl HirVisitor for Exits {
        fn visit_statement(&mut self, statement: &hir::Statement) {
            if self.found {
                return;
            }
            match &statement.kind {
                hir::StatementKind::Loop { label, block } => {
                    self.labels.push(label.map(|label| label.identifier.symbol));
                    hir::walk_block(self, block);
                    self.labels.pop();
                }
                // A nested function cannot break this function's loop.
                hir::StatementKind::Declaration(_) => {}
                _ => hir::walk_statement(self, statement),
            }
        }
        fn visit_expression(&mut self, expression: &hir::Expression) {
            if self.found {
                return;
            }
            match &expression.kind {
                hir::ExpressionKind::Loop { label, block } => {
                    self.labels.push(label.map(|label| label.identifier.symbol));
                    hir::walk_block(self, block);
                    self.labels.pop();
                }
                hir::ExpressionKind::Break { label, .. } => {
                    self.found = match label {
                        None => self.labels.len() == 1,
                        Some(label) => {
                            self.labels
                                .iter()
                                .rposition(|entry| *entry == Some(label.symbol))
                                == Some(0)
                        }
                    };
                }
                hir::ExpressionKind::Closure(_) => {}
                _ => hir::walk_expression(self, expression),
            }
        }
    }
    let mut exits = Exits {
        labels: vec![label.map(|label| label.identifier.symbol)],
        found: false,
    };
    hir::walk_block(&mut exits, block);
    !exits.found
}

#[cfg(test)]
mod tests {
    #[test]
    fn only_breaks_targeting_the_terminal_loop_allow_fallthrough() {
        for (body, allowed) in [
            ("loop { return 7 }", true),
            ("loop { loop { break } }", true),
            ("outer: loop { inner: loop { break inner } }", true),
            ("loop { break }", false),
            ("outer: loop { loop { break outer } }", false),
        ] {
            let source = format!(
                "func select(_ flag: bool) -> int32 {{ var other: int32 = 9; if flag {{ {body} }} else {{ other }} }}\nfunc main() {{}}"
            );
            let errors = crate::test_support::analyze_script_mir_diagnostics(&source);
            assert_eq!(errors.is_empty(), allowed, "{body}\n{errors:#?}");
            assert!(
                errors
                    .iter()
                    .all(|error| !error.message.contains("internal error")),
                "{errors:#?}"
            );
        }
    }
}
