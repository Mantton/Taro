use taroc_span::Span;

use super::package::Actor;

impl Actor<'_> {
    pub fn lower_statement(&mut self, statement: taroc_ast::Statement) -> taroc_hir::Statement {
        taroc_hir::Statement {
            id: self.next(),
            kind: self.lower_statement_kind(statement.kind, statement.span),
            span: statement.span,
        }
    }

    fn lower_statement_kind(
        &mut self,
        kind: taroc_ast::StatementKind,
        span: Span,
    ) -> taroc_hir::StatementKind {
        match kind {
            taroc_ast::StatementKind::Declaration(declaration) => {
                taroc_hir::StatementKind::Declaration(self.lower_function_declaration(declaration))
            }
            taroc_ast::StatementKind::Expression(expression) => {
                taroc_hir::StatementKind::Expression(self.lower_expression(expression))
            }
            taroc_ast::StatementKind::Variable(local) => {
                taroc_hir::StatementKind::Variable(self.lower_local(local))
            }
            taroc_ast::StatementKind::Break(identifier) => {
                taroc_hir::StatementKind::Break(identifier.clone())
            }
            taroc_ast::StatementKind::Continue(identifier) => {
                taroc_hir::StatementKind::Continue(identifier.clone())
            }
            taroc_ast::StatementKind::Return(expression) => taroc_hir::StatementKind::Return(
                self.lower_optional(expression, |a, e| a.lower_expression(e)),
            ),
            taroc_ast::StatementKind::Loop(s) => taroc_hir::StatementKind::Loop(
                self.lower_optional(s.label, |a, x| a.lower_label(x)),
                self.lower_block(s.block),
            ),
            taroc_ast::StatementKind::While(node) => self.lower_while_statement(node, span),
            taroc_ast::StatementKind::For(..) => todo!(),
            taroc_ast::StatementKind::Defer(..) => todo!(),
            taroc_ast::StatementKind::Guard(..) => todo!(),
        }
    }
}

impl Actor<'_> {
    pub fn lower_block(&mut self, b: taroc_ast::Block) -> taroc_hir::Block {
        taroc_hir::Block {
            id: self.next(),
            statements: self.lower_sequence(b.statements, |a, s| a.lower_statement(s)),
            has_declarations: b.has_declarations,
            span: b.span,
        }
    }
}

impl Actor<'_> {
    fn lower_while_statement(
        &mut self,
        node: taroc_ast::WhileStatement,
        span: Span,
    ) -> taroc_hir::StatementKind {
        /*
            --- ast ---
            while foo { ... }

            --- hir ---
            loop {
                if foo {...}
            }
        */
        let block_span = node.block.span;
        // - Create if node
        let if_node = taroc_hir::IfExpression {
            condition: self.lower_statement_conditions(node.conditions),
            then_block: self.lower_block_to_expression(node.block),
            else_block: None,
        };

        // - create if expression
        let expr = taroc_hir::Expression {
            id: self.next(),
            kind: taroc_hir::ExpressionKind::If(if_node),
            span,
        };
        let expr = Box::new(expr);
        let loop_stmts = vec![self.mk_statement(taroc_hir::StatementKind::Expression(expr), span)];

        // - create loop statement
        let kind = taroc_hir::StatementKind::Loop(
            self.lower_optional(node.label, |this, label| this.lower_label(label)),
            self.mk_block(loop_stmts, block_span),
        );

        kind
    }
}

impl Actor<'_> {
    pub fn mk_statement(
        &mut self,
        kind: taroc_hir::StatementKind,
        span: Span,
    ) -> taroc_hir::Statement {
        taroc_hir::Statement {
            id: self.next(),
            kind,
            span,
        }
    }

    pub fn mk_block(
        &mut self,
        statements: Vec<taroc_hir::Statement>,
        span: Span,
    ) -> taroc_hir::Block {
        let has_declarations = statements
            .iter()
            .any(|f| matches!(f.kind, taroc_hir::StatementKind::Declaration(..)));
        taroc_hir::Block {
            id: self.next(),
            statements,
            has_declarations,
            span,
        }
    }
}
