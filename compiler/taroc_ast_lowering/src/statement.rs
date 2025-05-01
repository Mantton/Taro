use super::package::Actor;

impl Actor<'_> {
    pub fn lower_statement(&mut self, statement: taroc_ast::Statement) -> taroc_hir::Statement {
        taroc_hir::Statement {
            id: self.next(),
            kind: self.lower_statement_kind(statement.kind),
            span: statement.span,
        }
    }

    fn lower_statement_kind(&mut self, kind: taroc_ast::StatementKind) -> taroc_hir::StatementKind {
        match kind {
            taroc_ast::StatementKind::Declaration(declaration) => {
                taroc_hir::StatementKind::Declaration(self.lower_declaration(declaration))
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
            taroc_ast::StatementKind::While(..) => todo!(),
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
