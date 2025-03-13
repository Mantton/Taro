use taroc_ast::{
    BindingPattern, BindingPatternKind, DeclarationContext, ForStatement, GuardStatement, Label,
    Local, LoopStatement, Mutability, Statement, StatementConditionList, StatementKind,
    WhileStatement,
};
use taroc_token::TokenKind;

use super::{
    package::{Parser, R},
    restrictions::Restrictions,
};

impl Parser {
    pub fn parse_statement(&mut self) -> R<Statement> {
        self.consume_comments_and_new_lines();
        let lo = self.lo_span();
        let label = self.parse_label()?;
        let k = self.parse_stmt_kind(label)?;

        let stmt = Statement {
            kind: k,
            span: lo.to(self.hi_span()),
        };

        Ok(stmt)
    }

    fn parse_stmt_kind(&mut self, label: Option<Label>) -> R<StatementKind> {
        match self.current_kind() {
            TokenKind::Loop | TokenKind::While | TokenKind::For => {}
            _ => self.warn_improper_label_position(label.clone()),
        };

        match self.current_kind() {
            TokenKind::Let | TokenKind::Var => self.parse_local_statement(),
            TokenKind::Loop => self.parse_loop_stmt(label),
            TokenKind::While => self.parse_while_stmt(label),
            TokenKind::For => self.parse_for_stmt(label),
            TokenKind::Return => self.parse_return_stmt(),
            TokenKind::Break => self.parse_break_stmt(),
            TokenKind::Continue => self.parse_continue_stmt(),
            TokenKind::Defer => self.parse_defer_stmt(),
            TokenKind::Guard => self.parse_guard_stmt(),
            _ => {
                // is shorthand decl
                if let Some(kind) = self.parse_variable_shorthand()? {
                    return Ok(kind);
                }

                // is decl
                if let Some(decl) = self.parse_declaration(false, DeclarationContext::Statement)? {
                    return Ok(StatementKind::Declaration(decl));
                }

                // is expr
                let expr = self.parse_expression()?;
                self.consume_new_lines();
                return Ok(StatementKind::Expression(expr));

                // invalid stmt
                // let msg = format!("expected statement found {}", self.current_kind());
                // let span = self.current_token_span();
                // Err(SpannedMessage::new(msg, span))
            }
        }
    }

    fn warn_improper_label_position(&mut self, label: Option<Label>) {
        if let Some(label) = label {
            let msg = "cannot use label here".to_string();
            self.emit_warning(msg, label.span);
        }
    }
}

impl Parser {
    pub fn parse_local(&mut self) -> R<Local> {
        // let | var <binding_pattern> <type_annotation>? <initializer_clause>?
        // type_annotation = : <type>
        // initializer_clause: = <expr>
        let mutability = if self.eat(TokenKind::Let) {
            Mutability::Immutable
        } else if self.eat(TokenKind::Var) {
            Mutability::Mutable
        } else {
            unreachable!("expected `let` | `var` token")
        };

        let pattern = self.parse_binding_pat()?;

        let ty = if self.eat(TokenKind::Colon) {
            Some(self.parse_type()?)
        } else {
            None
        };

        let initializer = if self.eat(TokenKind::Assign) {
            Some(self.parse_expression()?)
        } else {
            None
        };

        let local = Local {
            mutability,
            pattern,
            ty,
            initializer,
            is_shorthand: false,
        };

        Ok(local)
    }
    fn parse_local_statement(&mut self) -> R<StatementKind> {
        let local = self.parse_local()?;
        self.expect_line_break_or_semi()?;
        Ok(StatementKind::Variable(local))
    }
}

impl Parser {
    fn parse_loop_stmt(&mut self, label: Option<Label>) -> R<StatementKind> {
        self.expect(TokenKind::Loop)?;
        let block = self.parse_block()?;
        let l = LoopStatement { label, block };
        Ok(StatementKind::Loop(l))
    }

    fn parse_while_stmt(&mut self, label: Option<Label>) -> R<StatementKind> {
        self.expect(TokenKind::While)?;
        let mut while_restrictions = Restrictions::empty();
        while_restrictions.set(Restrictions::ALLOW_BINDING_CONDITION, true);

        let conditions = self.with_restrictions(while_restrictions, |p| {
            p.parse_statement_condition_list(TokenKind::LBrace)
        })?;
        let block = self.parse_block()?;

        let w = WhileStatement {
            label,
            conditions,
            block,
        };

        Ok(StatementKind::While(w))
    }

    fn parse_for_stmt(&mut self, label: Option<Label>) -> R<StatementKind> {
        self.expect(TokenKind::For)?;
        let pattern = self.parse_binding_pat()?;
        self.expect(TokenKind::In)?;

        let for_restrictions = Restrictions::empty();

        let iterator = self.with_restrictions(for_restrictions, |p| p.parse_expression())?;

        let clause = if self.eat(TokenKind::Where) {
            let clause = self.with_restrictions(for_restrictions, |p| p.parse_expression())?;
            Some(clause)
        } else {
            None
        };

        let block = self.parse_block()?;

        let f = ForStatement {
            label,
            pattern,
            iterator,
            clause,
            block,
        };
        Ok(StatementKind::For(f))
    }
}

impl Parser {
    pub fn parse_statement_condition_list(&mut self, end: TokenKind) -> R<StatementConditionList> {
        let lo = self.lo_span();
        let conditions =
            self.parse_sequence_until(&[end], TokenKind::Comma, false, |p| p.parse_expression())?;
        let c = StatementConditionList {
            conditions,
            span: lo.to(self.hi_span()),
        };

        Ok(c)
    }
}

impl Parser {
    fn parse_return_stmt(&mut self) -> R<StatementKind> {
        self.expect(TokenKind::Return)?;

        let expr = if !self.matches(TokenKind::Semicolon) && !self.matches(TokenKind::RBrace) {
            Some(self.parse_expression()?)
        } else {
            None
        };

        self.expect_line_break_or_semi()?;

        Ok(StatementKind::Return(expr))
    }

    fn parse_break_stmt(&mut self) -> R<StatementKind> {
        self.expect(TokenKind::Break)?;
        let ident = self.parse_optional_ident()?;
        self.expect_line_break_or_semi()?;
        Ok(StatementKind::Break(ident))
    }

    fn parse_continue_stmt(&mut self) -> R<StatementKind> {
        self.expect(TokenKind::Continue)?;
        let ident = self.parse_optional_ident()?;
        self.expect_line_break_or_semi()?;
        Ok(StatementKind::Continue(ident))
    }

    fn parse_defer_stmt(&mut self) -> R<StatementKind> {
        self.expect(TokenKind::Defer)?;
        let block = self.parse_block()?;
        Ok(StatementKind::Defer(block))
    }

    fn parse_guard_stmt(&mut self) -> R<StatementKind> {
        self.expect(TokenKind::Guard)?;

        let mut if_restrictions = Restrictions::empty();
        if_restrictions.set(Restrictions::ALLOW_BINDING_CONDITION, true);
        let conditions = self.with_restrictions(if_restrictions, |p| {
            p.parse_statement_condition_list(TokenKind::LBrace)
        })?;

        self.expect(TokenKind::Else)?;
        let block = self.parse_block()?;
        let g = GuardStatement { conditions, block };

        Ok(StatementKind::Guard(g))
    }
}

impl Parser {
    fn parse_variable_shorthand(&mut self) -> R<Option<StatementKind>> {
        if self.matches(TokenKind::Identifier) && self.next_matches(1, TokenKind::DeclareVar) {
            let identifier = self.parse_identifier()?;
            self.expect(TokenKind::DeclareVar)?;

            let initializer = self.parse_expression()?;
            let local = Local {
                mutability: Mutability::Mutable,
                pattern: BindingPattern {
                    span: identifier.span,
                    kind: BindingPatternKind::Identifier(identifier),
                },
                ty: None,
                initializer: Some(initializer),
                is_shorthand: true,
            };

            let kind = StatementKind::Variable(local);
            self.expect_line_break_or_semi()?;
            Ok(Some(kind))
        } else {
            Ok(None)
        }
    }
}

impl Parser {
    pub fn parse_label(&mut self) -> R<Option<Label>> {
        let can_parse =
            self.matches(TokenKind::Identifier) && self.next_matches(1, TokenKind::Colon);
        if !can_parse {
            return Ok(None);
        }

        let lo = self.lo_span();

        let identifier = self.parse_identifier()?;
        self.expect(TokenKind::Colon)?;

        let label = Label {
            identifier,
            span: lo.to(self.hi_span()),
        };

        Ok(Some(label))
    }
}
