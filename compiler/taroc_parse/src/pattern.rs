use super::{
    package::{Parser, R},
    restrictions::Restrictions,
};
use taroc_ast::{
    BindingMode, BindingPattern, BindingPatternKind, MatchingPattern, MatchingPatternKind,
    Mutability, PatternField,
};
use taroc_span::SpannedMessage;
use taroc_token::{Delimiter, TokenKind};

impl Parser {
    pub fn parse_binding_pat(&mut self) -> R<BindingPattern> {
        if self.matches(TokenKind::Identifier) {
            let lo = self.lo_span();
            let ident = self.parse_identifier()?;
            let kind = BindingPatternKind::Identifier(ident);
            return Ok(BindingPattern {
                span: lo.to(self.hi_span()),
                kind,
            });
        } else if self.matches(TokenKind::LParen) {
            let lo = self.lo_span();
            let items = self.parse_delimiter_sequence(
                Delimiter::Parenthesis,
                TokenKind::Comma,
                false,
                |p| p.parse_binding_pat(),
            )?;
            let kind = BindingPatternKind::Tuple(items);
            return Ok(BindingPattern {
                span: lo.to(self.hi_span()),
                kind,
            });
        } else if self.eat(TokenKind::Underscore) {
            let span = self.previous().unwrap().span;
            let kind = BindingPatternKind::Wildcard;
            return Ok(BindingPattern { span, kind });
        } else {
            let msg = format!("expected binding pattern, got {}", self.current_kind());
            let err = SpannedMessage::new(msg, self.current_token_span());
            return Err(err);
        }
    }
}

impl Parser {
    pub fn parse_match_case_pat(&mut self) -> R<MatchingPattern> {
        let lo = self.lo_span();
        let cases =
            self.parse_sequence_until(&[TokenKind::EqArrow], TokenKind::Bar, false, |p| {
                p.parse_match_pat()
            })?;

        if cases.is_empty() {
            let msg = format!("expected matching pattern, got {}", self.current_kind());
            let err = SpannedMessage::new(msg, self.current_token_span());
            return Err(err);
        }

        // has one pattern
        if cases.len() == 1 {
            return Ok(cases.into_iter().next().unwrap());
        }

        // has multiple patterns is an or pattern
        let span = lo.to(self.hi_span());
        let kind = MatchingPatternKind::Or(cases, span);

        let pat = MatchingPattern { span, kind };

        Ok(pat)
    }

    pub fn parse_match_pat(&mut self) -> R<MatchingPattern> {
        let lo = self.lo_span();
        let k = self.parse_match_pat_kind()?;

        let o = MatchingPattern {
            span: lo.to(self.hi_span()),
            kind: k,
        };

        Ok(o)
    }

    fn parse_match_pat_kind(&mut self) -> R<MatchingPatternKind> {
        match self.current_kind() {
            TokenKind::LParen => self.parse_match_tuple_kind(),
            TokenKind::Underscore => {
                self.bump();
                Ok(MatchingPatternKind::Wildcard)
            }
            TokenKind::DotDot => {
                if !self.restrictions.contains(Restrictions::ALLOW_REST_PATTERN) {
                    self.emit_error(
                        "'..'/rest patterns are not allowed here".into(),
                        self.current_token_span(),
                    );
                }
                self.bump();
                Ok(MatchingPatternKind::Rest)
            }
            TokenKind::Var | TokenKind::Identifier => self.parse_match_path_kind(),
            _ => {
                let ac = self.parse_anon_const()?;
                Ok(MatchingPatternKind::Literal(ac))
            }
        }
    }

    fn parse_match_tuple_kind(&mut self) -> R<MatchingPatternKind> {
        let lo = self.lo_span();
        let pats =
            self.parse_delimiter_sequence(Delimiter::Parenthesis, TokenKind::Comma, true, |p| {
                p.parse_match_pat()
            })?;
        Ok(MatchingPatternKind::Tuple(pats, lo.to(self.hi_span())))
    }

    fn parse_match_path_kind(&mut self) -> R<MatchingPatternKind> {
        // Cannot Possibly be a path pattern
        if (self.matches(TokenKind::Identifier) | self.matches(TokenKind::Var))
            && !(self.next_matches(1, TokenKind::LChevron)
                | self.next_matches(1, TokenKind::Scope)
                | self.next_matches(1, TokenKind::LBrace)
                | self.next_matches(1, TokenKind::LParen))
        {
            let mode = BindingMode(if self.eat(TokenKind::Var) {
                Mutability::Mutable
            } else {
                Mutability::Immutable
            });
            let ident = self.parse_identifier()?;
            return Ok(MatchingPatternKind::Binding(mode, ident));
        }

        let path = self.parse_path()?;

        match self.current_kind() {
            TokenKind::LParen => {
                // Path-Tuple Kind
                // Foo::Bar (a, b) | Foo::Bar(label: value)
                let lo = self.lo_span();

                let mut res = Restrictions::empty();
                res.insert(Restrictions::ALLOW_REST_PATTERN);
                let items = self.with_restrictions(res, |p| {
                    p.parse_delimiter_sequence(
                        Delimiter::Parenthesis,
                        TokenKind::Comma,
                        false,
                        |p| p.parse_match_pat(),
                    )
                })?;

                Ok(MatchingPatternKind::PathTuple(
                    path,
                    items,
                    lo.to(self.hi_span()),
                ))
            }
            TokenKind::LBrace => {
                // Path-Struct Kind
                let lo = self.lo_span();
                let (items, ignore_rest) = self.parse_pattern_fields()?;
                let span = lo.to(self.hi_span());
                let k = MatchingPatternKind::PathStruct(path, items, span, ignore_rest);
                Ok(k)
            }
            _ => Ok(MatchingPatternKind::Path(path)),
        }
    }
}

impl Parser {
    fn parse_pattern_fields(&mut self) -> R<(Vec<PatternField>, bool)> {
        self.expect(TokenKind::LBrace)?;

        let fields = self.parse_sequence_until(
            &[TokenKind::DotDot, TokenKind::LBrace],
            TokenKind::Comma,
            true,
            |p| p.parse_pattern_field(),
        )?;

        let ignore_rest = self.eat(TokenKind::DotDot);
        self.eat(TokenKind::Comma); // Might Have a trailing comma after ..
        self.expect(TokenKind::RBrace)?;
        return Ok((fields, ignore_rest));
    }

    fn parse_pattern_field(&mut self) -> R<PatternField> {
        let lo = self.lo_span();

        let identifier = self.parse_identifier()?;
        let pattern = if self.eat(TokenKind::Colon) {
            self.parse_match_pat()?
        } else {
            // Defualt to Ident Pattern
            MatchingPattern {
                span: identifier.span,
                kind: MatchingPatternKind::Binding(BindingMode(Mutability::Immutable), identifier),
            }
        };

        let field = PatternField {
            identifier,
            pattern,
            span: lo.to(self.hi_span()),
        };

        Ok(field)
    }
}
