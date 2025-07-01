use super::{
    package::{Parser, R},
    restrictions::Restrictions,
};
use taroc_ast::{Pattern, PatternField, PatternKind};
use taroc_span::SpannedMessage;
use taroc_token::{Delimiter, TokenKind};

impl Parser {
    pub fn parse_match_arm_pattern(&mut self) -> R<Pattern> {
        let lo = self.lo_span();
        let cases =
            self.parse_sequence_until(&[TokenKind::EqArrow], TokenKind::Comma, false, |p| {
                p.parse_pattern()
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
        let kind = PatternKind::Or(cases, span);

        let pat = Pattern { span, kind };

        Ok(pat)
    }

    pub fn parse_pattern(&mut self) -> R<Pattern> {
        let lo = self.lo_span();
        let k = self.parse_pattern_kind()?;

        let o = Pattern {
            span: lo.to(self.hi_span()),
            kind: k,
        };

        Ok(o)
    }

    fn parse_pattern_kind(&mut self) -> R<PatternKind> {
        match self.current_kind() {
            TokenKind::LParen => self.parse_pattern_tuple_kind(),
            TokenKind::Underscore => {
                self.bump();
                Ok(PatternKind::Wildcard)
            }
            TokenKind::DotDot => {
                if !self.restrictions.contains(Restrictions::ALLOW_REST_PATTERN) {
                    self.emit_error(
                        "'..'/rest patterns are not allowed here".into(),
                        self.current_token_span(),
                    );
                }
                self.bump();
                Ok(PatternKind::Rest)
            }
            TokenKind::Var | TokenKind::Identifier => self.parse_pattern_path_kind(),
            _ => {
                let ac = self.parse_anon_const()?;
                Ok(PatternKind::Literal(ac))
            }
        }
    }

    fn parse_pattern_tuple_kind(&mut self) -> R<PatternKind> {
        let lo = self.lo_span();
        let pats =
            self.parse_delimiter_sequence(Delimiter::Parenthesis, TokenKind::Comma, true, |p| {
                p.parse_pattern()
            })?;
        Ok(PatternKind::Tuple(pats, lo.to(self.hi_span())))
    }

    fn parse_pattern_path_kind(&mut self) -> R<PatternKind> {
        // Cannot Possibly be a path pattern
        if (self.matches(TokenKind::Identifier) | self.matches(TokenKind::Var))
            && !(self.next_matches(1, TokenKind::LChevron)
                | self.next_matches(1, TokenKind::Scope)
                | self.next_matches(1, TokenKind::LBrace)
                | self.next_matches(1, TokenKind::LParen))
        {
            let ident = self.parse_identifier()?;
            return Ok(PatternKind::Identifier(ident));
        }

        let path = self.parse_path()?;

        match self.current_kind() {
            TokenKind::LParen => {
                // Path-Tuple Kind
                // Foo::Bar (a, b)
                let lo = self.lo_span();

                let mut res = Restrictions::empty();
                res.insert(Restrictions::ALLOW_REST_PATTERN);
                let items = self.with_restrictions(res, |p| {
                    p.parse_delimiter_sequence(
                        Delimiter::Parenthesis,
                        TokenKind::Comma,
                        false,
                        |p| p.parse_pattern(),
                    )
                })?;

                Ok(PatternKind::PathTuple(path, items, lo.to(self.hi_span())))
            }
            TokenKind::LBrace => {
                // Path-Struct Kind
                let lo = self.lo_span();
                let (items, ignore_rest) = self.parse_pattern_fields()?;
                let span = lo.to(self.hi_span());
                let k = PatternKind::PathStruct(path, items, span, ignore_rest);
                Ok(k)
            }
            _ => Ok(PatternKind::Path(path)),
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
            self.parse_pattern()?
        } else {
            Pattern {
                span: identifier.span,
                kind: PatternKind::Identifier(identifier),
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
