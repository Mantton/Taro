use taroc_ast::Mutability;
use taroc_error::{CompileError, CompileResult};
use taroc_span::{Span, SpannedMessage, Symbol, with_session_globals};
use taroc_token::{Token, TokenKind};

use super::package::{Parser, R};

impl Parser {
    pub fn current(&self) -> Option<Token> {
        if self.cursor >= self.file.tokens.len() {
            return None;
        }

        Some(self.file.tokens[self.cursor].clone())
    }

    pub fn previous(&self) -> Option<Token> {
        if self.cursor == 0 {
            return self.current();
        }

        if self.cursor - 1 >= self.file.tokens.len() {
            return None;
        }

        Some(self.file.tokens[self.cursor - 1].clone())
    }

    pub(crate) fn current_kind(&self) -> TokenKind {
        if let Some(token) = self.current() {
            return token.kind.clone();
        }

        TokenKind::Eof
    }

    pub(crate) fn current_content(&self) -> String {
        if let Some(token) = self.current() {
            return self.read_span(token.span).unwrap_or("_err__".into());
        }

        "end-of-file".into()
    }

    pub(crate) fn current_token_span(&self) -> Span {
        if let Some(token) = self.current() {
            return token.span.clone();
        }

        Span::empty(self.file.file)
    }

    pub(crate) fn is_at_end(&self) -> bool {
        self.cursor >= self.file.tokens.len() - 1
    }

    pub fn bump(&mut self) {
        self.cursor += 1;
    }

    pub fn next(&mut self, index: usize) -> Option<&Token> {
        let k = self.cursor + index;
        if k >= self.file.tokens.len() {
            return None;
        }

        return Some(&self.file.tokens[k]);
    }

    pub fn next_matches(&mut self, index: usize, kind: TokenKind) -> bool {
        let Some(tok) = self.next(index) else {
            return false;
        };

        tok.kind == kind
    }

    pub(crate) fn eat(&mut self, kind: TokenKind) -> bool {
        if self.matches(kind) {
            self.bump();
            return true;
        }

        false
    }

    pub fn expect(&mut self, kind: TokenKind) -> R<()> {
        if self.eat(kind.clone()) {
            Ok(())
        } else {
            let msg = format!(
                "expected '{}',  got '{}' instead",
                kind,
                self.current_kind()
            );
            let err = SpannedMessage::new(msg, self.current_token_span());
            Err(err)
        }
    }

    pub fn matches(&self, kind: TokenKind) -> bool {
        self.current_kind() == kind
    }

    pub fn matches_any(&self, kinds: &[TokenKind]) -> bool {
        for kind in kinds {
            if self.matches(*kind) {
                return true;
            }
        }

        return false;
    }

    pub fn consume_comments_and_new_lines(&mut self) {
        loop {
            let kind = self.current_kind();

            match kind {
                TokenKind::MultiLineComment | TokenKind::SingleLineComment | TokenKind::Newline => {
                    self.bump()
                }
                _ => break,
            }
        }
    }

    pub fn consume_new_lines(&mut self) {
        loop {
            let kind = self.current_kind();

            match kind {
                TokenKind::Newline | TokenKind::Semicolon => self.bump(),
                _ => break,
            }
        }
    }

    pub fn expect_line_break_or_semi(&mut self) -> R<()> {
        if self.eat(TokenKind::Newline) {
            return Ok(());
        }

        if self.eat(TokenKind::Semicolon) {
            self.result.warn(SpannedMessage::new(
                "redundant semi-colon".into(),
                self.previous().unwrap().span,
            ));
            return Ok(());
        }

        let current = self.current_token_span();
        self.consume_comments_and_new_lines();
        if current != self.current_token_span() {
            return Ok(());
        }

        return Err(SpannedMessage::new(
            "expected line-break".into(),
            self.previous().unwrap().span,
        ));
    }
}

impl Parser {
    pub fn parse_string_content(&mut self) -> R<Symbol> {
        self.expect(TokenKind::String)?;
        let prev = self.previous().unwrap();
        let content = prev.content;
        let s = self.symbol_from(content)?;
        Ok(s)
    }
}

impl Parser {
    pub fn drop_anchor(&mut self) {
        self.anchors.push_back(self.cursor);
    }

    pub fn raise_anchor(&mut self) {
        let v = self.anchors.pop_back();
        if let Some(v) = v {
            self.cursor = v;
        }
    }

    pub fn _with_anchor<T, F>(&mut self, mut action: F) -> T
    where
        F: FnMut(&mut Parser) -> T,
    {
        self.drop_anchor();
        let result = action(self);
        self.raise_anchor();
        result
    }
}

impl Parser {
    pub fn emit_warning(&mut self, msg: String, span: Span) {
        self.result.warn(SpannedMessage::new(msg, span));
    }

    pub fn emit_error(&mut self, msg: String, span: Span) {
        self.result.error(SpannedMessage::new(msg, span));
    }
}

impl Parser {
    pub fn read_span(&self, span: Span) -> CompileResult<String> {
        with_session_globals(|session| {
            let file = session.get_file(self.file.file);
            let body = file.body()?;
            let source_count = body.characters.len();
            let start_line_index = body
                .lines
                .get(span.start.line)
                .cloned()
                .unwrap_or(source_count); // fallback if line is out of range
            let end_line_index = body
                .lines
                .get(span.end.line)
                .cloned()
                .unwrap_or(source_count);

            // Compute absolute indices.
            // Also ensure we don’t exceed the length of `content`.
            let abs_start = start_line_index.saturating_add(span.start.offset);
            let abs_end = end_line_index.saturating_add(span.end.offset);

            let abs_start = abs_start.min(source_count);
            let abs_end = abs_end.min(source_count);

            // 3) Slice the characters and collect into a String.
            let string = if abs_start < abs_end {
                body.characters[abs_start..abs_end].iter().collect()
            } else {
                String::new()
            };

            Ok(string)
        })
    }
    pub fn symbol_from(&self, span: Span) -> R<Symbol> {
        match self.read_span(span) {
            Ok(content) => {
                let content = content;
                let symbol = Symbol::with(&content);
                // println!("'{}' -- '{}'", content, symbol);
                return Ok(symbol);
            }
            Err(err) => match err {
                CompileError::Message(msg) => return Err(SpannedMessage::new(msg, span)),
                CompileError::Reported => {
                    return Err(SpannedMessage::new("failed to read file body".into(), span));
                }
            },
        }
    }

    pub fn parse_mutability(&mut self) -> Mutability {
        if self.eat(TokenKind::Mut) {
            Mutability::Mutable
        } else {
            if self.eat(TokenKind::Const) {
                let message = format!("unnecessary `const` modifier");
                self.emit_warning(message, self.previous().unwrap().span);
            }
            Mutability::Immutable
        }
    }
}

impl Parser {
    /* ------------------------------------------------------------------ */
    /* 1. Conditional splitter helpers                                    */
    /* ------------------------------------------------------------------ */

    /// Returns `true` IFF the *next* token *can* satisfy `expected`,
    /// performing "unshifting" on the fly if we are inside `< ... >`
    /// and the compound token needs to be split.
    fn test_then_unshift(&mut self, expected: TokenKind) -> bool {
        use TokenKind::*;
        let k0 = self.current_kind(); // raw token from the lexer
        match (expected, k0, self.angle_depth) {
            /* Looking for '<' but lexer gave us '<<' */
            (LChevron, Shl, depth) if depth > 0 => {
                self.split_shl(); // inject "<" "<"
                true
            }
            /* Looking for '>' but lexer gave us '>>' or '>>=' */
            (RChevron, Shr, depth) | (RChevron, ShrEq, depth) if depth > 0 => {
                self.split_shr_like(k0); // inject ">" (">" ["="])
                true
            }
            /* Looking for '=' after we've already split '>>='  */
            (Eql, token, _) if token == Eql => true,

            /* Normal single-token match */
            _ => k0 == expected,
        }
    }

    pub fn expect_unshifted(&mut self, kind: TokenKind) -> R<()> {
        if self.eat_unshifted(kind.clone()) {
            Ok(())
        } else {
            let msg = format!(
                "expected '{}',  got '{}' instead",
                kind,
                self.current_kind()
            );
            let err = SpannedMessage::new(msg, self.current_token_span());
            Err(err)
        }
    }

    /// Consuming version (`eat_*` style).
    fn eat_unshifted(&mut self, expected: TokenKind) -> bool {
        if self.test_then_unshift(expected) {
            self.bump(); // now safe: correct token is first
            true
        } else {
            false
        }
    }

    /*  low-level split helpers  --------------------------------------- */

    fn split_shl(&mut self) {
        // "<<": replace current with "<" then insert "<" after it.
        self.replace_current(TokenKind::LChevron);
        self.insert_future_token(TokenKind::LChevron);
    }
    fn split_shr_like(&mut self, k0: TokenKind) {
        // ">>" or ">>="
        self.replace_current(TokenKind::RChevron);
        self.insert_future_token(TokenKind::RChevron);
        if k0 == TokenKind::ShrEq {
            self.insert_future_token(TokenKind::Eql); // '=' from '>>='
        }
    }

    pub fn replace_current(&mut self, kind: TokenKind) {
        self.file.tokens[self.cursor].kind = kind;
    }
    fn insert_future_token(&mut self, kind: TokenKind) {
        let span = self
            .previous()
            .map(|f| f.span)
            .unwrap_or(Span::empty(self.file.file));
        self.file.tokens.insert(
            self.cursor + 1,
            Token {
                kind,
                span,
                content: span,
            },
        );
    }
}
