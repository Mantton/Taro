use taroc_token::{Delimiter, TokenKind};

use super::package::{Parser, R};

impl Parser {
    pub fn parse_delimiter_sequence<T, F>(
        &mut self,
        delim: Delimiter,
        separator: TokenKind,
        allow_trailing_sep: bool,
        mut action: F,
    ) -> R<Vec<T>>
    where
        F: FnMut(&mut Parser) -> R<T>,
    {
        // eat open
        self.expect(delim.open())?;

        self.consume_comments_and_new_lines();

        // if immediately closed return empty vec
        if self.eat(delim.close()) {
            return Ok(Vec::new());
        }

        let mut proceed = true;

        let mut items = Vec::new();
        while proceed {
            // parse item
            let item = action(self)?;
            items.push(item);

            proceed = self.eat(separator);
            self.consume_comments_and_new_lines();

            // can proceed but cursor points to ending token and allows a trailing sep, exit loop otherwise continue and perhaps throw error
            if proceed && self.matches(delim.close()) && allow_trailing_sep {
                break;
            } else if proceed && self.matches(delim.close()) {
                // recoverable error, trailing not allowed
            }
        }

        self.expect(delim.close())?;

        Ok(items)
    }

    pub fn parse_sequence_until<T, F>(
        &mut self,
        until: &[TokenKind],
        separator: TokenKind,
        allow_trailing_sep: bool,
        mut action: F,
    ) -> R<Vec<T>>
    where
        F: FnMut(&mut Parser) -> R<T>,
    {
        let mut proceed = true;

        let mut items = Vec::new();
        while proceed {
            // parse item
            let item = action(self)?;
            items.push(item);

            proceed = self.eat(separator);

            // can proceed but cursor points to ending token and allows a trailing sep, exit loop otherwise continue and perhaps throw error
            if proceed && self.matches_any(until) && allow_trailing_sep {
                break;
            } else if self.matches_any(until) {
                break;
            }
        }

        Ok(items)
    }
}

impl Parser {
    pub fn parse_block_sequence<T, F>(&mut self, mut parse_action: F) -> R<Vec<T>>
    where
        F: FnMut(&mut Parser) -> R<T>,
    {
        self.expect(TokenKind::LBrace)?;
        self.consume_comments_and_new_lines();

        let mut items = vec![];

        while !self.matches(TokenKind::RBrace) && !self.is_at_end() {
            self.consume_comments_and_new_lines();
            if self.matches(TokenKind::RBrace) {
                break;
            }
            let item = parse_action(self)?;
            items.push(item);

            if self.matches(TokenKind::RBrace) {
                break;
            }
        }

        self.expect(TokenKind::RBrace)?;
        Ok(items)
    }

    pub fn parse_brace_sequence<T, F>(&mut self, opening: bool, mut parse_action: F) -> R<Vec<T>>
    where
        F: FnMut(&mut Parser) -> R<T>,
    {
        if opening {
            self.expect(TokenKind::LBrace)?;
            self.consume_comments_and_new_lines();
        }

        let mut items = vec![];

        while !self.matches(TokenKind::RBrace) && !self.is_at_end() {
            self.consume_comments_and_new_lines();
            if self.matches(TokenKind::RBrace) {
                break;
            }
            let item = parse_action(self)?;
            items.push(item);

            if self.matches(TokenKind::RBrace) {
                break;
            }
        }

        self.expect(TokenKind::RBrace)?;
        Ok(items)
    }
}

impl Parser {
    pub fn parse_sequence<T, F>(&mut self, separator: TokenKind, mut action: F) -> R<Vec<T>>
    where
        F: FnMut(&mut Parser) -> R<T>,
    {
        self.consume_comments_and_new_lines();
        let mut proceed = true;
        let mut items = Vec::new();
        while proceed {
            let item = action(self)?;
            items.push(item);
            proceed = self.eat(separator);
        }
        Ok(items)
    }
}
