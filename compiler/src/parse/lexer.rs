use crate::{
    cfg,
    compile::source::EntryKind,
    constants::{FILE_EXTENSION, ROOT_MODULE_NAME, SOURCE_DIRECTORY},
    diagnostics::DiagCtx,
    error::ReportedError,
    parse::token::{Base, IntegerTypeSuffix, Token},
    span::{FileID, Position, Span, Spanned},
};
use std::{ffi::OsStr, path::PathBuf};

pub struct Pacakge {
    pub root: Module,
}

pub struct Module {
    pub name: String,
    pub files: Vec<File>,
    pub submodules: Vec<Module>,
}

pub struct File {
    pub id: FileID,
    pub tokens: Vec<Spanned<Token>>,
}

pub fn tokenize_package(
    path: PathBuf,
    dcx: &DiagCtx,
    target_triple: Option<&str>,
) -> Result<Pacakge, ReportedError> {
    let source = path.join(SOURCE_DIRECTORY);
    let mut root = tokenize_module(source, dcx, target_triple)?;
    root.name = ROOT_MODULE_NAME.into();

    Ok(Pacakge { root })
}

/// Tokenize a single source file as a virtual package.
/// The file becomes the root module with name "main".
pub fn tokenize_single_file(
    path: PathBuf,
    dcx: &DiagCtx,
    target_triple: Option<&str>,
) -> Result<Pacakge, ReportedError> {
    let file_path = match dcx.sources().resolve(&path) {
        Ok(path) => path,
        Err(e) => {
            let message = format!("failed to resolve source file – {e}");
            dcx.emit_error(message, None);
            return Err(ReportedError);
        }
    };

    // Verify it's a .tr file
    if file_path
        .extension()
        .and_then(|e| e.to_str())
        .map(|e| e != FILE_EXTENSION)
        .unwrap_or(true)
    {
        dcx.emit_error(
            format!(
                "expected a .{} file, got '{}'",
                FILE_EXTENSION,
                file_path.display()
            ),
            None,
        );
        return Err(ReportedError);
    }

    let id = dcx.add_file_mapping(file_path.clone());
    let file = match tokenize_file(id, file_path.clone(), dcx, target_triple) {
        Ok(file) => file,
        Err(_) => {
            return Err(ReportedError);
        }
    };

    let root = Module {
        name: ROOT_MODULE_NAME.into(),
        files: vec![file],
        submodules: vec![],
    };

    Ok(Pacakge { root })
}

pub fn tokenize_module(
    path: PathBuf,
    dcx: &DiagCtx,
    target_triple: Option<&str>,
) -> Result<Module, ReportedError> {
    let directory = match dcx.sources().resolve(&path) {
        Ok(path) => path,
        Err(e) => {
            let message = format!("failed to resolve project source directory – {e}");
            dcx.emit_error(message, None);
            return Err(ReportedError);
        }
    };

    let name = {
        let name = directory
            .file_name()
            .and_then(|name| name.to_str())
            .map(|s| s.to_string());
        match name {
            Some(name) => name,
            None => {
                let message = format!(
                    "failed to parse directory name from path '{}'",
                    directory.display()
                );
                dcx.emit_error(message, None);
                return Err(ReportedError);
            }
        }
    };

    let entries = match dcx.sources().read_directory(&directory) {
        Ok(entries) => entries,
        Err(e) => {
            let message = format!("failed to read directory '{}': {}", directory.display(), e);
            dcx.emit_error(message, None);
            return Err(ReportedError);
        }
    };

    let mut submodules = vec![];
    let mut files = vec![];

    for entry in entries {
        let path = entry.path;
        match entry.kind {
            EntryKind::File => {
                if path.extension().unwrap_or(OsStr::new("")) != FILE_EXTENSION {
                    continue;
                }
                let id = dcx.add_file_mapping(path.clone());
                files.push(tokenize_file(id, path, dcx, target_triple)?);
            }
            EntryKind::Directory => submodules.push(tokenize_module(path, dcx, target_triple)?),
        }
    }

    Ok(Module {
        files,
        submodules,
        name: name.into(),
    })
}

pub fn tokenize_file(
    file: FileID,
    path: PathBuf,
    dcx: &DiagCtx,
    target_triple: Option<&str>,
) -> Result<File, ReportedError> {
    let source = match dcx.sources().read_text(&path) {
        Ok(source) => source,
        Err(e) => {
            let message = format!("failed to read file '{}': {}", path.display(), e);
            dcx.emit_error(message.clone(), None);
            return Err(ReportedError);
        }
    };

    // Check for //+cfg directive on first line
    if let Some(triple) = target_triple {
        if !cfg::evaluate_file_cfg(source.text(), triple) {
            // File is excluded by cfg - return empty file with just EOF
            return Ok(File {
                id: file,
                tokens: vec![Spanned::new(Token::EOF, Span::empty(file))],
            });
        }
    }

    let lexer = Lexer::new(source.text(), file);
    dcx.record_source(file, source);
    match lexer.tokenize() {
        Ok(file) => Ok(file),
        Err(err) => {
            let message = format!("lexer error: {}", err.value);
            dcx.emit_error(message, Some(err.span));
            Err(ReportedError)
        }
    }
}

pub struct Lexer {
    source: Vec<char>,
    file: FileID,

    anchor: Position,
    cursor: usize,
    line: usize,
    offset: usize,
    tokens: Vec<Spanned<Token>>,
}

impl Lexer {
    pub fn new(source: &str, file: FileID) -> Lexer {
        let position = Position { line: 0, offset: 0 };
        // Normalize CRLF once, before tokenization, including inside literals.
        // Spans are line/column positions, so LF and CRLF files agree.
        let mut chars = source.chars().peekable();
        let source = std::iter::from_fn(|| {
            let ch = chars.next()?;
            if ch == '\r' && chars.peek() == Some(&'\n') {
                chars.next()
            } else {
                Some(ch)
            }
        })
        .collect();
        Lexer {
            anchor: position,
            cursor: 0,
            line: position.line,
            offset: position.offset,
            tokens: Vec::new(),
            source,
            file,
        }
    }
}

impl Lexer {
    pub fn tokenize(mut self) -> Result<File, Spanned<LexerError>> {
        while self.has_next() {
            self.anchor = self.position();
            let case = match self.next_token() {
                Ok(case) => case,
                Err(e) => {
                    let span = self.span_from_anchor();
                    return Err(Spanned::new(e, span));
                }
            };

            match case {
                TokenCase::End => {
                    break;
                }
                TokenCase::Skip => {
                    continue;
                }
                TokenCase::Valid(token) => {
                    let span = self.span_from_anchor();
                    let spanned = Spanned::new(token, span);
                    self.tokens.push(spanned);
                }
            }
        }
        // add eof token
        self.tokens
            .push(Spanned::new(Token::EOF, Span::empty(self.file)));

        // ASI
        self.tokens = automatic_semicolon_insertion(self.tokens);

        Ok(File {
            id: self.file,
            tokens: self.tokens,
        })
    }
}

// Utilities
impl Lexer {
    fn has_next(&self) -> bool {
        self.cursor < self.source.len()
    }

    fn eat(&mut self, c: char) -> bool {
        if !self.has_next() {
            return false;
        }

        match self.first() {
            Some(rs) if rs == c => {
                self.next_char();
                true
            }
            _ => false,
        }
    }

    fn first(&self) -> Option<char> {
        if !self.has_next() {
            return None;
        }

        return self.source.get(self.cursor).cloned();
    }

    fn second(&self) -> Option<char> {
        if let Some(_) = self.first() {
            return self.source.get(self.cursor + 1).cloned();
        } else {
            return None;
        }
    }
}

// Spans
impl Lexer {
    fn position(&self) -> Position {
        Position {
            line: self.line,
            offset: self.offset,
        }
    }

    fn span_from_anchor(&self) -> Span {
        Span {
            start: self.anchor,
            end: self.position(),
            file: self.file,
        }
    }

    #[inline]
    pub fn read(&self, lo: usize, hi: usize) -> String {
        self.source[lo..hi].iter().collect()
    }
}

// Chars
impl Lexer {
    fn next_char(&mut self) -> Option<char> {
        let ch = self.source.get(self.cursor).cloned();
        self.cursor += 1;
        self.offset += 1;

        if ch == Some('\n') {
            self.line += 1;
            self.offset = 0;
        }

        ch
    }
}

// Core
impl Lexer {
    fn next_token(&mut self) -> Result<TokenCase, LexerError> {
        let Some(char) = self.next_char() else {
            return Ok(TokenCase::End);
        };

        let token = match char {
            ' ' | '\t' | '\n' | '\r' => return Ok(TokenCase::Skip),
            '(' => Token::LParen,
            ')' => Token::RParen,
            '[' => Token::LBracket,
            ']' => Token::RBracket,
            '{' => Token::LBrace,
            '}' => Token::RBrace,
            ';' => Token::Semicolon,
            ',' => Token::Comma,
            '@' => Token::At,
            '#' => {
                let extra = self.source[self.cursor..]
                    .iter()
                    .take_while(|ch| **ch == '#')
                    .count();
                if self.source.get(self.cursor + extra) == Some(&'"') {
                    for _ in 0..extra + 1 {
                        self.next_char();
                    }
                    self.lex_string(extra + 1)?;
                    return Ok(TokenCase::Skip);
                }
                // Multiple hashes only introduce a raw string. Reject a bad
                // prefix once rather than rescanning its suffix for every `#`.
                if extra > 0 {
                    for _ in 0..extra {
                        self.next_char();
                    }
                    return Err(LexerError::InvalidCharacter('#'));
                }
                Token::Hash
            }
            '~' => Token::Tilde,
            ':' => {
                if self.eat(':') {
                    Token::ColonColon
                } else if self.eat('=') {
                    Token::ColonEq
                } else {
                    Token::Colon
                }
            }
            '.' => {
                if self.eat('.') {
                    let token = if self.eat('.') {
                        // ...
                        Token::Ellipsis
                    } else if self.eat('=') {
                        // ..=
                        Token::DotDotEq
                    } else {
                        // ..
                        Token::DotDot
                    };
                    token
                } else if self.eat('*') {
                    Token::DotStar
                } else {
                    Token::Dot
                }
            }
            '-' => {
                if self.eat('>') {
                    Token::RArrow
                } else if self.eat('=') {
                    Token::MinusEq
                } else {
                    Token::Minus
                }
            }
            '+' => {
                if self.eat('=') {
                    Token::PlusEq
                } else {
                    Token::Plus
                }
            }
            '*' => {
                if self.eat('=') {
                    Token::MulEq
                } else {
                    Token::Star
                }
            }
            '%' => {
                if self.eat('=') {
                    Token::RemEq
                } else {
                    Token::Modulus
                }
            }
            '!' => {
                if self.eat('=') {
                    if self.eat('=') {
                        Token::IdentityNeq
                    } else {
                        Token::Neq
                    }
                } else if self.first() == Some('i')
                    && self.second() == Some('n')
                    && !self
                        .source
                        .get(self.cursor + 2)
                        .is_some_and(|c| Lexer::is_alphanumeric(*c))
                {
                    // `!in` is one token only when `in` is a whole word:
                    // `!inside` stays `!` applied to an identifier, and
                    // `value! in set` (space after `!`) stays propagation.
                    self.next_char();
                    self.next_char();
                    Token::BangIn
                } else {
                    Token::Bang
                }
            }
            '=' => {
                if self.eat('=') {
                    if self.eat('=') {
                        Token::IdentityEql
                    } else {
                        Token::Eql
                    }
                } else if self.eat('>') {
                    Token::EqArrow
                } else {
                    Token::Assign
                }
            }
            '<' => {
                if self.eat('=') {
                    Token::Leq
                } else if self.eat('<') {
                    if self.eat('=') {
                        Token::ShlEq
                    } else {
                        Token::Shl
                    }
                } else {
                    Token::LChevron
                }
            }
            '>' => {
                if self.eat('=') {
                    Token::Geq
                } else if self.eat('>') {
                    if self.eat('=') {
                        Token::ShrEq
                    } else {
                        Token::Shr
                    }
                } else {
                    Token::RChevron
                }
            }
            '?' => {
                if self.eat('?') {
                    if self.eat('=') {
                        Token::QuestionQuestionEq
                    } else {
                        Token::QuestionQuestion
                    }
                } else if !self.source[self.cursor..].starts_with(&['.', '.', '.']) && self.eat('.')
                {
                    Token::QuestionDot
                } else {
                    Token::Question
                }
            }
            '^' => {
                if self.eat('=') {
                    Token::CaretEq
                } else {
                    Token::Caret
                }
            }
            '&' => {
                if self.eat('&') {
                    Token::AmpAmp
                } else if self.eat('=') {
                    Token::AmpEq
                } else {
                    Token::Amp
                }
            }
            '|' => {
                if self.eat('|') {
                    Token::BarBar
                } else if self.eat('>') {
                    Token::Pipe
                } else if self.eat('=') {
                    Token::BarEq
                } else {
                    Token::Bar
                }
            }
            '/' => {
                if self.eat('/') {
                    self.single_line_comment();
                    return Ok(TokenCase::Skip);
                } else if self.eat('*') {
                    self.multi_line_comment()?;
                    return Ok(TokenCase::Skip);
                } else if self.eat('=') {
                    Token::DivEq
                } else {
                    Token::Quotient
                }
            }
            '_' => {
                if self.first() != None && Lexer::is_alphanumeric(self.first().unwrap_or_default())
                {
                    self.identifier()
                } else {
                    Token::Underscore
                }
            }
            'f' if self.first() == Some('"') => return Err(LexerError::ObsoleteStringPrefix),
            '"' => {
                self.lex_string(0)?;
                return Ok(TokenCase::Skip);
            }
            '`' => self.escaped_identifier()?,
            '\'' => self.rune()?,
            _ => {
                if Lexer::is_digit(char) {
                    self.number(char)?
                } else if Lexer::is_alphanumeric(char) {
                    self.identifier()
                } else {
                    return Err(LexerError::InvalidCharacter(char));
                }
            }
        };

        return Ok(TokenCase::Valid(token));
    }
}

// identifiers
impl Lexer {
    fn identifier(&mut self) -> Token {
        let lo = self.cursor - 1;
        loop {
            match self.first() {
                Some(c) if Lexer::is_alphanumeric(c) => {
                    self.next_char();
                }
                _ => break,
            }
        }
        let hi = self.cursor;
        let content = self.read(lo, hi);
        let kw = str_to_keyword(&content);
        kw.unwrap_or_else(|| Token::Identifier {
            value: content.into(),
        })
    }
}

// runes
impl Lexer {
    fn rune(&mut self) -> Result<Token, LexerError> {
        let Some(content) = self.single_quoted_string() else {
            return Err(LexerError::UnterminatedRuneLiteral);
        };
        Ok(Token::Rune {
            value: content.into(),
        })
    }

    fn single_quoted_string(&mut self) -> Option<String> {
        let lo = self.cursor;

        // Next points to char after initial quote
        // Is one-symbol literal
        if self.second() == Some('\'') && self.first() != Some('\\') {
            self.next_char(); // eat single char
            let hi = self.cursor;
            self.next_char(); // eat closing quote
            return Some(self.read(lo, hi));
        }

        'PARENT: loop {
            match self.first() {
                Some('\'') => {
                    let hi = self.cursor;
                    self.next_char(); // eat closing quote
                    let content = self.read(lo, hi);
                    return Some(content);
                }
                Some('/') => break 'PARENT,
                Some('\n') => {
                    if self.second() != Some('\'') {
                        break 'PARENT;
                    }
                }
                Some('\\') => {
                    // considered one character, bump twice
                    self.next_char();
                    self.next_char();
                }
                None => break,
                _ => {
                    self.next_char();
                }
            }
        }

        None
    }
}

// Strings are decoded exactly once, here, before parser-generated format strings
// escape percent signs. Raw text uses the same token/AST representation without
// ever passing through the backslash decoder.
impl Lexer {
    fn push_token_with_span(&mut self, token: Token, start: Position, end: Position) {
        self.tokens.push(Spanned::new(
            token,
            Span {
                start,
                end,
                file: self.file,
            },
        ));
    }

    fn string_delimiter_at(&self, quotes: usize, hashes: usize) -> bool {
        self.source
            .get(self.cursor..self.cursor + quotes)
            .is_some_and(|text| text.iter().all(|ch| *ch == '"'))
            && self
                .source
                .get(self.cursor + quotes..self.cursor + quotes + hashes)
                .is_some_and(|text| text.iter().all(|ch| *ch == '#'))
    }

    /// Only `$` followed by exactly the delimiter's hash count and `{` opens
    /// interpolation. Mismatches remain ordinary text; `$$` has no special role.
    fn interpolation_at(&self, hashes: usize) -> bool {
        self.first() == Some('$')
            && self
                .source
                .get(self.cursor + 1..self.cursor + 1 + hashes)
                .is_some_and(|text| text.iter().all(|ch| *ch == '#'))
            && self.source.get(self.cursor + 1 + hashes) == Some(&'{')
    }

    fn emit_string_text(&mut self, text: &mut String, start: Position, pieces: &mut Vec<usize>) {
        if !text.is_empty() {
            pieces.push(self.tokens.len());
            self.push_token_with_span(
                Token::StringText {
                    value: std::mem::take(text),
                },
                start,
                self.position(),
            );
        }
    }

    /// The opening quote has already been consumed (including any raw hashes).
    /// Plain strings never enter the interpolation token stream, preserving
    /// attributes, patterns and ABI names without allocating format tokens.
    fn lex_string(&mut self, hashes: usize) -> Result<(), LexerError> {
        let start = self.anchor;
        let multiline = self.first() == Some('"') && self.second() == Some('"');
        if multiline {
            self.next_char();
            self.next_char();
        }
        let opening_end = self.position();
        if multiline && !self.eat('\n') {
            return Err(LexerError::MultilineStringOpening);
        }
        let mut text_start = self.position();
        let mut text = String::new();
        let mut pieces = Vec::new();
        let mut interpolated = false;
        let closing_indent;

        loop {
            let Some(ch) = self.first() else {
                self.anchor = start;
                return Err(LexerError::UnterminatedStringLiteral);
            };
            if self.string_delimiter_at(if multiline { 3 } else { 1 }, hashes) {
                closing_indent = if multiline {
                    let line_start = self.source[..self.cursor]
                        .iter()
                        .rposition(|ch| *ch == '\n')
                        .map_or(0, |i| i + 1);
                    let indent: String = self.source[line_start..self.cursor].iter().collect();
                    if !indent.chars().all(|ch| matches!(ch, ' ' | '\t')) {
                        self.anchor = self.position();
                        return Err(LexerError::MultilineStringClosing);
                    }
                    // The closing line's indentation and preceding boundary LF
                    // are source layout, not part of the value.
                    text.truncate(text.len() - indent.len());
                    if text.ends_with('\n') {
                        text.pop();
                    }
                    indent
                } else {
                    String::new()
                };
                let quote_start = self.position();
                if !interpolated {
                    for _ in 0..(if multiline { 3 } else { 1 }) + hashes {
                        self.next_char();
                    }
                    let value = decode_string_text(
                        text,
                        text_start.offset == 0,
                        multiline,
                        &closing_indent,
                        true,
                        hashes,
                    )
                    .map_err(|(error, line)| {
                        self.anchor = string_error_position(text_start, line);
                        error
                    })?;
                    self.push_token_with_span(Token::String { value }, start, self.position());
                    self.anchor = start;
                    return Ok(());
                }
                self.emit_string_text(&mut text, text_start, &mut pieces);
                for _ in 0..(if multiline { 3 } else { 1 }) + hashes {
                    self.next_char();
                }
                self.push_token_with_span(
                    Token::InterpolatedStringEnd,
                    quote_start,
                    self.position(),
                );
                break;
            }
            if self.interpolation_at(hashes) {
                if !interpolated {
                    self.push_token_with_span(Token::InterpolatedStringStart, start, opening_end);
                }
                self.emit_string_text(&mut text, text_start, &mut pieces);
                let marker_start = self.position();
                for _ in 0..hashes + 2 {
                    self.next_char();
                }
                self.push_token_with_span(
                    Token::StringInterpolationStart,
                    marker_start,
                    self.position(),
                );
                self.lex_string_interpolation(multiline, marker_start)?;
                let close_start = self.position();
                self.next_char(); // the matching `}`
                self.push_token_with_span(
                    Token::StringInterpolationEnd,
                    close_start,
                    self.position(),
                );
                text_start = self.position();
                interpolated = true;
                continue;
            }
            match ch {
                '\\' if hashes == 0 => {
                    text.push(self.next_char().unwrap());
                    match self.first() {
                        None => return Err(LexerError::UnterminatedStringLiteral),
                        Some('\n') => return Err(LexerError::StringLineContinuation),
                        Some(ch) => {
                            text.push(ch);
                            self.next_char();
                        }
                    }
                }
                '\n' if !multiline => return Err(LexerError::StringLiteralMustBeSingleLine),
                _ => {
                    text.push(ch);
                    self.next_char();
                }
            }
        }

        let end_token = self.tokens.len() - 1;
        for index in pieces {
            let piece = &mut self.tokens[index];
            let Token::StringText { value } = &mut piece.value else {
                unreachable!()
            };
            *value = decode_string_text(
                std::mem::take(value),
                piece.span.start.offset == 0,
                multiline,
                &closing_indent,
                index + 1 == end_token,
                hashes,
            )
            .map_err(|(error, line)| {
                self.anchor = string_error_position(piece.span.start, line);
                error
            })?;
        }
        self.anchor = start;
        Ok(())
    }

    fn lex_string_interpolation(
        &mut self,
        multiline: bool,
        marker: Position,
    ) -> Result<(), LexerError> {
        let mut brace_depth = 0usize;
        let mut group_depth = 0usize;
        let mut has_expression = false;
        loop {
            match self.first() {
                None => {
                    self.anchor = marker;
                    return Err(LexerError::UnterminatedStringInterpolation);
                }
                Some('\n') if !multiline => {
                    self.anchor = marker;
                    return Err(LexerError::UnterminatedStringInterpolation);
                }
                Some('}') if brace_depth == 0 => {
                    if !has_expression {
                        self.anchor = marker;
                        return Err(LexerError::EmptyStringInterpolation);
                    }
                    return Ok(());
                }
                _ => {}
            }
            self.anchor = self.position();
            let token_start = self.cursor;
            let line = self.line;
            let token_count = self.tokens.len();
            let token = self.next_token();
            if !multiline && self.line != line {
                let newline = self.source[token_start..self.cursor]
                    .iter()
                    .position(|ch| *ch == '\n')
                    .unwrap();
                self.cursor = token_start + newline;
                self.line = line;
                self.offset = self.anchor.offset + newline;
                self.anchor = marker;
                return Err(LexerError::UnterminatedStringInterpolation);
            }
            let token = token.map_err(|error| match error {
                LexerError::UnterminatedStringLiteral
                | LexerError::UnterminatedRuneLiteral
                | LexerError::UnterminatedEscapedIdentifier
                | LexerError::UnterminatedMultilineComment
                | LexerError::StringLiteralMustBeSingleLine => {
                    self.anchor = marker;
                    LexerError::UnterminatedStringInterpolation
                }
                other => other,
            })?;
            match token {
                // A colon outside every bracket ends the expression and opens
                // the hole's format specifier, unless it introduces a labeled
                // loop expression (`label: loop { ... }`). Labeled arguments
                // and struct fields sit inside their own delimiters, so they
                // never match.
                TokenCase::Valid(Token::Colon)
                    if brace_depth == 0
                        && group_depth == 0
                        && has_expression
                        && !self.interpolation_colon_is_loop_label() =>
                {
                    let colon = self.anchor;
                    let mut value = String::new();
                    loop {
                        match self.first() {
                            Some('}') => break,
                            None | Some('\n') => {
                                self.anchor = marker;
                                return Err(LexerError::UnterminatedStringInterpolation);
                            }
                            Some(ch) => {
                                value.push(ch);
                                self.next_char();
                            }
                        }
                    }
                    self.push_token_with_span(
                        Token::InterpolationFormat { value },
                        colon,
                        self.position(),
                    );
                    return Ok(());
                }
                TokenCase::Valid(token) => {
                    match token {
                        Token::LBrace => brace_depth += 1,
                        Token::RBrace => brace_depth -= 1,
                        Token::LParen | Token::LBracket => group_depth += 1,
                        Token::RParen | Token::RBracket => group_depth = group_depth.saturating_sub(1),
                        _ => {}
                    }
                    has_expression = true;
                    let span = self.span_from_anchor();
                    self.tokens.push(Spanned::new(token, span));
                }
                // Nested strings emit their own tokens; comments/whitespace do not.
                TokenCase::Skip => {
                    has_expression |= self.tokens.len() > token_count;
                }
                TokenCase::End => {
                    self.anchor = marker;
                    return Err(LexerError::UnterminatedStringInterpolation);
                }
            }
        }
    }

    fn interpolation_colon_is_loop_label(&self) -> bool {
        let mut idx = self.cursor;
        while let Some(&ch) = self.source.get(idx) {
            if ch == ' ' || ch == '\t' {
                idx += 1;
            } else {
                break;
            }
        }
        let rest = &self.source[idx..];
        for keyword in [&['l', 'o', 'o', 'p'][..], &['w', 'h', 'i', 'l', 'e'], &['f', 'o', 'r']] {
            if rest.starts_with(keyword) {
                let after = rest.get(keyword.len()).copied();
                if after.is_none_or(|ch| !ch.is_alphanumeric() && ch != '_') {
                    return true;
                }
            }
        }
        false
    }
}

/// Decode literal text before the parser builds formatting strings. A raw
/// string's hash-qualified interpolation is handled by the lexer, not here.
/// Errors carry the line within the text piece that caused them, so the
/// diagnostic can point at that line rather than at the start of the piece.
fn decode_string_text(
    mut value: String,
    line_start: bool,
    multiline: bool,
    indent: &str,
    final_piece: bool,
    hashes: usize,
) -> Result<String, (LexerError, usize)> {
    if multiline {
        value = strip_string_indentation(&value, line_start, indent, final_piece)
            .map_err(|line| (LexerError::MultilineStringIndentation, line))?;
    }
    if hashes == 0 {
        super::escape::unescape_str(&value).map_err(|error| (LexerError::MalformedString(error), 0))
    } else if value.contains('\r') {
        Err((
            LexerError::MalformedString(super::escape::EscapeError::BareCarriageReturn),
            0,
        ))
    } else {
        Ok(value)
    }
}

/// The start of `line` lines after a text piece that begins at `start`.
fn string_error_position(start: Position, line: usize) -> Position {
    if line == 0 {
        start
    } else {
        Position {
            line: start.line + line,
            offset: 0,
        }
    }
}

/// Strip physical source indentation only. Interpolation results never pass
/// through this function, and lines inside expression tokens are left alone.
/// On failure, returns the index of the first badly indented line.
fn strip_string_indentation(
    text: &str,
    mut line_start: bool,
    indent: &str,
    final_piece: bool,
) -> Result<String, usize> {
    let mut output = String::with_capacity(text.len());
    let lines = text.split_inclusive('\n');
    let line_count = lines.clone().count();
    for (index, line) in lines.enumerate() {
        if line_start {
            if let Some(rest) = line.strip_prefix(indent) {
                output.push_str(rest);
            } else if line.chars().all(|ch| matches!(ch, ' ' | '\t' | '\n'))
                && (line.ends_with('\n') || (final_piece && index + 1 == line_count))
            {
                if line.ends_with('\n') {
                    output.push('\n');
                }
            } else {
                return Err(index);
            }
        } else {
            output.push_str(line);
        }
        line_start = line.ends_with('\n');
    }
    Ok(output)
}

// escaped identifiers
impl Lexer {
    fn escaped_identifier(&mut self) -> Result<Token, LexerError> {
        let Some(content) = self.back_quote_string()? else {
            return Err(LexerError::UnterminatedEscapedIdentifier);
        };

        return Ok(Token::Identifier {
            value: content.into(),
        });
    }

    fn back_quote_string(&mut self) -> Result<Option<String>, LexerError> {
        let lo = self.cursor;
        loop {
            match self.next_char() {
                Some('`') => {
                    let hi = self.cursor - 1;
                    return Ok(Some(self.read(lo, hi)));
                }
                Some('\\') if self.eat('\\') || self.eat('`') => {
                    self.next_char();
                }
                Some('\n') => return Err(LexerError::EscapeIdentifierMustBeSingleLine),
                None => break,
                _ => {
                    continue;
                }
            };
        }

        Ok(None)
    }
}

// Comments
impl Lexer {
    fn single_line_comment(&mut self) {
        // slashes have already been parsed
        while self.first() != Some('\n') && self.has_next() {
            self.next_char();
        }
    }

    fn multi_line_comment(&mut self) -> Result<(), LexerError> {
        let mut depth = 1usize;
        while self.has_next() {
            if self.first() == Some('/') && self.second() == Some('*') {
                self.next_char();
                self.next_char();
                depth += 1;
            } else if self.first() == Some('*') && self.second() == Some('/') {
                self.next_char(); // eat '*'
                self.next_char(); // eat '/'
                depth -= 1;
                if depth == 0 {
                    return Ok(());
                }
            } else {
                self.next_char();
            }
        }

        // EOF without closing "*/"
        Err(LexerError::UnterminatedMultilineComment)
    }
}

// Numbers
impl Lexer {
    fn number(&mut self, first_digit: char) -> Result<Token, LexerError> {
        let mut base = Base::Decimal;
        let lo = self.cursor - 1; // we've consumed the first token already
        let content = |this: &Lexer| this.read(lo, this.cursor);

        if first_digit == '0' {
            match self.first() {
                Some('b') => {
                    base = Base::Binary;
                    self.next_char(); // eat base char

                    let res = self.eat_digits(Self::is_digit);

                    if !res {
                        return Err(LexerError::InvalidIntegerLiteral);
                    }
                }
                Some('o') => {
                    base = Base::Octal;
                    self.next_char();

                    let res = self.eat_digits(Self::is_digit);

                    if !res {
                        return Err(LexerError::InvalidIntegerLiteral);
                    }
                }
                Some('x') => {
                    base = Base::Hexadecimal;
                    self.next_char();

                    let res = self.eat_digits(Self::is_hex_char);

                    if !res {
                        return Err(LexerError::InvalidIntegerLiteral);
                    }
                }
                Some(c) => match c {
                    '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' | '_' => {
                        self.eat_digits(Self::is_digit);
                    }
                    '.' | 'e' | 'E' => {
                        // these will be handled in the next half
                    }
                    _ => {
                        // just a 0
                        return Ok(Token::Integer {
                            value: content(self).into(),
                            base,
                            suffix: None,
                        });
                    }
                },
                None => {
                    // `0` at end of a source without trailing content.
                    return Ok(Token::Integer {
                        value: content(self).into(),
                        base,
                        suffix: None,
                    });
                }
            }
        } else {
            self.eat_digits(Self::is_digit);
        }

        // After a member-access dot the number is a field index. A following
        // dot starts the next projection in `value.0.1`.
        let field_index = matches!(self.tokens.last().map(|token| &token.value),
            Some(Token::Dot | Token::QuestionDot));
        match self.first() {
            Some('.') if !field_index => {
                let sec = self.second();
                // eat decimal point, avoid range expr
                if sec != None && sec != Some('.') && !Lexer::is_letter(sec.unwrap()) {
                    self.next_char();
                    let mut empty = false;

                    if self.first() != None && Lexer::is_digit(self.first().unwrap()) {
                        self.eat_digits(Self::is_digit);

                        match self.first() {
                            Some('e') | Some('E') => {
                                self.next_char();
                                empty = !self.eat_float_exponents();
                            }
                            _ => {}
                        }
                    }

                    if empty {
                        return Err(LexerError::InvalidFloatLiteral);
                    }

                    return Ok(Token::Float {
                        value: content(self).into(),
                        base,
                    });
                }
            }
            Some('e') | Some('E') => {
                self.next_char();
                let empty = !self.eat_float_exponents();

                if empty {
                    return Err(LexerError::InvalidFloatLiteral);
                }

                return Ok(Token::Float {
                    value: content(self).into(),
                    base,
                });
            }
            _ => {}
        }

        let integer_value = content(self);
        let suffix = self.parse_integer_suffix(integer_value.as_str())?;
        return Ok(Token::Integer {
            value: integer_value.into(),
            base,
            suffix,
        });
    }
}

impl Lexer {
    fn parse_integer_suffix(
        &mut self,
        current_content: &str,
    ) -> Result<Option<IntegerTypeSuffix>, LexerError> {
        if !current_content.ends_with('_') {
            return Ok(None);
        }

        let sign = match self.first() {
            Some(c @ ('i' | 'I' | 'u' | 'U')) => c,
            _ => return Ok(None),
        };
        self.next_char();

        let bits_lo = self.cursor;
        while matches!(self.first(), Some(c) if Lexer::is_digit(c)) {
            self.next_char();
        }
        let bits = self.read(bits_lo, self.cursor);

        let Some(suffix) = IntegerTypeSuffix::parse(sign, &bits) else {
            return Err(LexerError::InvalidIntegerLiteral);
        };

        if matches!(self.first(), Some(c) if Lexer::is_alphanumeric(c) || c == '_') {
            return Err(LexerError::InvalidIntegerLiteral);
        }

        Ok(Some(suffix))
    }

    fn eat_digits(&mut self, is_digit: fn(char) -> bool) -> bool {
        let mut has_digits = false;
        while let Some(c) = self.first() {
            if is_digit(c) {
                has_digits = true;
            } else if c != '_' {
                break;
            }
            self.next_char();
        }
        has_digits
    }

    fn eat_float_exponents(&mut self) -> bool {
        if self.eat('-') || self.eat('+') {
            // sign already consumed
        }

        self.eat_digits(Self::is_digit)
    }
}

impl Lexer {
    fn is_digit(c: char) -> bool {
        '0' <= c && c <= '9'
    }

    fn is_letter(c: char) -> bool {
        'a' <= c && c <= 'z' || 'A' <= c && c <= 'Z' || c == '_'
    }

    fn is_alphanumeric(c: char) -> bool {
        Self::is_letter(c) || Self::is_digit(c)
    }

    fn is_hex_char(c: char) -> bool {
        ('0' <= c && c <= '9') || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')
    }
}

fn str_to_keyword(word: &str) -> Option<Token> {
    let token = match word {
        "any" => Token::Any,
        "as" => Token::As,
        "is" => Token::Is,
        "break" => Token::Break,
        "case" => Token::Case,
        "const" => Token::Const,
        "continue" => Token::Continue,
        "defer" => Token::Defer,
        "else" => Token::Else,
        "enum" => Token::Enum,
        "export" => Token::Export,
        "extern" => Token::Extern,
        "false" => Token::False,
        "for" => Token::For,
        "func" => Token::Function,
        "guard" => Token::Guard,
        "if" => Token::If,
        "impl" => Token::Impl,
        "extend" => Token::Extend,
        "conform" => Token::Conform,
        "import" => Token::Import,
        "in" => Token::In,
        "init" => Token::Init,
        "deinit" => Token::Deinit,
        "interface" => Token::Interface,
        "let" => Token::Let,
        "loop" => Token::Loop,
        "match" => Token::Match,
        "mod" => Token::Mod,
        "namespace" => Token::Namespace,
        "nil" => Token::Nil,
        "operator" => Token::Operator,
        "private" => Token::Private,
        "internal" => Token::Internal,
        "public" => Token::Public,
        "readonly" => Token::Readonly,
        "return" => Token::Return,
        "static" => Token::Static,
        "struct" => Token::Struct,
        "true" => Token::True,
        "type" => Token::Type,
        "var" => Token::Var,
        "where" => Token::Where,
        "while" => Token::While,
        "unsafe" => Token::Unsafe,

        // reserved
        "class" => Token::Class,
        "final" => Token::Final,
        "override" => Token::Override,
        "fileprivate" => Token::FilePrivate,
        "protected" => Token::Protected,
        "async" => Token::Async,
        "await" => Token::Await,
        "mut" => Token::Mut,
        "ref" => Token::Ref,
        _ => return None,
    };

    Some(token)
}

#[derive(Debug)]
pub enum LexerError {
    InvalidCharacter(char),
    UnterminatedMultilineComment,
    UnterminatedEscapedIdentifier,
    UnterminatedRuneLiteral,
    UnterminatedStringLiteral,
    UnterminatedStringInterpolation,
    EmptyStringInterpolation,
    StringLiteralMustBeSingleLine,
    MultilineStringOpening,
    MultilineStringClosing,
    MultilineStringIndentation,
    StringLineContinuation,
    MalformedString(super::escape::EscapeError),
    ObsoleteStringPrefix,
    EscapeIdentifierMustBeSingleLine,
    InvalidIntegerLiteral,
    InvalidFloatLiteral,
}

impl std::fmt::Display for LexerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LexerError::InvalidCharacter(c) => write!(f, "invalid character '{}'", c),
            LexerError::UnterminatedMultilineComment => write!(f, "unterminated multiline comment"),
            LexerError::UnterminatedEscapedIdentifier => {
                write!(f, "unterminated escaped identifier")
            }
            LexerError::UnterminatedRuneLiteral => write!(f, "unterminated rune literal"),
            LexerError::UnterminatedStringLiteral => write!(f, "unterminated string literal"),
            LexerError::UnterminatedStringInterpolation => {
                write!(f, "unterminated string interpolation")
            }
            LexerError::EmptyStringInterpolation => {
                write!(f, "string interpolation cannot be empty")
            }
            LexerError::StringLiteralMustBeSingleLine => {
                write!(f, "string literals must be on a single line")
            }
            LexerError::MultilineStringOpening => f.write_str("multiline string opening delimiter must be followed by a newline"),
            LexerError::MultilineStringClosing => f.write_str("multiline string closing delimiter must be on its own line"),
            LexerError::MultilineStringIndentation => f.write_str("multiline string line does not match closing delimiter indentation"),
            LexerError::StringLineContinuation => f.write_str("backslash line continuations are not supported in strings"),
            LexerError::MalformedString(error) => write!(f, "malformed string, {error:?}"),
            LexerError::ObsoleteStringPrefix => f.write_str("the f string prefix is no longer supported; use ${expression} inside an ordinary string"),
            LexerError::EscapeIdentifierMustBeSingleLine => {
                write!(f, "escaped identifiers must be on a single line")
            }
            LexerError::InvalidIntegerLiteral => write!(f, "invalid integer literal"),
            LexerError::InvalidFloatLiteral => write!(f, "invalid float literal"),
        }
    }
}

pub enum TokenCase {
    End,
    Skip,
    Valid(Token),
}

/// Insert semicolons à la Go, *but* allow operator-leading continuations:
/// - If a newline (or EOF) follows a token that can end a statement, insert `;`.
/// - **Unless** the next token is a line-continuation starter
///   (an operator/connector like `+`, `-`, `*`, `.`, `..`, `==`, `=`, `|>`, etc.).
/// - **Unless** the newline sits directly inside `( )` or `[ ]`. Braces nested
///   inside those delimiters (blocks, closure bodies, `match` arms) and string
///   interpolations insert semicolons as usual.
pub fn automatic_semicolon_insertion(tokens: Vec<Spanned<Token>>) -> Vec<Spanned<Token>> {
    use crate::span::{Span, Spanned};

    let grouped = newline_inside_group(&tokens);
    let mut out = Vec::with_capacity(tokens.len() + 8);
    // Comments have already been consumed. Walk backwards for lookahead without clones.
    let mut next: Option<(usize, bool, bool)> = None;
    let mut tokens = tokens.into_iter().zip(grouped).rev().peekable();
    while let Some((token, grouped)) = tokens.next() {
        // The wildcard in `import path::*` ends the declaration. An ordinary
        // multiplication/dereference star still cannot end a statement.
        let path_glob = matches!(token.value, Token::Star)
            && matches!(tokens.peek(), Some((previous, _)) if matches!(previous.value, Token::ColonColon));
        let is_wildcard = matches!(token.value, Token::Underscore)
            && matches!(tokens.peek(), Some((previous, _)) if matches!(previous.value, Token::Is));
        let insert = (can_end_statement(&token.value) || path_glob || is_wildcard)
            && match next {
                None => true,
                Some((line, eof, continuation)) => {
                    eof || (line > token.span.end.line && !continuation && !grouped)
                }
            };
        if insert {
            let position = token.span.end;
            out.push(Spanned::new(
                Token::Semicolon,
                Span {
                    start: position,
                    end: position,
                    file: token.span.file,
                },
            ));
        }
        next = Some((
            token.span.start.line,
            is_eof(&token.value),
            is_line_continuation_starter(&token.value),
        ));
        out.push(token);
    }
    out.reverse();
    out
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Group {
    Paren,
    Bracket,
    Brace,
    Interpolation,
}

/// For each token, whether the innermost delimiter still open after it is
/// `(` or `[`, so a newline that follows it does not end a statement.
///
/// A closer pops back to its matching opener, discarding any unclosed
/// delimiters in between, and a closer with no matching opener is ignored.
/// An unclosed `(` therefore stops suppressing at the `}` that closes the
/// enclosing block, and the parser reports the error near the `(`.
pub(crate) fn newline_inside_group(tokens: &[Spanned<Token>]) -> Vec<bool> {
    let mut stack: Vec<Group> = Vec::new();
    let close = |stack: &mut Vec<Group>, group: Group| {
        if let Some(depth) = stack.iter().rposition(|open| *open == group) {
            stack.truncate(depth);
        }
    };
    tokens
        .iter()
        .map(|token| {
            match token.value {
                Token::LParen => stack.push(Group::Paren),
                Token::LBracket => stack.push(Group::Bracket),
                Token::LBrace => stack.push(Group::Brace),
                Token::StringInterpolationStart => stack.push(Group::Interpolation),
                Token::RParen => close(&mut stack, Group::Paren),
                Token::RBracket => close(&mut stack, Group::Bracket),
                Token::RBrace => close(&mut stack, Group::Brace),
                Token::StringInterpolationEnd => close(&mut stack, Group::Interpolation),
                _ => {}
            }
            matches!(stack.last(), Some(Group::Paren | Group::Bracket))
        })
        .collect()
}

fn can_end_statement(tok: &Token) -> bool {
    match tok {
        // primaries / identifiers / literals
        Token::Identifier { .. }
        | Token::Integer { .. }
        | Token::Float { .. }
        | Token::Rune { .. }
        | Token::String { .. }
        | Token::InterpolatedStringEnd
        // singletons
        | Token::True
        | Token::False
        | Token::Nil
        // keywords that end a stmt
        | Token::Break
        | Token::Continue
        | Token::Return
        // closers can end a stmt at a newline (parser may relax this inside groups)
        | Token::RParen
        | Token::RBracket
        | Token::RBrace
        // postfix optional marker (`T?`) should allow ASI to end the line
        | Token::Question
        // wildcard path suffix at end of import / export line
        | Token::DotStar
        // Never type (!) can end a statement (e.g. extern signature)
        | Token::Bang
        // Postfix lower-bounded / full range (`a..`, `..`) can end a statement
        | Token::DotDot => true,
        _ => false,
    }
}

fn is_eof(tok: &Token) -> bool {
    matches!(tok, Token::EOF)
}

/// Tokens that *cannot* start a new statement and therefore indicate the previous
/// line is continued if they appear at the beginning of a new line.
///
/// This enables operator-leading styles:
/// ```text
/// foo
/// + bar
/// * baz
/// .method()
/// .. upper
/// ?? fallback
/// |> pipe
/// ```
fn is_line_continuation_starter(tok: &Token) -> bool {
    use Token::*;
    matches!(
        tok,
        // arithmetic / bitwise / logical operators
        // Note: Star (*) and Amp (&) are excluded because they have common
        // unary uses (dereference and reference) that should start new statements
        StringInterpolationEnd | InterpolationFormat { .. } | Plus | Minus | Quotient | Modulus
        | Caret | Bar
        | AmpAmp | BarBar
        // relational / equality
        | LChevron | RChevron | Leq | Geq | Eql | Neq | IdentityEql | IdentityNeq
        // shifts
        | Shl | Shr
        // assignment family (leading assignment style)
        | Assign | ColonEq | PlusEq | MinusEq | MulEq | DivEq | RemEq
        | ShlEq | ShrEq | CaretEq | AmpEq | BarEq | QuestionQuestionEq
        // member / optional chaining / spread (`..` and `..=` excluded so prefix ranges start new statements)
        | Dot | ColonColon | Ellipsis | QuestionDot
        // nullish / pipe
        | QuestionQuestion | Pipe
        // arrows can lead a continuation (e.g., in patterns or lambdas)
        | RArrow | EqArrow
        // casting / infix-like keywords that glue to the previous expr
        | As | Is | In | BangIn
        // `else` only follows an `if` block or a `guard` condition, and
        // `where` only opens a where clause or a `for` filter
        | Else | Where
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::token::Token;

    fn tokenize_result(input: &str) -> Result<Vec<Token>, LexerError> {
        let dcx = DiagCtx::new(PathBuf::from("."));
        // We use a dummy file ID, effectively ignoring it for these unit tests.
        let file_id = dcx.add_file_mapping(PathBuf::from("test.taro"));
        let lexer = Lexer::new(input, file_id);

        let file = lexer.tokenize().map_err(|s| s.value)?;
        Ok(file.tokens.into_iter().map(|s| s.value).collect())
    }

    fn tokenize(input: &str) -> Vec<Token> {
        tokenize_result(input).expect("Lexing failed")
    }

    #[test]
    fn string_syntax_regression_plain_and_escaped_markers_remain_literals() {
        let tokens = tokenize(r#""$HOME $$ {name} \${name}""#);
        assert_eq!(
            tokens[0],
            Token::String {
                value: "$HOME $$ {name} ${name}".into(),
            }
        );
    }

    #[test]
    fn string_syntax_regression_matching_hashes_select_interpolation() {
        let tokens = tokenize(r###"##"${name} $#{name} $##{name}"##"###);
        assert!(tokens.iter().any(|token| matches!(token,
            Token::StringText { value } if value == "${name} $#{name} ")));
        assert_eq!(
            tokens
                .iter()
                .filter(|token| matches!(token, Token::StringInterpolationStart))
                .count(),
            1
        );
    }

    #[test]
    fn string_syntax_regression_raw_backslashes_are_not_decoded() {
        let tokens = tokenize(r##"#"C:\notes\file\"#"##);
        assert_eq!(
            tokens[0],
            Token::String {
                value: "C:\\notes\\file\\".into()
            }
        );
    }

    #[test]
    fn string_syntax_regression_multiline_strips_only_source_indentation() {
        let tokens = tokenize("\"\"\"\n    Hello\n      world\n    \"\"\"");
        assert_eq!(
            tokens[0],
            Token::String {
                value: "Hello\n  world".into()
            }
        );
    }

    #[test]
    fn interpolation_is_recognized_before_decoding_source_escapes() {
        for (source, expected) in [
            (r#""\u{24}{name}""#, "${name}"),
            (r#""$\u{7b}name}""#, "${name}"),
            (r#""\${name}""#, "${name}"),
            (
                r##"#"${name} $##{name} \n \u{24}"#"##,
                "${name} $##{name} \\n \\u{24}",
            ),
            (r#""$HOME $$ {} }} {{""#, "$HOME $$ {} }} {{"),
        ] {
            assert_eq!(
                tokenize(source)[0],
                Token::String {
                    value: expected.into()
                },
                "{source}"
            );
        }
        let tokens = tokenize(r#""Cost: $${amount}""#);
        assert_eq!(
            tokens[1],
            Token::StringText {
                value: "Cost: $".into()
            }
        );
    }

    #[test]
    fn raw_delimiters_and_interpolation_match_arbitrary_hash_counts() {
        for count in 1..=16 {
            let hashes = "#".repeat(count);
            let source =
                format!("{hashes}\"literal \\\" ${{x}} $#{hashes}{{x}} ${hashes}{{x}}\"{hashes}");
            let tokens = tokenize(&source);
            assert_eq!(
                tokens
                    .iter()
                    .filter(|token| matches!(token, Token::StringInterpolationStart))
                    .count(),
                1,
                "{source}"
            );
            assert!(
                tokens
                    .iter()
                    .any(|token| matches!(token, Token::Identifier { value } if value == "x"))
            );
        }
        assert_eq!(
            tokenize(r###"##"a "# b"##"###)[0],
            Token::String {
                value: "a \"# b".into()
            }
        );
    }

    #[test]
    fn long_hash_delimiters_and_malformed_prefixes_do_not_require_backtracking() {
        let hashes = "#".repeat(4096);
        let content = "$\"".repeat(4096);
        let source = format!("{hashes}\"{content}\"{hashes}");
        assert_eq!(tokenize(&source)[0], Token::String { value: content });
        for source in [hashes.clone(), format!("{hashes}notAString")] {
            assert!(matches!(
                tokenize_result(&source),
                Err(LexerError::InvalidCharacter('#'))
            ));
        }
        // Existing hash directives still use the ordinary token path.
        assert_eq!(tokenize("#cfg")[0], Token::Hash);
    }

    #[test]
    fn raw_interpolation_uses_normal_lexing_for_inner_strings() {
        let tokens = tokenize(r###"#"\$#{"\n"} $#{#"\t"#}"#"###);
        let literals: Vec<_> = tokens
            .iter()
            .filter_map(|token| match token {
                Token::String { value } => Some(value.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(literals, ["\n", "\\t"]);
        assert!(
            tokens
                .iter()
                .any(|token| matches!(token, Token::StringText { value } if value == "\\"))
        );
    }

    #[test]
    fn empty_and_comment_only_interpolations_are_errors() {
        for source in [
            r#""${}""#,
            r#""${ /* } */ }""#,
            "\"\"\"\n${\n// empty\n}\n\"\"\"",
        ] {
            assert!(
                matches!(
                    tokenize_result(source),
                    Err(LexerError::EmptyStringInterpolation)
                ),
                "{source}"
            );
        }
        assert!(tokenize_result(r#""${""}""#).is_ok());
    }

    #[test]
    fn multiline_layout_preserves_blank_lines_tabs_and_escape_values() {
        for (source, expected) in [
            ("\"\"\"\n\"\"\"", ""),
            ("\"\"\"\n    \n    \"\"\"", ""),
            ("\"\"\"\n    \n    x  \n\n    \"\"\"", "\nx  \n"),
            ("\"\"\"\n\tx\n\t  y\n\t\"\"\"", "x\n  y"),
            ("\"\"\"\n    \\n\\t\n    \"\"\"", "\n\t"),
            ("#\"\"\"\n    \\n\\t\n    \"\"\"#", "\\n\\t"),
        ] {
            assert_eq!(
                tokenize(source)[0],
                Token::String {
                    value: expected.into()
                },
                "{source}"
            );
            assert_eq!(tokenize(source), tokenize(&source.replace('\n', "\r\n")));
        }
    }

    #[test]
    fn multiline_indentation_is_validated_even_before_an_expression() {
        for source in [
            "\"\"\"\n  short\n    \"\"\"",
            "\"\"\"\n  ${x}\n    \"\"\"",
            "\"\"\"\n\tx\n    \"\"\"",
        ] {
            assert!(
                matches!(
                    tokenize_result(source),
                    Err(LexerError::MultilineStringIndentation)
                ),
                "{source}"
            );
        }
        assert!(matches!(
            tokenize_result("\"\"\"inline\"\"\""),
            Err(LexerError::MultilineStringOpening)
        ));
        assert!(matches!(
            tokenize_result("\"\"\"\ntext\"\"\""),
            Err(LexerError::MultilineStringClosing)
        ));
        assert!(matches!(
            tokenize_result("\"a\\\nb\""),
            Err(LexerError::StringLineContinuation)
        ));
        assert!(matches!(
            tokenize_result(r#"f"old""#),
            Err(LexerError::ObsoleteStringPrefix)
        ));
    }

    #[test]
    fn multiline_expression_lines_are_not_literal_indentation() {
        let source = "\"\"\"\n    before ${\n1 +\n2\n} after\n    \"\"\"";
        let tokens = tokenize(source);
        let text: Vec<_> = tokens
            .iter()
            .filter_map(|token| match token {
                Token::StringText { value } => Some(value.as_str()),
                _ => None,
            })
            .collect();
        assert_eq!(text, ["before ", " after"]);
        let end = tokens
            .iter()
            .position(|token| matches!(token, Token::StringInterpolationEnd))
            .unwrap();
        assert!(!matches!(tokens[end - 1], Token::Semicolon));
    }

    #[test]
    fn test_keywords() {
        let input = "func let if else return";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Function,
                Token::Let,
                Token::If,
                Token::Else,
                Token::Return,
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_operators() {
        let input = "+ - * / %";
        let tokens = tokenize(input);

        let expected = vec![
            Token::Plus,
            Token::Minus,
            Token::Star,
            Token::Quotient,
            Token::Modulus,
            Token::EOF,
        ];

        assert_eq!(tokens, expected);
    }

    #[test]
    fn test_punctuation_combinations() {
        // Test ambiguity like .. vs ..= vs .
        let input = ".. ..= . ...";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::DotDot,
                Token::DotDotEq,
                Token::Dot,
                Token::Ellipsis,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_literals_integers() {
        let input = "123 0xFF 0b101 0o77";
        let tokens = tokenize(input);
        // 0o77 is Octal 77
        assert_eq!(
            tokens,
            vec![
                Token::Integer {
                    value: "123".into(),
                    base: Base::Decimal,
                    suffix: None,
                },
                Token::Integer {
                    value: "0xFF".into(),
                    base: Base::Hexadecimal,
                    suffix: None,
                },
                Token::Integer {
                    value: "0b101".into(),
                    base: Base::Binary,
                    suffix: None,
                },
                Token::Integer {
                    value: "0o77".into(),
                    base: Base::Octal,
                    suffix: None,
                },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_literals_integers_with_type_suffixes() {
        let input = "1_u32 200_i64 7_U8 9_I16";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Integer {
                    value: "1_".into(),
                    base: Base::Decimal,
                    suffix: Some(IntegerTypeSuffix::U32),
                },
                Token::Integer {
                    value: "200_".into(),
                    base: Base::Decimal,
                    suffix: Some(IntegerTypeSuffix::I64),
                },
                Token::Integer {
                    value: "7_".into(),
                    base: Base::Decimal,
                    suffix: Some(IntegerTypeSuffix::U8),
                },
                Token::Integer {
                    value: "9_".into(),
                    base: Base::Decimal,
                    suffix: Some(IntegerTypeSuffix::I16),
                },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_invalid_integer_suffix() {
        let error = tokenize_result("1_i128").expect_err("expected lexing to fail");
        assert!(matches!(error, LexerError::InvalidIntegerLiteral));
    }

    #[test]
    fn test_literals_floats() {
        let input = "1.0 0.5 10e-5";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Float {
                    value: "1.0".into(),
                    base: Base::Decimal
                },
                Token::Float {
                    value: "0.5".into(),
                    base: Base::Decimal
                },
                Token::Float {
                    value: "10e-5".into(),
                    base: Base::Decimal
                },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_literals_strings() {
        let input = r#""hello" "escaped \" quote""#;
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::String {
                    value: "hello".into()
                },
                Token::String {
                    value: "escaped \" quote".into()
                },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_string_ending_with_escaped_quote() {
        let input = r#""\"" "before\"""#;
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::String { value: "\"".into() },
                Token::String {
                    value: "before\"".into()
                },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_literals_string_interpolation_basic() {
        let input = r#""hello, ${name}""#;
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::InterpolatedStringStart,
                Token::StringText {
                    value: "hello, ".into()
                },
                Token::StringInterpolationStart,
                Token::Identifier {
                    value: "name".into()
                },
                Token::StringInterpolationEnd,
                Token::InterpolatedStringEnd,
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn interpolation_zero_at_end_of_expression() {
        let input = r#""${a + 0}""#;
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::InterpolatedStringStart,
                Token::StringInterpolationStart,
                Token::Identifier { value: "a".into() },
                Token::Plus,
                Token::Integer {
                    value: "0".into(),
                    base: Base::Decimal,
                    suffix: None,
                },
                Token::StringInterpolationEnd,
                Token::InterpolatedStringEnd,
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_braces_do_not_require_escaping() {
        assert_eq!(
            tokenize(r#""{ok}""#),
            vec![
                Token::String {
                    value: "{ok}".into()
                },
                Token::Semicolon,
                Token::EOF
            ]
        );
    }

    #[test]
    fn test_literals_string_interpolation_nested_braces_in_expression() {
        let input = r#""value=${Point { x: 1 }}""#;
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::InterpolatedStringStart,
                Token::StringText {
                    value: "value=".into()
                },
                Token::StringInterpolationStart,
                Token::Identifier {
                    value: "Point".into()
                },
                Token::LBrace,
                Token::Identifier { value: "x".into() },
                Token::Colon,
                Token::Integer {
                    value: "1".into(),
                    base: Base::Decimal,
                    suffix: None,
                },
                Token::RBrace,
                Token::StringInterpolationEnd,
                Token::InterpolatedStringEnd,
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_string_interpolation_nested_interpolation_uses_normal_lexing() {
        let tokens = tokenize(r#""${"${"}"}"}""#);
        assert_eq!(
            tokens,
            vec![
                Token::InterpolatedStringStart,
                Token::StringInterpolationStart,
                Token::InterpolatedStringStart,
                Token::StringInterpolationStart,
                Token::String { value: "}".into() },
                Token::StringInterpolationEnd,
                Token::InterpolatedStringEnd,
                Token::StringInterpolationEnd,
                Token::InterpolatedStringEnd,
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn string_interpolation_tokens_preserve_original_source_spans() {
        let input = r#""${'{' /* } */ + `}` }""#;
        let file = Lexer::new(input, FileID::from_raw(0)).tokenize().unwrap();
        for (snippet, token) in [
            ("'{'", Token::Rune { value: "{".into() }),
            ("+", Token::Plus),
            ("`}`", Token::Identifier { value: "}".into() }),
        ] {
            let actual = file.tokens.iter().find(|item| item.value == token).unwrap();
            let offset = input.find(snippet).unwrap();
            assert_eq!(actual.span.start, Position { line: 0, offset });
            assert_eq!(
                actual.span.end,
                Position {
                    line: 0,
                    offset: offset + snippet.len()
                }
            );
        }
    }

    #[test]
    fn string_interpolation_newline_error_stops_before_newline() {
        for input in [
            "\"${\"unterminated\n}\"}",
            "\"${/* unterminated\n}\"}",
            "\"${`unterminated\n}\"}",
            "\"${'\n'}\"",
        ] {
            let error = Lexer::new(input, FileID::from_raw(0))
                .tokenize()
                .err()
                .unwrap();
            assert!(matches!(
                error.value,
                LexerError::UnterminatedStringInterpolation
            ));
            assert_eq!(error.span.start, Position { line: 0, offset: 1 });
            assert_eq!(
                error.span.end,
                Position {
                    line: 0,
                    offset: input.find('\n').unwrap()
                }
            );
        }
    }

    #[test]
    fn test_string_interpolation_empty_interpolation_error() {
        let error = tokenize_result(r#""${}""#).expect_err("expected lexing to fail");
        assert!(matches!(error, LexerError::EmptyStringInterpolation));
    }

    #[test]
    fn unmatched_braces_are_literal_text() {
        assert_eq!(
            tokenize(r#""{ok} }} {{""#)[0],
            Token::String {
                value: "{ok} }} {{".into()
            }
        );
    }

    #[test]
    fn test_string_interpolation_unterminated_interpolation_error() {
        let error = tokenize_result(r#""${name"}"#).expect_err("expected lexing to fail");
        assert!(matches!(error, LexerError::UnterminatedStringInterpolation));
    }

    #[test]
    fn test_literals_runes() {
        let input = "'a' '\\n'";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Rune { value: "a".into() },
                Token::Rune {
                    value: "\\n".into()
                },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_comments() {
        let input = "
        // single line
        /* multi
           line */
        123
        ";
        let tokens = tokenize(input);

        // Comments are skipped by the lexer

        let expected = vec![
            Token::Integer {
                value: "123".into(),
                base: Base::Decimal,
                suffix: None,
            },
            Token::Semicolon,
            Token::EOF,
        ];

        assert_eq!(tokens, expected);
    }

    #[test]
    fn nested_comments_balance_delimiters_and_preserve_asi() {
        assert_eq!(
            tokenize("1 /* outer /* inner */\n tail */ 2"),
            tokenize("1\n2")
        );
        assert_eq!(tokenize("/* \" /* */ \" */ 42"), tokenize("42"));
        assert_eq!(
            tokenize("\"${1 /* outer /* inner */ tail */ + 2}\""),
            tokenize("\"${1 + 2}\"")
        );
        let deeply_nested = format!("{}{}42", "/*".repeat(2048), "*/".repeat(2048));
        assert_eq!(tokenize(&deeply_nested), tokenize("42"));
    }

    #[test]
    fn nested_comments_require_every_closing_delimiter() {
        for source in ["/* outer /* inner */", "/* /* */ /* */", "/*/"] {
            assert!(
                matches!(
                    tokenize_result(source),
                    Err(LexerError::UnterminatedMultilineComment)
                ),
                "{source}"
            );
        }
    }

    #[test]
    fn crlf_preserves_tokens_spans_and_lexical_errors() {
        let file = FileID::new(0);
        for source in [
            "//+cfg family(\"unix\")\nlet x = 'é'\n/* comment\nline */\nx\n",
            "func main() {\n let s = \"${42}\"\n}\n",
            "\"first\nsecond\"",
            "\"${1\n}\"",
            "`first\nsecond`",
        ] {
            let lf = Lexer::new(source, file).tokenize().map(|f| f.tokens);
            let crlf = Lexer::new(&source.replace('\n', "\r\n"), file)
                .tokenize()
                .map(|f| f.tokens);
            assert_eq!(format!("{lf:?}"), format!("{crlf:?}"), "{source}");
        }
    }

    #[test]
    fn crlf_normalization_is_single_pass_and_bare_cr_is_whitespace() {
        let lexer = Lexer::new("\r\r\n\n", FileID::new(0));
        assert_eq!(lexer.source, vec!['\r', '\n', '\n']);
        assert_eq!(tokenize("let\rx\r=\r1"), tokenize("let x = 1"));
        assert_eq!(tokenize("1\r\n2\n3"), tokenize("1\n2\n3"));
    }

    #[test]
    fn test_asi_basic() {
        let input = "
        return
        return
        ";

        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Return,
                Token::Semicolon,
                Token::Return,
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_asi_skip_continuation() {
        let input = "
        a
        + b
        ";

        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Identifier { value: "a".into() },
                Token::Plus,
                Token::Identifier { value: "b".into() },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_asi_line_continuations() {
        let input = "
        a
        + b
        - c
        / d
        % e
        | f
        ^ g
        || h
        && i
        == j
        != k
        < l
        > m
        <= n
        >= o
        << p
        >> q
        . r
        |> t
        ?? u
        ";

        let semi_count = tokenize(input)
            .iter()
            .filter(|t| matches!(t, Token::Semicolon))
            .count();
        assert_eq!(semi_count, 1, "Should only have one semicolon at the end");
    }

    #[test]
    fn test_asi_open_ended_ranges() {
        // Postfix `start..` ends a statement at newline so the next line does not become RHS.
        let tokens = tokenize("r := start..\nnextCall()\n");
        assert_eq!(
            tokens,
            vec![
                Token::Identifier { value: "r".into() },
                Token::ColonEq,
                Token::Identifier {
                    value: "start".into()
                },
                Token::DotDot,
                Token::Semicolon,
                Token::Identifier {
                    value: "nextCall".into()
                },
                Token::LParen,
                Token::RParen,
                Token::Semicolon,
                Token::EOF,
            ]
        );

        // Leading `..end` and `..=end` do not continue the previous line.
        let tokens = tokenize("a\n..b\n..=c\n");
        assert_eq!(
            tokens,
            vec![
                Token::Identifier { value: "a".into() },
                Token::Semicolon,
                Token::DotDot,
                Token::Identifier { value: "b".into() },
                Token::Semicolon,
                Token::DotDotEq,
                Token::Identifier { value: "c".into() },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_asi_not_continuations() {
        // & and * are NOT continuation starters (unary ambiguity)
        // so `a \n * b` -> `a; * b`
        let input = "
        a
        * b
        ";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Identifier { value: "a".into() },
                Token::Semicolon,
                Token::Star,
                Token::Identifier { value: "b".into() },
                Token::Semicolon,
                Token::EOF,
            ]
        );

        let input = "
        a
        & b
        ";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Identifier { value: "a".into() },
                Token::Semicolon,
                Token::Amp,
                Token::Identifier { value: "b".into() },
                Token::Semicolon,
                Token::EOF,
            ]
        );

        // ! and ~ are also not starters
        let input = "
        a
        ! b
        ";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Identifier { value: "a".into() },
                Token::Semicolon,
                Token::Bang,
                Token::Identifier { value: "b".into() },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_bang_in_requires_a_whole_word() {
        let ident = |value: &str| Token::Identifier {
            value: value.into(),
        };
        // `!` touching `in` is the negated membership operator.
        assert_eq!(
            tokenize("a !in b"),
            vec![ident("a"), Token::BangIn, ident("b"), Token::Semicolon, Token::EOF]
        );
        assert_eq!(
            tokenize("a!in b"),
            vec![ident("a"), Token::BangIn, ident("b"), Token::Semicolon, Token::EOF]
        );
        assert_eq!(
            tokenize("a !in(b)"),
            vec![
                ident("a"),
                Token::BangIn,
                Token::LParen,
                ident("b"),
                Token::RParen,
                Token::Semicolon,
                Token::EOF
            ]
        );
        // A space after `!` keeps postfix `!` followed by `in`.
        assert_eq!(
            tokenize("a! in b"),
            vec![ident("a"), Token::Bang, Token::In, ident("b"), Token::Semicolon, Token::EOF]
        );
        // Identifiers that begin with `in` stay identifiers.
        for name in ["inside", "index", "in_range", "in2"] {
            assert_eq!(
                tokenize(&format!("!{name}")),
                vec![Token::Bang, ident(name), Token::Semicolon, Token::EOF],
                "!{name}"
            );
        }
    }

    #[test]
    fn test_asi_optional_assignment_continues_the_line() {
        let input = "
        a
        ??= b
        ";
        assert_eq!(
            tokenize(input),
            vec![
                Token::Identifier { value: "a".into() },
                Token::QuestionQuestionEq,
                Token::Identifier { value: "b".into() },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_asi_bang_in_continues_the_line() {
        let input = "
        a
        !in b
        ";
        assert_eq!(
            tokenize(input),
            vec![
                Token::Identifier { value: "a".into() },
                Token::BangIn,
                Token::Identifier { value: "b".into() },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_asi_keywords_continuation() {
        // `as`, `as?`, `is`, and `in` ARE continuation starters
        let input = "
        a
        as b
        ";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Identifier { value: "a".into() },
                Token::As,
                Token::Identifier { value: "b".into() },
                Token::Semicolon,
                Token::EOF,
            ]
        );

        let input = "
        a
        as? b
        ";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Identifier { value: "a".into() },
                Token::As,
                Token::Question,
                Token::Identifier { value: "b".into() },
                Token::Semicolon,
                Token::EOF,
            ]
        );

        let input = "
        a
        is b
        ";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Identifier { value: "a".into() },
                Token::Is,
                Token::Identifier { value: "b".into() },
                Token::Semicolon,
                Token::EOF,
            ]
        );

        let input = "
        a
        in b
        ";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Identifier { value: "a".into() },
                Token::In,
                Token::Identifier { value: "b".into() },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    #[test]
    fn test_asi_control_flow() {
        // return, break, continue followed by newline SHOULD imply semicolon
        // return \n value -> return; value
        let input = "
        return
        value
        ";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Return,
                Token::Semicolon,
                Token::Identifier {
                    value: "value".into()
                },
                Token::Semicolon,
                Token::EOF,
            ]
        );

        let input = "
        break
        label
        ";
        let tokens = tokenize(input);
        assert_eq!(
            tokens,
            vec![
                Token::Break,
                Token::Semicolon,
                Token::Identifier {
                    value: "label".into()
                },
                Token::Semicolon,
                Token::EOF,
            ]
        );
    }

    /// Tokens after ASI, separated by spaces, without the trailing EOF.
    fn render(input: &str) -> String {
        let tokens = tokenize(input);
        let (eof, tokens) = tokens.split_last().unwrap();
        assert_eq!(*eof, Token::EOF);
        tokens
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(" ")
    }

    #[test]
    fn asi_else_on_a_new_line_continues_the_previous_line() {
        assert_eq!(
            render("if a {\n    b()\n}\nelse if c {\n    d()\n}\nelse {\n    e()\n}"),
            "if a { b ( ) ; } else if c { d ( ) ; } else { e ( ) ; } ;"
        );
        assert_eq!(
            render("guard value > 0\nelse { return }"),
            "guard value > 0 else { return } ;"
        );
    }

    #[test]
    fn asi_where_on_a_new_line_continues_the_previous_line() {
        assert_eq!(
            render("func largest[T](_ values: [T]) -> T\n    where T: Ord {\n    x\n}"),
            "func largest [ T ] ( _ values : [ T ] ) -> T where T : Ord { x ; } ;"
        );
        assert_eq!(
            render("for item in items\n    where item.enabled {\n}"),
            "for item in items where item . enabled { } ;"
        );
    }

    #[test]
    fn asi_brace_on_a_new_line_still_ends_the_previous_line() {
        // Only `else` and `where` were added; a leading `{` is unchanged.
        assert_eq!(
            render("func f() -> T\n    where T: Ord\n{\n}"),
            "func f ( ) -> T where T : Ord ; { } ;"
        );
        assert_eq!(render("if a {\n}\n{\n}"), "if a { } ; { } ;");
    }

    #[test]
    fn asi_does_not_insert_inside_parentheses_or_brackets() {
        assert_eq!(
            render("total := sum(\n    first,\n    second\n)"),
            "total := sum ( first , second ) ;"
        );
        assert_eq!(
            render("matrix := [\n    [1, 2, 3],\n    [4, 5, 6]\n]"),
            "matrix := [ [ 1 , 2 , 3 ] , [ 4 , 5 , 6 ] ] ;"
        );
        assert_eq!(
            render("value := table[\n    row\n]"),
            "value := table [ row ] ;"
        );
        assert_eq!(
            render("point := (\n    x,\n    y\n)"),
            "point := ( x , y ) ;"
        );
        // A missing comma is now the parser's to report, not a stray `;`.
        assert_eq!(render("f(\n    a\n    b\n)"), "f ( a b ) ;");
    }

    #[test]
    fn asi_inserts_inside_braces_nested_in_parentheses_or_brackets() {
        assert_eq!(
            render(
                "compute(\n    items.map(item => {\n        log(item)\n        item * 2\n    })\n)"
            ),
            "compute ( items . map ( item => { log ( item ) ; item * 2 ; } ) ) ;"
        );
        assert_eq!(
            render("[\n    match x {\n        case .a => 1\n        case .b => 2\n    }\n]"),
            "[ match x { case . a => 1 ; case . b => 2 ; } ] ;"
        );
    }

    #[test]
    fn asi_resumes_the_enclosing_rule_after_a_closing_delimiter() {
        assert_eq!(render("f(\n    a\n)\nb"), "f ( a ) ; b ;");
        assert_eq!(
            render("{\n    f(a)\n    [1].count\n}"),
            "{ f ( a ) ; [ 1 ] . count ; } ;"
        );
    }

    #[test]
    fn asi_keeps_explicit_semicolons_inside_brackets() {
        assert_eq!(render("[0; 20]"), "[ 0 ; 20 ] ;");
        assert_eq!(render("x: [uint8; 20]"), "x : [ uint8 ; 20 ] ;");
        // A newline no longer stands in for the repeat separator.
        assert_eq!(render("[0\n20]"), "[ 0 20 ] ;");
    }

    #[test]
    fn asi_inside_interpolations_is_unchanged() {
        // Interpolations in multi-line strings keep the brace rule...
        let tokens = tokenize("\"\"\"\n    ${ a\nb }\n    \"\"\"");
        assert_eq!(
            tokens
                .iter()
                .filter(|t| matches!(t, Token::Semicolon))
                .count(),
            2
        );
        // ...while a call inside one suppresses insertion, and an
        // interpolation inside a call argument returns to the call's rule.
        let tokens = tokenize("f(\n\"\"\"\n    ${ g(\na\n) }\n    \"\"\"\n)");
        assert_eq!(
            tokens
                .iter()
                .filter(|t| matches!(t, Token::Semicolon))
                .count(),
            1
        );
        assert_eq!(render("f(\n    \"${x}\"\n)"), render("f(\"${x}\")"));
    }

    #[test]
    fn asi_recovers_from_unbalanced_delimiters() {
        // An unclosed `(` stops suppressing at the `}` that closes its block.
        assert_eq!(
            render("{\n    f(a\n    b\n}\nc\nd"),
            "{ f ( a b } ; c ; d ;"
        );
        // A closer without an opener is ignored.
        assert_eq!(render("a)\nb\nc]\nd"), "a ) ; b ; c ] ; d ;");
        // End of file still inserts inside an unclosed delimiter.
        assert_eq!(render("f(a"), "f ( a ;");
    }

    #[test]
    fn test_all_keywords() {
        let keywords = vec![
            ("any", Token::Any),
            ("as", Token::As),
            ("is", Token::Is),
            ("break", Token::Break),
            ("case", Token::Case),
            ("const", Token::Const),
            ("continue", Token::Continue),
            ("defer", Token::Defer),
            ("else", Token::Else),
            ("enum", Token::Enum),
            ("export", Token::Export),
            ("extern", Token::Extern),
            ("false", Token::False),
            ("for", Token::For),
            ("func", Token::Function),
            ("guard", Token::Guard),
            ("if", Token::If),
            ("impl", Token::Impl),
            ("extend", Token::Extend),
            ("conform", Token::Conform),
            ("import", Token::Import),
            ("in", Token::In),
            ("interface", Token::Interface),
            ("let", Token::Let),
            ("loop", Token::Loop),
            ("match", Token::Match),
            ("mod", Token::Mod),
            ("mut", Token::Mut),
            ("namespace", Token::Namespace),
            ("nil", Token::Nil),
            ("operator", Token::Operator),
            ("private", Token::Private),
            ("internal", Token::Internal),
            ("public", Token::Public),
            ("return", Token::Return),
            ("readonly", Token::Readonly),
            ("static", Token::Static),
            ("struct", Token::Struct),
            ("true", Token::True),
            ("type", Token::Type),
            ("var", Token::Var),
            ("where", Token::Where),
            ("while", Token::While),
            ("unsafe", Token::Unsafe),
            // Reserved
            ("class", Token::Class),
            ("final", Token::Final),
            ("override", Token::Override),
            ("fileprivate", Token::FilePrivate),
            ("protected", Token::Protected),
            ("async", Token::Async),
            ("await", Token::Await),
            ("ref", Token::Ref),
            ("init", Token::Init),
            ("deinit", Token::Deinit),
        ];

        for (text, expected_token) in keywords {
            let tokens = tokenize(text);
            assert_eq!(
                tokens[0], expected_token,
                "Failed to tokenize keyword '{}'",
                text
            );
        }
    }

    #[test]
    fn test_all_punctuation() {
        let punctuation = vec![
            ("=", Token::Assign),
            ("+", Token::Plus),
            ("-", Token::Minus),
            ("*", Token::Star),
            ("/", Token::Quotient),
            ("%", Token::Modulus),
            ("&", Token::Amp),
            ("!", Token::Bang),
            ("~", Token::Tilde),
            ("<", Token::LChevron),
            (">", Token::RChevron),
            ("==", Token::Eql),
            ("!=", Token::Neq),
            ("<=", Token::Leq),
            (">=", Token::Geq),
            ("&&", Token::AmpAmp),
            ("||", Token::BarBar),
            (",", Token::Comma),
            (".", Token::Dot),
            (":", Token::Colon),
            ("::", Token::ColonColon),
            (":=", Token::ColonEq),
            ("(", Token::LParen),
            (")", Token::RParen),
            ("{", Token::LBrace),
            ("}", Token::RBrace),
            ("[", Token::LBracket),
            ("]", Token::RBracket),
            ("+=", Token::PlusEq),
            ("-=", Token::MinusEq),
            ("*=", Token::MulEq),
            ("/=", Token::DivEq),
            ("%=", Token::RemEq),
            ("&=", Token::AmpEq),
            ("|=", Token::BarEq),
            ("^=", Token::CaretEq),
            ("<<=", Token::ShlEq),
            (">>=", Token::ShrEq),
            ("|", Token::Bar),
            ("^", Token::Caret),
            (">>", Token::Shr),
            ("<<", Token::Shl),
            ("->", Token::RArrow),
            ("=>", Token::EqArrow),
            ("_", Token::Underscore),
            ("|>", Token::Pipe),
            ("?", Token::Question),
            ("?.", Token::QuestionDot),
            ("??", Token::QuestionQuestion),
            ("??=", Token::QuestionQuestionEq),
            ("!in", Token::BangIn),
            ("@", Token::At),
            ("...", Token::Ellipsis),
            ("..", Token::DotDot),
            ("..=", Token::DotDotEq),
            (".*", Token::DotStar),
        ];

        for (text, expected_token) in punctuation {
            let tokens = tokenize(text);
            assert_eq!(
                tokens[0], expected_token,
                "Failed to tokenize punctuation '{}'",
                text
            );
        }
    }
}
