use crate::{
    constants::{FILE_EXTENSION, ROOT_MODULE_NAME, SOURCE_DIRECTORY},
    diagnostics::DiagCtx,
    error::ReportedError,
    parse::token::{Base, Token},
    span::{FileID, Position, Span, Spanned},
};
use std::{
    ffi::OsStr,
    fs::{read_dir, read_to_string},
    path::PathBuf,
};

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

pub fn tokenize_package(path: PathBuf, dcx: &DiagCtx) -> Result<Pacakge, ReportedError> {
    let source = path.join(SOURCE_DIRECTORY);
    let mut root = tokenize_module(source, dcx)?;
    root.name = ROOT_MODULE_NAME.into();

    Ok(Pacakge { root })
}

/// Tokenize a single source file as a virtual package.
/// The file becomes the root module with name "main".
pub fn tokenize_single_file(path: PathBuf, dcx: &DiagCtx) -> Result<Pacakge, ReportedError> {
    let file_path = match path.canonicalize() {
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
    let file = match tokenize_file(id, file_path.clone(), dcx) {
        Ok(file) => file,
        Err(e) => {
            let message = format!("lexer error in file '{}': {}", file_path.display(), e);
            dcx.emit_error(message, None);
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

pub fn tokenize_module(path: PathBuf, dcx: &DiagCtx) -> Result<Module, ReportedError> {
    let directory = match path.canonicalize() {
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

    if name == ROOT_MODULE_NAME {
        let message = format!(
            "module cannot be named '{}' (reserved for root module)",
            ROOT_MODULE_NAME
        );
        dcx.emit_error(message, None);
        return Err(ReportedError);
    }

    let entries = match read_dir(&directory) {
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
        let entry = match entry {
            Ok(entry) => entry,
            Err(e) => {
                let message = format!(
                    "failed to read directory entry in '{}': {}",
                    directory.display(),
                    e
                );
                dcx.emit_error(message, None);
                return Err(ReportedError);
            }
        };

        let path = entry.path();
        if path.is_symlink() {
            continue;
        }

        if path.is_file() {
            if path.extension().unwrap_or(OsStr::new("")) != FILE_EXTENSION {
                continue;
            };
            let id = dcx.add_file_mapping(path.clone());
            let file = match tokenize_file(id, path.clone(), dcx) {
                Ok(file) => file,
                Err(e) => {
                    let message = format!("lexer error in file '{}': {}", path.display(), e);
                    dcx.emit_error(message, None);
                    return Err(ReportedError);
                }
            };
            files.push(file);
        } else if path.is_dir() {
            let module = tokenize_module(path.clone(), dcx)?;
            submodules.push(module);
        }
    }

    Ok(Module {
        files,
        submodules,
        name: name.into(),
    })
}

pub fn tokenize_file(file: FileID, path: PathBuf, dcx: &DiagCtx) -> Result<File, LexerError> {
    let source = match read_to_string(&path) {
        Ok(source) => source,
        Err(e) => {
            let message = format!("failed to read file '{}': {}", path.display(), e);
            dcx.emit_error(message.clone(), None);
            return Err(LexerError::IO(message));
        }
    };
    let lexer = Lexer::new(&source, file);
    lexer.tokenize()
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
        let source: Vec<char> = source.chars().collect();
        Lexer {
            anchor: Position { line: 0, offset: 0 },
            cursor: 0,
            line: 0,
            offset: 0,
            tokens: Vec::new(),
            source,
            file,
        }
    }
}

impl Lexer {
    pub fn tokenize(mut self) -> Result<File, LexerError> {
        while self.has_next() {
            self.anchor = self.position();
            let case = match self.next_token() {
                Ok(case) => case,
                Err(e) => {
                    return Err(e);
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
        // println!("Tokens: {:#?}", self.tokens);

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
            ' ' | '\t' | '\n' => return Ok(TokenCase::Skip),
            '(' => Token::LParen,
            ')' => Token::RParen,
            '[' => Token::LBracket,
            ']' => Token::RBracket,
            '{' => Token::LBrace,
            '}' => Token::RBrace,
            ';' => Token::Semicolon,
            ',' => Token::Comma,
            '@' => Token::At,
            '#' => Token::Hash,
            '~' => Token::Tilde,
            ':' => Token::Colon,
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
                    Token::Neq
                } else {
                    Token::Bang
                }
            }
            '=' => {
                if self.eat('=') {
                    if self.eat('=') {
                        Token::PtrEq
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
                    Token::QuestionQuestion
                } else if self.eat('.') {
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
            '"' => self.string()?,
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

// strings
impl Lexer {
    fn string(&mut self) -> Result<Token, LexerError> {
        let Some(content) = self.double_quoted_string()? else {
            return Err(LexerError::UnterminatedStringLiteral);
        };

        Ok(Token::String {
            value: content.into(),
        })
    }

    fn double_quoted_string(&mut self) -> Result<Option<String>, LexerError> {
        let lo = self.cursor;
        loop {
            match self.next_char() {
                Some('"') => {
                    let hi = self.cursor - 1;
                    return Ok(Some(self.read(lo, hi)));
                }
                Some('\\') if self.eat('\\') || self.eat('"') => {
                    self.next_char();
                }
                Some('\n') => return Err(LexerError::StringLiteralMustBeSingleLine),
                None => break,
                _ => {
                    continue;
                }
            };
        }

        Ok(None)
    }
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

    fn multi_line_comment(&mut self) -> Result<Token, LexerError> {
        let lo = self.cursor;

        // Scan until we see "*/" or run out of input.
        while self.has_next() {
            if self.first() == Some('*') && self.second() == Some('/') {
                let hi = self.cursor;
                let content: String = self.read(lo, hi);
                self.next_char(); // eat '*'
                self.next_char(); // eat '/'

                let token = Token::CommentDoc {
                    value: content.into(),
                };
                return Ok(token);
            }
            self.next_char();
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

                    let res = self.eat_decimal_digits();

                    if !res {
                        return Err(LexerError::InvalidIntegerLiteral);
                    }
                }
                Some('o') => {
                    base = Base::Octal;
                    self.next_char();

                    let res = self.eat_decimal_digits();

                    if !res {
                        return Err(LexerError::InvalidIntegerLiteral);
                    }
                }
                Some('x') => {
                    base = Base::Hexadecimal;
                    self.next_char();

                    let res = self.eat_hex_digits();

                    if !res {
                        return Err(LexerError::InvalidIntegerLiteral);
                    }
                }
                Some(c) => match c {
                    '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' | '_' => {
                        self.eat_decimal_digits();
                    }
                    '.' | 'e' | 'E' => {
                        // these will be handled in the next half
                    }
                    _ => {
                        // just a 0
                        return Ok(Token::Integer {
                            value: content(self).into(),
                            base,
                        });
                    }
                },
                None => {
                    return Err(LexerError::InvalidIntegerLiteral);
                }
            }
        } else {
            self.eat_decimal_digits();
        }

        match self.first() {
            Some('.') => {
                let sec = self.second();
                // eat decimal point, avoid range expr
                if sec != None && sec != Some('.') && !Lexer::is_letter(sec.unwrap()) {
                    self.next_char();
                    let mut empty = false;

                    if self.first() != None && Lexer::is_digit(self.first().unwrap()) {
                        self.eat_decimal_digits();

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

        return Ok(Token::Integer {
            value: content(self).into(),
            base,
        });
    }
}

impl Lexer {
    fn eat_decimal_digits(&mut self) -> bool {
        let mut has_digits = false;

        loop {
            match self.first() {
                Some(c) if c == '_' => {
                    self.next_char();
                }
                Some(c) if Lexer::is_digit(c) => {
                    has_digits = true;
                    self.next_char();
                }
                _ => break,
            }
        }

        has_digits
    }

    fn eat_hex_digits(&mut self) -> bool {
        let mut has_digits = false;

        loop {
            match self.first() {
                Some(c) if c == '_' => {
                    self.next_char();
                }
                Some(c) if Lexer::is_hex_char(c) => {
                    has_digits = true;
                    self.next_char();
                }
                _ => break,
            }
        }

        has_digits
    }
    fn eat_float_exponents(&mut self) -> bool {
        if self.eat('-') || self.eat('+') {
            // sign already consumed
        }

        self.eat_decimal_digits()
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
        "import" => Token::Import,
        "in" => Token::In,
        "init" => Token::Init,
        "interface" => Token::Interface,
        "let" => Token::Let,
        "loop" => Token::Loop,
        "match" => Token::Match,
        "namespace" => Token::Namespace,
        "nil" => Token::Nil,
        "operator" => Token::Operator,
        "private" => Token::Private,
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
    #[allow(unused)]
    InvalidCharacter(char),
    UnterminatedMultilineComment,
    UnterminatedEscapedIdentifier,
    UnterminatedRuneLiteral,
    UnterminatedStringLiteral,
    StringLiteralMustBeSingleLine,
    EscapeIdentifierMustBeSingleLine,
    InvalidIntegerLiteral,
    InvalidFloatLiteral,
    IO(String),
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
            LexerError::StringLiteralMustBeSingleLine => {
                write!(f, "string literals must be on a single line")
            }
            LexerError::EscapeIdentifierMustBeSingleLine => {
                write!(f, "escaped identifiers must be on a single line")
            }
            LexerError::InvalidIntegerLiteral => write!(f, "invalid integer literal"),
            LexerError::InvalidFloatLiteral => write!(f, "invalid float literal"),
            LexerError::IO(msg) => write!(f, "{}", msg),
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
/// - **Unless** the next non-comment token is a line-continuation starter
///   (an operator/connector like `+`, `-`, `*`, `.`, `..`, `==`, `=`, `|>`, etc.).
pub fn automatic_semicolon_insertion(tokens: Vec<Spanned<Token>>) -> Vec<Spanned<Token>> {
    use crate::span::{Span, Spanned};

    if tokens.is_empty() {
        return tokens;
    }

    let mut out = Vec::with_capacity(tokens.len() + 8);
    let len = tokens.len();
    let mut i = 0usize;

    while i < len {
        let cur = tokens[i].clone();
        let cur_can_end = can_end_statement(&cur.value);

        // Find the next non-comment token.
        let mut j = i + 1;
        while j < len && is_comment(&tokens[j].value) {
            j += 1;
        }
        let next_opt = tokens.get(j);

        // Decide if we should insert a semicolon after `cur`.
        let mut should_insert = false;
        if cur_can_end {
            match next_opt {
                Some(next_spanned) => {
                    let next_is_eof = is_eof(&next_spanned.value);
                    let has_newline = next_spanned.span.start.line > cur.span.end.line;

                    // Only consider inserting on newline or before EOF.
                    if next_is_eof {
                        should_insert = true;
                    } else if has_newline {
                        // Suppress insertion for operator-leading continuation lines.
                        if !is_line_continuation_starter(&next_spanned.value) {
                            should_insert = true;
                        }
                    }
                }
                None => {
                    // No next token at all: be conservative and terminate the statement.
                    should_insert = true;
                }
            }
        }

        out.push(cur.clone());

        if should_insert {
            let pos = cur.span.end;
            let semi_span = Span {
                start: pos,
                end: pos,
                file: cur.span.file,
            };
            out.push(Spanned::new(Token::Semicolon, semi_span));
        }

        i += 1;
    }

    out
}

fn can_end_statement(tok: &Token) -> bool {
    match tok {
        // primaries / identifiers / literals
        Token::Identifier { .. }
        | Token::Integer { .. }
        | Token::Float { .. }
        | Token::Rune { .. }
        | Token::String { .. }
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
        | Token::Bang => true,
        _ => false,
    }
}

fn is_comment(tok: &Token) -> bool {
    matches!(tok, Token::CommentDoc { .. })
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
        Plus | Minus | Quotient | Modulus
        | Caret | Bar
        | AmpAmp | BarBar
        // relational / equality
        | LChevron | RChevron | Leq | Geq | Eql | Neq | PtrEq
        // shifts
        | Shl | Shr
        // assignment family (leading assignment style)
        | Assign | PlusEq | MinusEq | MulEq | DivEq | RemEq
        | ShlEq | ShrEq | CaretEq | AmpEq | BarEq | DotDotEq
        // range / member / optional chaining
        | Dot | DotDot | Ellipsis | QuestionDot
        // nullish / pipe
        | QuestionQuestion | Pipe
        // arrows can lead a continuation (e.g., in patterns or lambdas)
        | RArrow | EqArrow
        // casting / infix-like keywords that glue to the previous expr
        | As | In
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::token::Token;

    fn tokenize(input: &str) -> Vec<Token> {
        let dcx = DiagCtx::new(PathBuf::from("."));
        // We use a dummy file ID, effectively ignoring it for these unit tests.
        let file_id = dcx.add_file_mapping(PathBuf::from("test.taro"));
        let lexer = Lexer::new(input, file_id);

        let file = lexer.tokenize().expect("Lexing failed");
        file.tokens.into_iter().map(|s| s.value).collect()
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
                    base: Base::Decimal
                },
                Token::Integer {
                    value: "0xFF".into(),
                    base: Base::Hexadecimal
                },
                Token::Integer {
                    value: "0b101".into(),
                    base: Base::Binary
                },
                Token::Integer {
                    value: "0o77".into(),
                    base: Base::Octal
                },
                Token::Semicolon,
                Token::EOF,
            ]
        );
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
                    value: r#"escaped \" quote"#.into()
                },
                Token::Semicolon,
                Token::EOF,
            ]
        );
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
            },
            Token::Semicolon,
            Token::EOF,
        ];

        assert_eq!(tokens, expected);
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
        .. s
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
    fn test_asi_keywords_continuation() {
        // `as` and `in` ARE continuation starters
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
    #[test]
    fn test_all_keywords() {
        let keywords = vec![
            ("any", Token::Any),
            ("as", Token::As),
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
            ("import", Token::Import),
            ("in", Token::In),
            ("interface", Token::Interface),
            ("let", Token::Let),
            ("loop", Token::Loop),
            ("match", Token::Match),
            ("mut", Token::Mut),
            ("namespace", Token::Namespace),
            ("nil", Token::Nil),
            ("operator", Token::Operator),
            ("private", Token::Private),
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
            ("===", Token::PtrEq),
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
