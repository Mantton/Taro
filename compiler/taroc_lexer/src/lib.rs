#![feature(iterator_try_collect)]
use std::{ffi::OsStr, fs::read_dir};
use taroc_constants::{FILE_EXTENSION, SOURCE_DIRECTORY};
use taroc_error::{CompileError, CompileResult};
use taroc_sema::GlobalContext;
use taroc_span::{FileID, Position, Span, SpannedMessage, Symbol, with_session_globals};
use taroc_token::{Base, Token, TokenKind};

type Gcx<'a> = GlobalContext<'a>;
type CR<T> = CompileResult<T>;
#[derive(Debug)]
pub struct Package {
    pub root: Module,
}

#[derive(Debug)]
pub struct Module {
    pub name: Symbol,
    pub files: Vec<File>,
    pub submodules: Vec<Module>,
}

#[derive(Debug)]
pub struct File {
    pub file: FileID,
    pub tokens: Vec<Token>,
}

pub fn tokenize_package(context: GlobalContext) -> CompileResult<Package> {
    let source = &context.session().config.source_path;
    let source = source.join(SOURCE_DIRECTORY);
    let root = tokenize_module(&source, true, context)?;
    if context.diagnostics.has_errors() {
        Err(CompileError::Reported)
    } else {
        Ok(Package { root })
    }
}

pub fn tokenize_module(
    directory: &std::path::Path,
    is_root: bool,
    context: GlobalContext,
) -> CompileResult<Module> {
    let directory = match directory.canonicalize() {
        Ok(dir) => dir,
        Err(err) => {
            return Err(CompileError::Message(format!(
                "failed to read directory: {}",
                err
            )));
        }
    };

    let name = if !is_root {
        let name = directory
            .file_name()
            .and_then(|name| name.to_str())
            .map(|s| s.to_string());
        match name {
            Some(name) => name,
            None => {
                return Err(CompileError::Message(format!(
                    "failed to read direcotry name from: {:?}",
                    directory
                )));
            }
        }
    } else {
        "__package__root__".into()
    };

    let content = match read_dir(&directory) {
        Ok(contents) => contents,
        Err(err) => {
            return Err(CompileError::Message(format!(
                "failed to read directory: {}",
                err
            )));
        }
    };

    let mut files = vec![];
    let mut submodules = vec![];
    for entry in content {
        let entry = match entry {
            Ok(entry) => entry,
            Err(err) => {
                return Err(CompileError::Message(format!(
                    "failed to read directory entry: {}",
                    err
                )));
            }
        };

        let path = entry.path();

        if path.is_file() {
            if path.extension().unwrap_or(OsStr::new("")) != FILE_EXTENSION {
                continue;
            };

            // Register File in Source Map
            let id = with_session_globals(|session| session.tag_file(path));
            files.push(id);
        } else if path.is_dir() {
            let module = tokenize_module(&path, false, context)?;
            submodules.push(module);
        }
    }

    let files = files
        .into_iter()
        .map(|file| tokenize_file(file, context))
        .try_collect()?;

    Ok(Module {
        name: Symbol::with(&name),
        files,
        submodules,
    })
}

pub fn tokenize_file(source: FileID, context: Gcx) -> CR<File> {
    with_session_globals(|session| {
        let file = session.get_file(source);
        let content = file.content()?;
        let lexer = Lexer::new(&content, source);
        match lexer.tokenize() {
            Ok(file) => Ok(file),
            Err(err) => {
                context.diagnostics.error(err.message, err.span);
                Err(CompileError::Reported)
            }
        }
    })
}

type LR<T> = Result<T, SpannedMessage>;

pub struct Lexer {
    source: Vec<char>,
    file: FileID,

    anchor: Position,
    cursor: usize,
    line: usize,
    offset: usize,
    tokens: Vec<Token>,
    lines: Vec<usize>,
}

impl Lexer {
    pub fn new(source: &str, file: FileID) -> Lexer {
        let mut lines = vec![];
        let mut start = 0;
        let source: Vec<char> = source.chars().collect();

        // Iterate over the string's characters with their byte indices.
        for (i, c) in source.iter().enumerate() {
            if *c == '\n' {
                // Push the current line slice and its starting index.
                lines.push(start);
                // Set the start of the next line to be after the newline character.
                start = i + c.len_utf8();
            }
        }
        // Add the last line (if the string doesn't end with a newline)
        if start <= source.len() {
            lines.push(start);
        }

        Lexer {
            anchor: Position { line: 0, offset: 0 },
            cursor: 0,
            line: 0,
            offset: 0,
            tokens: Vec::new(),

            source,
            file,
            lines,
        }
    }
}

impl Lexer {
    pub fn tokenize(mut self) -> LR<File> {
        while self.has_next() {
            self.anchor = self.position();
            let token = self.token()?;

            match token {
                Some(token) => {
                    if !matches!(token.kind, TokenKind::Whitespace) {
                        self.tokens.push(token);
                    }
                }
                None => break,
            }
        }

        self.tokens.push(Token {
            kind: TokenKind::Eof,
            span: Span::empty(self.file),
            content: Span::empty(self.file),
        });

        Ok(File {
            tokens: self.tokens,
            file: self.file,
        })
    }
}

impl Lexer {
    fn has_next(&self) -> bool {
        self.cursor < self.source.len()
    }

    fn position(&self) -> Position {
        Position {
            line: self.line,
            offset: self.offset,
        }
    }

    fn anchored_span(&self) -> Span {
        Span {
            start: self.anchor,
            end: self.position(),
            file: self.file,
        }
    }

    fn position_span(&self) -> Span {
        Span {
            start: self.position(),
            end: self.position(),
            file: self.file,
        }
    }

    pub fn read(&self, span: &Span) -> String {
        let source_count = self.source.len();
        // 2) Convert (line, offset) -> absolute index in `content`.
        //    Make sure we don’t go out of range if `span.line` exceeds the number of lines we found.
        let start_line_index = self
            .lines
            .get(span.start.line)
            .cloned()
            .unwrap_or(source_count); // fallback if line is out of range
        let end_line_index = self
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
            self.source[abs_start..abs_end].iter().collect()
        } else {
            String::new()
        };

        string
    }

    fn build(&self, kind: TokenKind) -> Token {
        let span = self.anchored_span();
        Token::new(kind, span, span)
    }

    fn build_with_content_span(&self, kind: TokenKind, content: Span) -> Token {
        let span = self.anchored_span();
        Token::new(kind, span, content)
    }
}

impl Lexer {
    fn next(&mut self) -> Option<char> {
        let c = self.source.get(self.cursor).cloned();
        self.cursor += 1;
        self.offset += 1;

        if c == Some('\n') {
            self.line += 1;
            self.offset = 0;
        }

        c
    }

    fn matches(&mut self, c: char) -> bool {
        if !self.has_next() {
            return false;
        }

        match self.first() {
            Some(rs) if rs == c => {
                self.next();
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

impl Lexer {
    fn token(&mut self) -> LR<Option<Token>> {
        let Some(char) = self.next() else {
            return Ok(None);
        };

        let token = match char {
            ' ' | '\t' => self.build(TokenKind::Whitespace),
            '\n' => self.build(TokenKind::Newline),
            '(' => self.build(TokenKind::LParen),
            ')' => self.build(TokenKind::RParen),
            '[' => self.build(TokenKind::LBracket),
            ']' => self.build(TokenKind::RBracket),
            '{' => self.build(TokenKind::LBrace),
            '}' => self.build(TokenKind::RBrace),
            ';' => self.build(TokenKind::Semicolon),
            ',' => self.build(TokenKind::Comma),
            '@' => self.build(TokenKind::At),
            '.' => {
                if self.matches('.') {
                    let v = if self.matches('.') {
                        // ...
                        self.build(TokenKind::Ellipsis)
                    } else if self.matches('=') {
                        // ..=
                        self.build(TokenKind::DotDotEq)
                    } else {
                        // ..
                        self.build(TokenKind::DotDot)
                    };

                    v
                } else {
                    self.build(TokenKind::Dot)
                }
            }
            ':' => {
                if self.matches(':') {
                    self.build(TokenKind::Scope)
                } else {
                    self.build(TokenKind::Colon)
                }
            }
            '-' => {
                if self.matches('>') {
                    self.build(TokenKind::RArrow)
                } else if self.matches('=') {
                    self.build(TokenKind::MinusEq)
                } else {
                    self.build(TokenKind::Minus)
                }
            }
            '+' => {
                if self.matches('=') {
                    self.build(TokenKind::PlusEq)
                } else {
                    self.build(TokenKind::Plus)
                }
            }
            '*' => {
                if self.matches('=') {
                    self.build(TokenKind::MulEq)
                } else {
                    self.build(TokenKind::Star)
                }
            }
            '%' => {
                if self.matches('=') {
                    self.build(TokenKind::RemEq)
                } else {
                    self.build(TokenKind::Modulus)
                }
            }
            '!' => {
                if self.matches('=') {
                    self.build(TokenKind::Neq)
                } else {
                    self.build(TokenKind::Bang)
                }
            }
            '=' => {
                if self.matches('=') {
                    if self.matches('=') {
                        self.build(TokenKind::PtrEq)
                    } else {
                        self.build(TokenKind::Eql)
                    }
                } else if self.matches('>') {
                    self.build(TokenKind::EqArrow)
                } else {
                    self.build(TokenKind::Assign)
                }
            }
            '~' => {
                if self.matches('=') {
                    self.build(TokenKind::Teq)
                } else {
                    self.build(TokenKind::Tilde)
                }
            }
            '<' => {
                if self.matches('=') {
                    self.build(TokenKind::Leq)
                } else if self.matches('<') {
                    if self.matches('=') {
                        self.build(TokenKind::ShlEq)
                    } else {
                        self.build(TokenKind::Shl)
                    }
                } else {
                    self.build(TokenKind::LChevron)
                }
            }
            '>' => {
                if self.matches('=') {
                    self.build(TokenKind::Geq)
                } else if self.matches('>') {
                    if self.matches('=') {
                        self.build(TokenKind::ShrEq)
                    } else {
                        self.build(TokenKind::Shr)
                    }
                } else {
                    self.build(TokenKind::RChevron)
                }
            }
            '?' => {
                if self.matches('?') {
                    self.build(TokenKind::QuestionQuestion)
                } else if self.matches('.') {
                    self.build(TokenKind::QuestionDot)
                } else {
                    self.build(TokenKind::Question)
                }
            }
            '^' => {
                if self.matches('=') {
                    self.build(TokenKind::CaretEq)
                } else {
                    self.build(TokenKind::Caret)
                }
            }
            '&' => {
                if self.matches('&') {
                    self.build(TokenKind::AmpAmp)
                } else if self.matches('=') {
                    self.build(TokenKind::AmpEq)
                } else {
                    self.build(TokenKind::Amp)
                }
            }
            '|' => {
                if self.matches('|') {
                    self.build(TokenKind::BarBar)
                } else if self.matches('>') {
                    self.build(TokenKind::Pipe)
                } else if self.matches('=') {
                    self.build(TokenKind::BarEq)
                } else {
                    self.build(TokenKind::Bar)
                }
            }
            '/' => {
                if self.matches('/') {
                    self.single_line_comment()
                } else if self.matches('*') {
                    self.multi_line_comment()?
                } else if self.matches('=') {
                    self.build(TokenKind::DivEq)
                } else {
                    self.build(TokenKind::Quotient)
                }
            }
            '_' => {
                if self.first() != None && Lexer::is_alphanumeric(self.first().unwrap_or_default())
                {
                    let k = self.identifier();
                    self.build(k)
                } else {
                    self.build(TokenKind::Underscore)
                }
            }
            '"' => {
                let token = self.string()?;
                return Ok(Some(token));
            }
            '`' => {
                let token = self.escaped_identifier()?;
                return Ok(Some(token));
            }
            '\'' => {
                let token = self.char()?;
                return Ok(Some(token));
            }
            _ => {
                if Lexer::is_digit(char) {
                    let k = self.number(char)?;
                    self.build(k)
                } else if Lexer::is_alphanumeric(char) {
                    let k = self.identifier();
                    self.build(k)
                } else {
                    return Err(SpannedMessage {
                        message: "invalid token".into(),
                        span: self.anchored_span(),
                    });
                }
            }
        };

        return Ok(Some(token));
    }
}

impl Lexer {
    fn single_line_comment(&mut self) -> Token {
        let lo = self.position();
        // slashes have already been parsed
        while self.first() != Some('\n') && self.has_next() {
            self.next();
        }

        let hi = self.position();
        self.build_with_content_span(TokenKind::SingleLineComment, lo.to(hi, self.file))
    }

    fn multi_line_comment(&mut self) -> LR<Token> {
        let lo = self.position();
        // iterate till the peek token is on the star and the upper token is on the closing slash
        while self.first() != Some('*') && self.second() != Some('/') && self.has_next() {
            self.next();
        }

        // valid match
        if self.has_next() && self.first() == Some('*') && self.second() == Some('/') {
            let hi = self.position();
            let span = lo.to(hi, self.file);
            self.next(); // eat star
            self.next(); // eat slash
            return Ok(self.build_with_content_span(TokenKind::MultiLineComment, span));
        } else {
            let message = SpannedMessage {
                message: "unterminated multiline comment".into(),
                span: self.position_span(),
            };
            return Err(message);
        }
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

impl Lexer {
    fn identifier(&mut self) -> TokenKind {
        // collect
        loop {
            match self.first() {
                Some(c) if Lexer::is_alphanumeric(c) => {
                    self.next();
                }
                _ => break,
            }
        }

        let content = self.read(&self.anchored_span());
        // check for keyword
        let kw = TokenKind::keyword(&content);

        kw.unwrap_or_else(|| TokenKind::Identifier)
    }

    fn escaped_identifier(&mut self) -> LR<Token> {
        let Some((kind, span)) = self.back_quote_string()? else {
            return Err(SpannedMessage {
                message: "unterminated template-string literal".into(),
                span: self.anchored_span(),
            });
        };

        return Ok(self.build_with_content_span(kind, span));
    }

    fn char(&mut self) -> LR<Token> {
        let Some((kind, span)) = self.single_quoted_string() else {
            return Err(SpannedMessage {
                message: "unterminated rune literal".into(),
                span: self.anchored_span(),
            });
        };

        Ok(self.build_with_content_span(kind, span))
    }

    fn string(&mut self) -> LR<Token> {
        let Some((kind, span)) = self.double_quoted_string()? else {
            return Err(SpannedMessage {
                message: "unterminated string literal".into(),
                span: self.anchored_span(),
            });
        };

        return Ok(self.build_with_content_span(kind, span));
    }
}

impl Lexer {
    fn eat_decimal_digits(&mut self) -> bool {
        let mut has_digits = false;

        loop {
            match self.first() {
                Some(c) if c == '_' => {
                    self.next();
                }
                Some(c) if Lexer::is_digit(c) => {
                    has_digits = true;
                    self.next();
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
                    self.next();
                }
                Some(c) if Lexer::is_hex_char(c) => {
                    has_digits = true;
                    self.next();
                }
                _ => break,
            }
        }

        has_digits
    }
    fn eat_float_exponents(&mut self) -> bool {
        if self.matches('-') || self.matches('+') {
            self.next();
        }

        self.eat_decimal_digits()
    }
}

impl Lexer {
    fn single_quoted_string(&mut self) -> Option<(TokenKind, Span)> {
        let lo = self.position();
        // Next points to char after initial quote
        // Is one-symbol literal
        if self.second() == Some('\'') && self.first() != Some('\\') {
            self.next(); // eat single char
            let hi = self.position();
            self.next(); // eat closing quote
            return Some((TokenKind::Rune, lo.to(hi, self.file)));
        }

        'PARENT: loop {
            match self.first() {
                Some('\'') => {
                    let hi = self.position();
                    self.next();
                    return Some((TokenKind::Rune, lo.to(hi, self.file)));
                }
                Some('/') => break 'PARENT,
                Some('\n') => {
                    if self.second() != Some('\'') {
                        break 'PARENT;
                    }
                }
                Some('\\') => {
                    // considered one character, bump twice
                    self.next();
                    self.next();
                }
                None => break,
                _ => {
                    self.next();
                }
            }
        }

        None
    }

    fn double_quoted_string(&mut self) -> LR<Option<(TokenKind, Span)>> {
        let lo = self.position();
        loop {
            match self.next() {
                Some('"') => {
                    let mut hi = self.position();
                    hi.offset -= 1;
                    return Ok(Some((TokenKind::String, lo.to(hi, self.file))));
                }
                Some('\\') if self.matches('\\') || self.matches('"') => {
                    self.next();
                }
                Some('\n') => {
                    let msg =
                        "string literals must be on a single line, use a template string instead"
                            .into();

                    let msg = SpannedMessage {
                        message: msg,
                        span: self.anchored_span(),
                    };

                    return Err(msg);
                }
                None => break,
                _ => {
                    continue;
                }
            };
        }

        Ok(None)
    }

    fn back_quote_string(&mut self) -> LR<Option<(TokenKind, Span)>> {
        let lo = self.position();
        loop {
            match self.next() {
                Some('`') => {
                    let mut hi = self.position();
                    hi.offset -= 1;
                    return Ok(Some((TokenKind::Identifier, lo.to(hi, self.file))));
                }
                Some('\\') if self.matches('\\') || self.matches('`') => {
                    self.next();
                }
                Some('\n') => {
                    let msg = "template identifiers must be on a single line".into();

                    let msg = SpannedMessage {
                        message: msg,
                        span: self.anchored_span(),
                    };

                    return Err(msg);
                }
                None => break,
                _ => {
                    continue;
                }
            };
        }

        Ok(None)
    }

    fn _back_quote_string_old(&mut self) -> LR<Option<(TokenKind, Span)>> {
        // already parsed first '`'
        let lo = self.position();
        loop {
            match self.next() {
                Some('`') => {
                    let mut hi = self.position();
                    hi.offset -= 1;
                    return Ok(Some((TokenKind::Identifier, lo.to(hi, self.file))));
                }
                Some('\\') if self.matches('\\') || self.matches('`') => {
                    self.next();
                }
                None => break,
                _ => continue,
            };
        }

        Ok(None)
    }
}

impl Lexer {
    fn number(&mut self, first_digit: char) -> LR<TokenKind> {
        let mut base = Base::Decimal;

        if first_digit == '0' {
            match self.first() {
                Some('b') => {
                    base = Base::Binary;
                    self.next(); // eat base char

                    let res = self.eat_decimal_digits();

                    if !res {
                        return Err(SpannedMessage {
                            message: "invalid integer literal".into(),
                            span: self.anchored_span(),
                        });
                    }
                }
                Some('o') => {
                    base = Base::Octal;
                    self.next();

                    let res = self.eat_decimal_digits();

                    if !res {
                        return Err(SpannedMessage {
                            message: "invalid integer literal".into(),
                            span: self.anchored_span(),
                        });
                    }
                }
                Some('x') => {
                    base = Base::Hexadecimal;
                    self.next();

                    let res = self.eat_hex_digits();

                    if !res {
                        return Err(SpannedMessage {
                            message: "invalid integer literal".into(),
                            span: self.anchored_span(),
                        });
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
                        return Ok(TokenKind::Integer(base));
                    }
                },
                None => {
                    return Err(SpannedMessage {
                        message: "invalid integer literal".into(),
                        span: self.anchored_span(),
                    });
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
                    self.next();
                    let mut empty = false;

                    if self.first() != None && Lexer::is_digit(self.first().unwrap()) {
                        self.eat_decimal_digits();

                        match self.first() {
                            Some('e') | Some('E') => {
                                self.next();
                                empty = !self.eat_float_exponents();
                            }
                            _ => {}
                        }
                    }

                    if empty {
                        return Err(SpannedMessage {
                            message: "invalid float literal".into(),
                            span: self.anchored_span(),
                        });
                    }

                    return Ok(TokenKind::Float(base));
                }
            }
            Some('e') | Some('E') => {
                self.next();
                let empty = !self.eat_float_exponents();

                if empty {
                    return Err(SpannedMessage {
                        message: "invalid float literal".into(),
                        span: self.anchored_span(),
                    });
                }
            }
            _ => {}
        }

        Ok(TokenKind::Integer(base))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn lexer(input: &str) -> Lexer {
        Lexer::new(input.into(), FileID::new(0))
    }

    macro_rules! assert_token {
        ($input: expr, $kind: expr, $content: expr) => {
            let mut lexer = lexer($input);
            let token = lexer
                .token()
                .expect("Expected Valid Token")
                .expect("Expected Token");
            assert_eq!($kind, token.kind);
            assert_eq!($content, lexer.read(&token.content));
        };
    }

    macro_rules! assert_sequence_kind {
        ($input: expr, $( $token: expr ),+ ) => {
            let lexer = lexer($input);
            let file = lexer.tokenize().expect("Expected Parsed Sequence");
            let kinds: Vec<TokenKind> = file.tokens.into_iter().map(|v| v.kind).collect();
            assert_eq!(kinds, vec![$( $token, )+ TokenKind::Eof]);
        };
    }

    macro_rules! assert_error {
        ($input: expr, $msg: expr) => {
            let mut lexer = lexer($input);
            match lexer.token() {
                Ok(_) => panic!("Expected lexer error"),
                Err(err) => assert_eq!(err.message, $msg),
            }
        };
    }

    #[test]
    fn test_keywords() {
        assert_token!("enum", TokenKind::Enum, "enum");
        assert_token!("struct", TokenKind::Struct, "struct");
        assert_token!("true", TokenKind::True, "true");
        assert_token!("false", TokenKind::False, "false");
        assert_token!("nil", TokenKind::Nil, "nil");
        assert_token!("func", TokenKind::Function, "func");
        assert_token!("struct", TokenKind::Struct, "struct");
        assert_token!("enum", TokenKind::Enum, "enum");
        assert_token!("import", TokenKind::Import, "import");
        assert_token!("bridge", TokenKind::Bridge, "bridge");
        assert_token!("interface", TokenKind::Interface, "interface");
        assert_token!("type", TokenKind::Type, "type");
        assert_token!("conform", TokenKind::Conform, "conform");
        assert_token!("extend", TokenKind::Extend, "extend");
        assert_token!("extern", TokenKind::Extern, "extern");
        assert_token!("let", TokenKind::Let, "let");
        assert_token!("var", TokenKind::Var, "var");
        assert_token!("const", TokenKind::Const, "const");
        assert_token!("loop", TokenKind::Loop, "loop");
        assert_token!("while", TokenKind::While, "while");
        assert_token!("if", TokenKind::If, "if");
        assert_token!("else", TokenKind::Else, "else");
        assert_token!("return", TokenKind::Return, "return");
        assert_token!("break", TokenKind::Break, "break");
        assert_token!("continue", TokenKind::Continue, "continue");
        assert_token!("ensure", TokenKind::Ensure, "ensure");
        assert_token!("defer", TokenKind::Defer, "defer");
        assert_token!("guard", TokenKind::Guard, "guard");
        assert_token!("for", TokenKind::For, "for");
        assert_token!("async", TokenKind::Async, "async");
        assert_token!("unsafe", TokenKind::Unsafe, "unsafe");
        assert_token!("as", TokenKind::As, "as");
        assert_token!("in", TokenKind::In, "in");
        assert_token!("where", TokenKind::Where, "where");
        assert_token!("await", TokenKind::Await, "await");
        assert_token!("namespace", TokenKind::Namespace, "namespace");
        assert_token!("public", TokenKind::Public, "public");
        assert_token!("when", TokenKind::When, "when");
    }

    #[test]
    fn test_operands() {
        assert_sequence_kind!(
            "+ - / * %",
            TokenKind::Plus,
            TokenKind::Minus,
            TokenKind::Quotient,
            TokenKind::Star,
            TokenKind::Modulus
        );

        assert_sequence_kind!(
            "+= -= /= *= %=",
            TokenKind::PlusEq,
            TokenKind::MinusEq,
            TokenKind::DivEq,
            TokenKind::MulEq,
            TokenKind::RemEq
        );

        assert_sequence_kind!("&& ||", TokenKind::AmpAmp, TokenKind::BarBar);

        assert_sequence_kind!(
            "< > == != <= >= ~= ===",
            TokenKind::LChevron,
            TokenKind::RChevron,
            TokenKind::Eql,
            TokenKind::Neq,
            TokenKind::Leq,
            TokenKind::Geq,
            TokenKind::Teq,
            TokenKind::PtrEq
        );
    }

    #[test]
    fn test_literals() {
        // integers
        assert_token!("100", TokenKind::Integer(Base::Decimal), "100");
        assert_token!("0b1111", TokenKind::Integer(Base::Binary), "0b1111");
        assert_token!("0o4444", TokenKind::Integer(Base::Octal), "0o4444");
        assert_token!("0xFFFF", TokenKind::Integer(Base::Hexadecimal), "0xFFFF");

        assert_token!("100e10", TokenKind::Integer(Base::Decimal), "100e10");

        // float
        assert_token!("2.44", TokenKind::Float(Base::Decimal), "2.44");
        assert_token!("2.44e5", TokenKind::Float(Base::Decimal), "2.44e5");

        // others
        assert_token!("\"one\"", TokenKind::String, "one");
        assert_token!("\'A\'", TokenKind::Rune, "A");
        assert_token!("true", TokenKind::True, "true");
        assert_token!("false", TokenKind::False, "false");
        assert_token!("nil", TokenKind::Nil, "nil");
    }

    #[test]
    fn test_identifiers() {
        assert_token!("foo", TokenKind::Identifier, "foo");
        assert_token!("_foo", TokenKind::Identifier, "_foo");
        assert_token!("__foo__", TokenKind::Identifier, "__foo__");
        assert_token!("foo1", TokenKind::Identifier, "foo1");
        assert_token!("foo__1", TokenKind::Identifier, "foo__1");
        assert_token!("`pub`", TokenKind::Identifier, "pub");
        assert_token!(
            "`test escaped identifier`",
            TokenKind::Identifier,
            "test escaped identifier"
        );
    }

    #[test]
    fn test_comments() {
        assert_token!("//foo bar baz", TokenKind::SingleLineComment, "foo bar baz");

        assert_token!(
            "// foo bar baz",
            TokenKind::SingleLineComment,
            " foo bar baz"
        );

        assert_token!(
            "/*foo bar baz*/",
            TokenKind::MultiLineComment,
            "foo bar baz"
        );

        assert_token!(
            r#"/*
            One

            Two

            Three

            */
            "#,
            TokenKind::MultiLineComment,
            r#"
            One

            Two

            Three

            "#
        );
    }

    #[test]
    fn test_delimiters() {
        assert_sequence_kind!(
            "( ) [ ] { } ; ,",
            TokenKind::LParen,
            TokenKind::RParen,
            TokenKind::LBracket,
            TokenKind::RBracket,
            TokenKind::LBrace,
            TokenKind::RBrace,
            TokenKind::Semicolon,
            TokenKind::Comma
        );

        assert_sequence_kind!(
            ": :: -> =>",
            TokenKind::Colon,
            TokenKind::Scope,
            TokenKind::RArrow,
            TokenKind::EqArrow
        );

        assert_sequence_kind!(
            ". .. ... ..=",
            TokenKind::Dot,
            TokenKind::DotDot,
            TokenKind::Ellipsis,
            TokenKind::DotDotEq
        );
    }

    #[test]
    fn test_misc_tokens() {
        assert_sequence_kind!(
            "? ?. ?? @ _ | |> ^ ^= & &= | |= << >> <<= >>=",
            TokenKind::Question,
            TokenKind::QuestionDot,
            TokenKind::QuestionQuestion,
            TokenKind::At,
            TokenKind::Underscore,
            TokenKind::Bar,
            TokenKind::Pipe,
            TokenKind::Caret,
            TokenKind::CaretEq,
            TokenKind::Amp,
            TokenKind::AmpEq,
            TokenKind::Bar,
            TokenKind::BarEq,
            TokenKind::Shl,
            TokenKind::Shr,
            TokenKind::ShlEq,
            TokenKind::ShrEq
        );
    }

    #[test]
    fn test_error_cases() {
        assert_error!("/* unterminated", "unterminated multiline comment");
        assert_error!("\"unterminated", "unterminated string literal");
        assert_error!("`unterminated", "unterminated template-string literal");
        assert_error!("'a", "unterminated rune literal");
    }

    #[test]
    fn test_operator_tokens() {
        assert_sequence_kind!(
            "= ! ~",
            TokenKind::Assign,
            TokenKind::Bang,
            TokenKind::Tilde
        );
    }

    #[test]
    fn test_numeric_underscores() {
        assert_token!("1_000", TokenKind::Integer(Base::Decimal), "1_000");
        assert_token!("0b10_10", TokenKind::Integer(Base::Binary), "0b10_10");
        assert_token!("0o70_70", TokenKind::Integer(Base::Octal), "0o70_70");
        assert_token!("0xAB_CD", TokenKind::Integer(Base::Hexadecimal), "0xAB_CD");
    }

    #[test]
    fn test_invalid_literals() {
        assert_error!("0b", "invalid integer literal");
        assert_error!("0xG", "invalid integer literal");
        assert_error!("1e", "invalid float literal");
    }

    #[test]
    fn test_line_terminated_literals() {
        assert_error!(
            "\"foo\nbar\"",
            "string literals must be on a single line, use a template string instead"
        );
        assert_error!(
            "`foo\nbar`",
            "template identifiers must be on a single line"
        );
    }

    #[test]
    fn test_invalid_token() {
        assert_error!("$", "invalid token");
    }
}
