use std::fmt::Display;
use taroc_span::Span;

#[derive(Debug, Clone, PartialEq, Copy)]
pub enum TokenKind {
    Eof,
    Newline,
    Whitespace,
    SingleLineComment,
    MultiLineComment,

    Identifier,
    Integer(Base),
    Float(Base),
    Rune,
    String,

    True,
    False,
    Nil,

    Import,
    Export,

    Public,
    Private,

    Function,
    Struct,
    Enum,
    Interface,
    Type,
    Conform,
    Extend,
    Extern,
    Namespace,
    Operator,

    Let,
    Var,
    Const,
    Readonly,

    If,
    Else,
    Match,
    Case,

    Defer,
    Guard,
    Return,
    Break,
    Continue,
    Loop,
    While,
    For,

    Ensure,

    Await,
    Async,

    As,
    In,
    Where,

    Some,
    Any,

    Assign,   // =, Variable Assignment
    Plus,     // +, Arithmetic Add
    Minus,    // -, Arithmetic Sub
    Star,     // *, Arithmetic Mul
    Quotient, // /, Arithmetic Div
    Modulus,  // %, Arithmetic Remainder
    Amp,      // &, Bitwise And,
    Bang,     // !, Binary Not
    Tilde,    // ~, Bitwise Not

    LChevron, // <
    RChevron, // >
    Eql,      // ==
    Neq,      // !=
    Leq,      // <=
    Geq,      // >=

    AmpAmp, // &&
    BarBar, // ||

    Comma,     // ,
    Dot,       // .
    Semicolon, // ;
    Colon,     // :
    Scope,     // ::
    LParen,    // (
    RParen,    // )
    LBrace,    // {
    RBrace,    // }
    LBracket,  // [
    RBracket,  // ]

    PlusEq,  // +=
    MinusEq, // -=
    MulEq,   // *=
    DivEq,   // /=
    RemEq,   // %=
    AmpEq,   // &=
    BarEq,   // |=
    CaretEq, // ^=
    ShlEq,   // <<=
    ShrEq,   // >>=
    PtrEq,   // ===

    Bar,   // |
    Caret, // ^
    Shr,   // >>
    Shl,   // <<

    RArrow,           // ->
    EqArrow,          // =>
    Underscore,       // _
    Pipe,             // |>
    Question,         // ?
    QuestionDot,      // ?.
    QuestionQuestion, // ??
    At,               // @

    Ellipsis, // ...
    DotDot,   // ..
    DotDotEq, // ..=
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let text = match self {
            TokenKind::Eof => "END OF FILE",
            TokenKind::Newline => "new_line_break",
            TokenKind::Whitespace => "WHITE_SPACE",
            TokenKind::SingleLineComment => "COMMENT",
            TokenKind::MultiLineComment => "MULTI_LINE_COMMENT",
            TokenKind::Identifier => "IDENTIFIER",
            TokenKind::Integer(_) => "INTEGER",
            TokenKind::Float(_) => "FLOAT",
            TokenKind::String => "string",
            TokenKind::Rune => "rune",
            TokenKind::True => "true",
            TokenKind::False => "false",
            TokenKind::Nil => "nil",
            TokenKind::Function => "func",
            TokenKind::Struct => "struct",
            TokenKind::Enum => "enum",
            TokenKind::Import => "import",
            TokenKind::Interface => "interface",
            TokenKind::Type => "type",
            TokenKind::Conform => "conform",
            TokenKind::Extend => "extend",
            TokenKind::Extern => "extern",
            TokenKind::Let => "let",
            TokenKind::Var => "var",
            TokenKind::Const => "const",
            TokenKind::Loop => "loop",
            TokenKind::While => "while",
            TokenKind::If => "if",
            TokenKind::Else => "else",
            TokenKind::Return => "return",
            TokenKind::Break => "break",
            TokenKind::Continue => "continue",
            TokenKind::Ensure => "ensure",
            TokenKind::Defer => "defer",
            TokenKind::Guard => "guard",
            TokenKind::For => "for",
            TokenKind::Async => "async",
            TokenKind::As => "as",
            TokenKind::In => "in",
            TokenKind::Where => "where",
            TokenKind::Assign => "=",
            TokenKind::Plus => "+",
            TokenKind::Minus => "-",
            TokenKind::Star => "*",
            TokenKind::Quotient => "/",
            TokenKind::Modulus => "%",
            TokenKind::Amp => "&",
            TokenKind::Bang => "!",
            TokenKind::Tilde => "~",
            TokenKind::LChevron => "<",
            TokenKind::RChevron => ">",
            TokenKind::Eql => "==",
            TokenKind::Neq => "!=",
            TokenKind::Leq => "<=",
            TokenKind::Geq => ">=",
            TokenKind::AmpAmp => "&&",
            TokenKind::BarBar => "||",
            TokenKind::Comma => ",",
            TokenKind::Dot => ".",
            TokenKind::Semicolon => ";",
            TokenKind::Colon => ":",
            TokenKind::Scope => "::",
            TokenKind::LParen => "(",
            TokenKind::RParen => ")",
            TokenKind::LBrace => "{",
            TokenKind::RBrace => "}",
            TokenKind::LBracket => "[",
            TokenKind::RBracket => "]",
            TokenKind::PlusEq => "+=",
            TokenKind::MinusEq => "-=",
            TokenKind::MulEq => "*=",
            TokenKind::DivEq => "/=",
            TokenKind::RemEq => "%=",
            TokenKind::AmpEq => "&=",
            TokenKind::BarEq => "|=",
            TokenKind::CaretEq => "^=",
            TokenKind::ShlEq => "<<=",
            TokenKind::ShrEq => ">>=",
            TokenKind::Bar => "|",
            TokenKind::Caret => "^",
            TokenKind::Shr => ">>",
            TokenKind::Shl => "<<",
            TokenKind::RArrow => "->",
            TokenKind::Underscore => "_",
            TokenKind::Pipe => "|>",
            TokenKind::Question => "?",
            TokenKind::QuestionDot => "?.",
            TokenKind::QuestionQuestion => "??",
            TokenKind::At => "@",
            TokenKind::Public => "public",
            TokenKind::Ellipsis => "...",
            TokenKind::Await => "await",
            TokenKind::DotDot => "..",
            TokenKind::DotDotEq => "..=",
            TokenKind::Namespace => "namespace",
            TokenKind::Match => "match",
            TokenKind::EqArrow => "=>",
            TokenKind::Some => "some",
            TokenKind::Any => "any",
            TokenKind::Export => "export",
            TokenKind::PtrEq => "===",
            TokenKind::Operator => "operator",
            TokenKind::Private => "private",
            TokenKind::Readonly => "readonly",
            TokenKind::Case => "case",
        };
        write!(f, "{}", text)
    }
}

impl TokenKind {
    pub fn keyword(str: &String) -> Option<Self> {
        let v = match str.as_str() {
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            "nil" => TokenKind::Nil,
            "func" => TokenKind::Function,
            "struct" => TokenKind::Struct,
            "enum" => TokenKind::Enum,
            "import" => TokenKind::Import,
            "interface" => TokenKind::Interface,
            "type" => TokenKind::Type,
            "conform" => TokenKind::Conform,
            "extend" => TokenKind::Extend,
            "extern" => TokenKind::Extern,
            "let" => TokenKind::Let,
            "var" => TokenKind::Var,
            "const" => TokenKind::Const,
            "loop" => TokenKind::Loop,
            "while" => TokenKind::While,
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "return" => TokenKind::Return,
            "break" => TokenKind::Break,
            "continue" => TokenKind::Continue,
            "ensure" => TokenKind::Ensure,
            "defer" => TokenKind::Defer,
            "guard" => TokenKind::Guard,
            "for" => TokenKind::For,
            "async" => TokenKind::Async,
            "as" => TokenKind::As,
            "in" => TokenKind::In,
            "where" => TokenKind::Where,
            "await" => TokenKind::Await,
            "namespace" => TokenKind::Namespace,
            "public" => TokenKind::Public,
            "match" => TokenKind::Match,
            "some" => TokenKind::Some,
            "any" => TokenKind::Any,
            "export" => TokenKind::Export,
            "operator" => TokenKind::Operator,
            "private" => TokenKind::Private,
            "readonly" => TokenKind::Readonly,
            "case" => TokenKind::Case,
            _ => return None,
        };

        Some(v)
    }
}

impl TokenKind {
    pub fn is_generic_type_disambiguating_token(kind: Self) -> bool {
        use TokenKind::*;

        if matches!(
            kind,
            RParen
                | RBracket
                | LBrace
                | RBrace
                | Dot
                | Comma
                | Semicolon
                | Newline
                | Eof
                | QuestionDot
                | Colon
                | Question
                | Assign
                | Scope
                | As
                | RChevron
        ) {
            return true;
        }

        if matches!(kind, LParen | LBracket) {
            return true;
        }

        return false;
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub content: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span, content: Span) -> Token {
        Token {
            kind,
            span,
            content,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Base {
    Decimal,
    Binary,
    Octal,
    Hexadecimal,
}

impl Base {
    pub fn radix(&self) -> u32 {
        match self {
            Base::Decimal => 10,
            Base::Binary => 2,
            Base::Octal => 8,
            Base::Hexadecimal => 16,
        }
    }
}

pub enum Delimiter {
    /// `( ... )`
    Parenthesis,
    /// `{ ... }`
    Brace,
    /// `[ ... ]`
    Bracket,
    /// `< ... >`
    Chevron,
    /// ` |...|`
    Bar,
}

impl Delimiter {
    pub fn open(&self) -> TokenKind {
        match self {
            Delimiter::Parenthesis => TokenKind::LParen,
            Delimiter::Brace => TokenKind::LBrace,
            Delimiter::Bracket => TokenKind::LBracket,
            Delimiter::Chevron => TokenKind::LChevron,
            Delimiter::Bar => TokenKind::Bar,
        }
    }

    pub fn close(&self) -> TokenKind {
        match self {
            Delimiter::Parenthesis => TokenKind::RParen,
            Delimiter::Brace => TokenKind::RBrace,
            Delimiter::Bracket => TokenKind::RBracket,
            Delimiter::Chevron => TokenKind::RChevron,
            Delimiter::Bar => TokenKind::Bar,
        }
    }
}
