use std::fmt::Display;
mod operator;
pub use operator::*;
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
    Void,

    Import,
    Export,

    Public,
    Function,
    Struct,
    Enum,
    Bridge,
    Interface,
    Type,
    Conform,
    Extend,
    Extern,
    Namespace,
    Init,
    AssociatedType,
    Case,
    Operator,

    Let,
    Var,
    Const,
    Mut,

    If,
    Else,
    When,

    Defer,
    Guard,
    Return,
    Break,
    Continue,
    Loop,
    While,
    For,

    Ensure,
    Unsafe,

    Await,
    Async,

    As,
    In,
    Is,
    Where,
    Match,

    Some,
    Any,

    Assign,     // =, Variable Assignment
    DeclareVar, // :=, Variable Declaration
    Plus,       // +, Arithmetic Add
    Minus,      // -, Arithmetic Sub
    Star,       // *, Arithmetic Mul
    Quotient,   // /, Arithmetic Div
    Modulus,    // %, Arithmetic Remainder
    Amp,        // &, Bitwise And,
    Bang,       // !, Binary Not
    Tilde,      // ~, Bitwise Not

    LChevron, // <
    RChevron, // >
    Eql,      // ==
    Neq,      // !=
    Leq,      // <=
    Geq,      // >=
    Teq,      // ~=, Expression Matches

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
            TokenKind::Bridge => "bridge",
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
            TokenKind::DeclareVar => ":=",
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
            TokenKind::Teq => "~=",
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
            TokenKind::Unsafe => "unsafe",
            TokenKind::Public => "public",
            TokenKind::Ellipsis => "...",
            TokenKind::Void => "void",
            TokenKind::Await => "await",
            TokenKind::DotDot => "..",
            TokenKind::DotDotEq => "..=",
            TokenKind::Namespace => "namespace",
            TokenKind::Match => "match",
            TokenKind::When => "when",
            TokenKind::EqArrow => "=>",
            TokenKind::Is => "is",
            TokenKind::Some => "some",
            TokenKind::Any => "any",
            TokenKind::Init => "init",
            TokenKind::Export => "export",
            TokenKind::AssociatedType => "associatedtype",
            TokenKind::PtrEq => "===",
            TokenKind::Case => "case",
            TokenKind::Operator => "operator",
            TokenKind::Mut => "mut",
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
            "bridge" => TokenKind::Bridge,
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
            "unsafe" => TokenKind::Unsafe,
            "as" => TokenKind::As,
            "in" => TokenKind::In,
            "where" => TokenKind::Where,
            "void" => TokenKind::Void,
            "await" => TokenKind::Await,
            "namespace" => TokenKind::Namespace,
            "public" => TokenKind::Public,
            "when" => TokenKind::When,
            "match" => TokenKind::Match,
            "is" => TokenKind::Is,
            "some" => TokenKind::Some,
            "any" => TokenKind::Any,
            "init" => TokenKind::Init,
            "export" => TokenKind::Export,
            "associatedtype" => TokenKind::AssociatedType,
            "case" => TokenKind::Case,
            "operator" => TokenKind::Operator,
            "mut" => TokenKind::Mut,
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
        ) {
            return true;
        }

        if matches!(kind, LParen | LBracket) {
            return true;
        }

        return false;
    }
}

impl TokenKind {
    pub fn bin_op_non_assign(k: TokenKind) -> Option<BinaryOperator> {
        match k {
            TokenKind::Plus => Some(BinaryOperator::Add),
            TokenKind::Minus => Some(BinaryOperator::Sub),
            TokenKind::Star => Some(BinaryOperator::Mul),
            TokenKind::Quotient => Some(BinaryOperator::Div),
            TokenKind::Modulus => Some(BinaryOperator::Rem),

            TokenKind::AmpAmp => Some(BinaryOperator::BoolAnd),
            TokenKind::BarBar => Some(BinaryOperator::BoolOr),

            TokenKind::Amp => Some(BinaryOperator::BitAnd),
            TokenKind::Bar => Some(BinaryOperator::BitOr),
            TokenKind::Caret => Some(BinaryOperator::BitXor),

            TokenKind::Shl => Some(BinaryOperator::BitShl),
            TokenKind::Shr => Some(BinaryOperator::BitShr),

            TokenKind::Eql => Some(BinaryOperator::Eql),
            TokenKind::Neq => Some(BinaryOperator::Neq),
            TokenKind::Geq => Some(BinaryOperator::Geq),
            TokenKind::Leq => Some(BinaryOperator::Leq),
            TokenKind::Teq => Some(BinaryOperator::PatMatch),

            TokenKind::RChevron => Some(BinaryOperator::Gt),
            TokenKind::LChevron => Some(BinaryOperator::Lt),
            TokenKind::PtrEq => Some(BinaryOperator::PtrEq),
            _ => None,
        }
    }

    pub fn bin_op_assign(k: TokenKind) -> Option<BinaryOperator> {
        match k {
            TokenKind::PlusEq => Some(BinaryOperator::Add),
            TokenKind::MinusEq => Some(BinaryOperator::Sub),
            TokenKind::MulEq => Some(BinaryOperator::Mul),
            TokenKind::DivEq => Some(BinaryOperator::Div),
            TokenKind::RemEq => Some(BinaryOperator::Rem),

            TokenKind::AmpEq => Some(BinaryOperator::BitAnd),
            TokenKind::BarEq => Some(BinaryOperator::BitOr),
            TokenKind::CaretEq => Some(BinaryOperator::BitXor),

            TokenKind::ShlEq => Some(BinaryOperator::BitShl),
            TokenKind::ShrEq => Some(BinaryOperator::BitShr),
            _ => None,
        }
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
}

impl Delimiter {
    pub fn open(&self) -> TokenKind {
        match self {
            Delimiter::Parenthesis => TokenKind::LParen,
            Delimiter::Brace => TokenKind::LBrace,
            Delimiter::Bracket => TokenKind::LBracket,
            Delimiter::Chevron => TokenKind::LChevron,
        }
    }

    pub fn close(&self) -> TokenKind {
        match self {
            Delimiter::Parenthesis => TokenKind::RParen,
            Delimiter::Brace => TokenKind::RBrace,
            Delimiter::Bracket => TokenKind::RBracket,
            Delimiter::Chevron => TokenKind::RChevron,
        }
    }
}
