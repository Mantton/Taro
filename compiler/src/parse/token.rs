use ecow::EcoString;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    EOF,
    Semicolon,

    CommentDoc { value: EcoString },

    Identifier { value: EcoString },
    String { value: EcoString },
    Rune { value: EcoString },
    Integer { value: EcoString, base: Base },
    Float { value: EcoString, base: Base },

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

    Comma,    // ,
    Dot,      // .
    Colon,    // :
    LParen,   // (
    RParen,   // )
    LBrace,   // {
    RBrace,   // }
    LBracket, // [
    RBracket, // ]

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
    DotStar,  // .*

    // Keywords
    Any,
    As,
    Break,
    Case,
    Const,
    Continue,
    Defer,
    Else,
    Enum,
    Export,
    Extend,
    False,
    For,
    Function,
    Guard,
    If,
    Import,
    In,
    Init,
    Interface,
    Let,
    Loop,
    Match,
    Namespace,
    Nil,
    Private,
    Public,
    Return,
    Static,
    Struct,
    True,
    Type,
    Var,
    Where,
    While,

    // Reserved Keywords
    Class,
    Final,
    Override,
    FilePrivate,
    Protected,
    Get,
    Set,
    Async,
    Await,
    Mut,
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
