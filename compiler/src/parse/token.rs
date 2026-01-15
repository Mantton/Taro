#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    EOF,
    Semicolon,

    CommentDoc { value: String },

    Identifier { value: String },
    String { value: String },
    Rune { value: String },
    Integer { value: String, base: Base },
    Float { value: String, base: Base },

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
    Hash,             // #

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
    Extern,
    False,
    For,
    Function,
    Guard,
    If,
    Impl,
    Import,
    In,
    Interface,
    Let,
    Loop,
    Match,
    Mut,
    Namespace,
    Nil,
    Operator,
    Private,
    Public,
    Return,
    Readonly,
    Static,
    Struct,
    True,
    Type,
    Unsafe,
    Var,
    Where,
    While,

    // Reserved Keywords
    Class,
    Final,
    Override,
    FilePrivate,
    Protected,
    Async,
    Await,
    Ref,
    Init,
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
