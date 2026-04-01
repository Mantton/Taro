#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    EOF,
    Semicolon,

    CommentDoc {
        value: String,
    },

    Identifier {
        value: String,
    },
    String {
        value: String,
    },
    FStringStart,
    FStringText {
        value: String,
    },
    FStringExprStart,
    FStringExprEnd,
    FStringEnd,
    Rune {
        value: String,
    },
    Integer {
        value: String,
        base: Base,
        suffix: Option<IntegerTypeSuffix>,
    },
    Float {
        value: String,
        base: Base,
    },

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
    Is,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntegerTypeSuffix {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
}

impl IntegerTypeSuffix {
    pub fn parse(sign: char, bits: &str) -> Option<Self> {
        let signed = match sign {
            'i' | 'I' => true,
            'u' | 'U' => false,
            _ => return None,
        };

        match (signed, bits) {
            (true, "8") => Some(Self::I8),
            (true, "16") => Some(Self::I16),
            (true, "32") => Some(Self::I32),
            (true, "64") => Some(Self::I64),
            (false, "8") => Some(Self::U8),
            (false, "16") => Some(Self::U16),
            (false, "32") => Some(Self::U32),
            (false, "64") => Some(Self::U64),
            _ => None,
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
