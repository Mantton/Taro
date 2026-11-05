#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    EOF,
    Semicolon,

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
    ColonEq,  // :=, inferred mutable local declaration
    Plus,     // +, Arithmetic Add
    Minus,    // -, Arithmetic Sub
    Star,     // *, Arithmetic Mul
    Quotient, // /, Arithmetic Div
    Modulus,  // %, Arithmetic Remainder
    Amp,      // &, Bitwise And,
    Bang,     // !, Binary Not
    Tilde,    // ~, Bitwise Not

    LChevron,    // <
    RChevron,    // >
    IdentityEql, // ===
    IdentityNeq, // !==
    Eql,         // ==
    Neq,         // !=
    Leq,         // <=
    Geq,         // >=

    AmpAmp, // &&
    BarBar, // ||

    Comma,      // ,
    Dot,        // .
    Colon,      // :
    ColonColon, // ::, qualified namespace/type access
    LParen,     // (
    RParen,     // )
    LBrace,     // {
    RBrace,     // }
    LBracket,   // [
    RBracket,   // ]

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
    Extend,
    Conform,
    Import,
    In,
    Interface,
    Let,
    Loop,
    Match,
    Mod,
    Mut,
    Namespace,
    Nil,
    Operator,
    Private,
    Internal,
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
    Deinit,
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

/// Source spellings for diagnostics; never expose the Rust token representation.
impl std::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Identifier { value }
            | Self::FStringText { value }
            | Self::Float { value, .. } => f.write_str(value),
            Self::String { value } => write!(f, "\"{value}\""),
            Self::Rune { value } => write!(f, "'{value}'"),
            Self::Integer { value, suffix, .. } => {
                f.write_str(value)?;
                if let Some(suffix) = suffix {
                    if !value.ends_with('_') {
                        f.write_str("_")?;
                    }
                    f.write_str(match suffix {
                        IntegerTypeSuffix::I8 => "i8",
                        IntegerTypeSuffix::I16 => "i16",
                        IntegerTypeSuffix::I32 => "i32",
                        IntegerTypeSuffix::I64 => "i64",
                        IntegerTypeSuffix::U8 => "u8",
                        IntegerTypeSuffix::U16 => "u16",
                        IntegerTypeSuffix::U32 => "u32",
                        IntegerTypeSuffix::U64 => "u64",
                    })?;
                }
                Ok(())
            }
            Self::EOF => f.write_str("end of file"),
            Self::Semicolon => f.write_str(";"),
            Self::FStringStart => f.write_str("f\""),
            Self::FStringEnd => f.write_str("\""),
            Self::FStringExprStart => f.write_str("{"),
            Self::FStringExprEnd => f.write_str("}"),
            Self::Assign => f.write_str("="),
            Self::ColonEq => f.write_str(":="),
            Self::Plus => f.write_str("+"),
            Self::Minus => f.write_str("-"),
            Self::Star => f.write_str("*"),
            Self::Quotient => f.write_str("/"),
            Self::Modulus => f.write_str("%"),
            Self::Amp => f.write_str("&"),
            Self::Bang => f.write_str("!"),
            Self::Tilde => f.write_str("~"),
            Self::LChevron => f.write_str("<"),
            Self::RChevron => f.write_str(">"),
            Self::IdentityEql => f.write_str("==="),
            Self::IdentityNeq => f.write_str("!=="),
            Self::Eql => f.write_str("=="),
            Self::Neq => f.write_str("!="),
            Self::Leq => f.write_str("<="),
            Self::Geq => f.write_str(">="),
            Self::AmpAmp => f.write_str("&&"),
            Self::BarBar => f.write_str("||"),
            Self::Comma => f.write_str(","),
            Self::Dot => f.write_str("."),
            Self::Colon => f.write_str(":"),
            Self::ColonColon => f.write_str("::"),
            Self::LParen => f.write_str("("),
            Self::RParen => f.write_str(")"),
            Self::LBrace => f.write_str("{"),
            Self::RBrace => f.write_str("}"),
            Self::LBracket => f.write_str("["),
            Self::RBracket => f.write_str("]"),
            Self::PlusEq => f.write_str("+="),
            Self::MinusEq => f.write_str("-="),
            Self::MulEq => f.write_str("*="),
            Self::DivEq => f.write_str("/="),
            Self::RemEq => f.write_str("%="),
            Self::AmpEq => f.write_str("&="),
            Self::BarEq => f.write_str("|="),
            Self::CaretEq => f.write_str("^="),
            Self::ShlEq => f.write_str("<<="),
            Self::ShrEq => f.write_str(">>="),
            Self::Bar => f.write_str("|"),
            Self::Caret => f.write_str("^"),
            Self::Shr => f.write_str(">>"),
            Self::Shl => f.write_str("<<"),
            Self::RArrow => f.write_str("->"),
            Self::EqArrow => f.write_str("=>"),
            Self::Underscore => f.write_str("_"),
            Self::Pipe => f.write_str("|>"),
            Self::Question => f.write_str("?"),
            Self::QuestionDot => f.write_str("?."),
            Self::QuestionQuestion => f.write_str("??"),
            Self::At => f.write_str("@"),
            Self::Hash => f.write_str("#"),
            Self::Ellipsis => f.write_str("..."),
            Self::DotDot => f.write_str(".."),
            Self::DotDotEq => f.write_str("..="),
            Self::DotStar => f.write_str(".*"),
            Self::Any => f.write_str("any"),
            Self::As => f.write_str("as"),
            Self::Is => f.write_str("is"),
            Self::Break => f.write_str("break"),
            Self::Case => f.write_str("case"),
            Self::Const => f.write_str("const"),
            Self::Continue => f.write_str("continue"),
            Self::Defer => f.write_str("defer"),
            Self::Else => f.write_str("else"),
            Self::Enum => f.write_str("enum"),
            Self::Export => f.write_str("export"),
            Self::Extern => f.write_str("extern"),
            Self::False => f.write_str("false"),
            Self::For => f.write_str("for"),
            Self::Function => f.write_str("func"),
            Self::Guard => f.write_str("guard"),
            Self::If => f.write_str("if"),
            Self::Impl => f.write_str("impl"),
            Self::Extend => f.write_str("extend"),
            Self::Conform => f.write_str("conform"),
            Self::Import => f.write_str("import"),
            Self::In => f.write_str("in"),
            Self::Init => f.write_str("init"),
            Self::Deinit => f.write_str("deinit"),
            Self::Interface => f.write_str("interface"),
            Self::Let => f.write_str("let"),
            Self::Loop => f.write_str("loop"),
            Self::Match => f.write_str("match"),
            Self::Mod => f.write_str("mod"),
            Self::Namespace => f.write_str("namespace"),
            Self::Nil => f.write_str("nil"),
            Self::Operator => f.write_str("operator"),
            Self::Private => f.write_str("private"),
            Self::Internal => f.write_str("internal"),
            Self::Public => f.write_str("public"),
            Self::Readonly => f.write_str("readonly"),
            Self::Return => f.write_str("return"),
            Self::Static => f.write_str("static"),
            Self::Struct => f.write_str("struct"),
            Self::True => f.write_str("true"),
            Self::Type => f.write_str("type"),
            Self::Var => f.write_str("var"),
            Self::Where => f.write_str("where"),
            Self::While => f.write_str("while"),
            Self::Unsafe => f.write_str("unsafe"),
            Self::Class => f.write_str("class"),
            Self::Final => f.write_str("final"),
            Self::Override => f.write_str("override"),
            Self::FilePrivate => f.write_str("fileprivate"),
            Self::Protected => f.write_str("protected"),
            Self::Async => f.write_str("async"),
            Self::Await => f.write_str("await"),
            Self::Mut => f.write_str("mut"),
            Self::Ref => f.write_str("ref"),
        }
    }
}

#[cfg(test)]
mod diagnostic_literal_tests {
    use super::*;
    #[test]
    fn suffixed_integer_diagnostic_keeps_one_suffix_separator() {
        // The lexer leaves the separator in the numeric text and records the
        // suffix separately.
        let token = Token::Integer {
            value: "0xff_".into(),
            base: Base::Hexadecimal,
            suffix: Some(IntegerTypeSuffix::U32),
        };
        assert_eq!(token.to_string(), "0xff_u32");
    }
}
