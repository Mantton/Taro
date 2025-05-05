pub fn convert_ast_literal(literal: taroc_ast::Literal) -> Result<taroc_hir::Literal, String> {
    match literal.kind {
        taroc_ast::LiteralKind::Bool(v) => Ok(taroc_hir::Literal::Bool(v)),
        taroc_ast::LiteralKind::String => Ok(taroc_hir::Literal::String(literal.content)),
        taroc_ast::LiteralKind::Nil => Ok(taroc_hir::Literal::Nil),
        taroc_ast::LiteralKind::Rune => {
            let c: char = unescape_char(literal.content.as_str())
                .map_err(|err| format!("malformed rune, {:?}", err))?;
            Ok(taroc_hir::Literal::Rune(c))
        }
        taroc_ast::LiteralKind::Integer(base) => {
            let content = literal.content.as_str().replace("_", "");
            u64::from_str_radix(content.as_str(), base.radix())
                .map(|i| taroc_hir::Literal::Integer(i))
                .map_err(|err| format!("malformed integer: {}", err))
        }
        taroc_ast::LiteralKind::Float => {
            match literal.content.as_str().parse::<f64>() {
                Ok(v) => return Ok(taroc_hir::Literal::Float(v)),
                Err(err) => return Err(format!("malformed floating point, {}", err)),
            };
        }
    }
}

/// Errors and warnings that can occur during string unescaping. They mostly
/// relate to malformed escape sequences, but there are a few that are about
/// other problems.
#[derive(Debug, PartialEq, Eq)]
#[allow(unused)]
pub enum EscapeError {
    /// Expected 1 char, but 0 were found.
    ZeroChars,
    /// Expected 1 char, but more than 1 were found.
    MoreThanOneChar,

    /// Escaped '\' character without continuation.
    LoneSlash,
    /// Invalid escape character (e.g. '\z').
    InvalidEscape,
    /// Raw '\r' encountered.
    BareCarriageReturn,
    /// Raw '\r' encountered in raw string.
    BareCarriageReturnInRawString,
    /// Unescaped character that was expected to be escaped (e.g. raw '\t').
    EscapeOnlyChar,

    /// Numeric character escape is too short (e.g. '\x1').
    TooShortHexEscape,
    /// Invalid character in numeric escape (e.g. '\xz')
    InvalidCharInHexEscape,
    /// Character code in numeric escape is non-ascii (e.g. '\xFF').
    OutOfRangeHexEscape,

    /// '\u' not followed by '{'.
    NoBraceInUnicodeEscape,
    /// Non-hexadecimal value in '\u{..}'.
    InvalidCharInUnicodeEscape,
    /// '\u{}'
    EmptyUnicodeEscape,
    /// No closing brace in '\u{..}', e.g. '\u{12'.
    UnclosedUnicodeEscape,
    /// '\u{_12}'
    LeadingUnderscoreUnicodeEscape,
    /// More than 6 characters in '\u{..}', e.g. '\u{10FFFF_FF}'
    OverlongUnicodeEscape,
    /// Invalid in-bound unicode character code, e.g. '\u{DFFF}'.
    LoneSurrogateUnicodeEscape,
    /// Out of bounds unicode character code, e.g. '\u{FFFFFF}'.
    OutOfRangeUnicodeEscape,

    /// Unicode escape code in byte literal.
    UnicodeEscapeInByte,
    /// Non-ascii character in byte literal, byte string literal, or raw byte string literal.
    NonAsciiCharInByte,

    // `\0` in a C string literal.
    NulInCStr,

    /// After a line ending with '\', the next line contains whitespace
    /// characters that are not skipped.
    UnskippedWhitespaceWarning,

    /// After a line ending with '\', multiple lines are skipped.
    MultipleSkippedLinesWarning,
}

impl EscapeError {
    /// Returns true for actual errors, as opposed to warnings.
    pub fn _is_fatal(&self) -> bool {
        !matches!(
            self,
            EscapeError::UnskippedWhitespaceWarning | EscapeError::MultipleSkippedLinesWarning
        )
    }
}

/// Takes a contents of a char literal (without quotes), and returns an
/// unescaped char or an error.
pub fn unescape_char(src: &str) -> Result<char, EscapeError> {
    unescape_char_or_byte(&mut src.chars(), Mode::Char)
}

/// What kind of literal do we parse.
#[derive(Debug, Clone, Copy, PartialEq)]
#[allow(unused)]
pub enum Mode {
    Char,

    Byte,

    Str,
    RawStr,

    ByteStr,
    RawByteStr,

    CStr,
    RawCStr,
}

#[allow(unused)]
impl Mode {
    pub fn in_double_quotes(self) -> bool {
        use Mode::*;
        match self {
            Str | RawStr | ByteStr | RawByteStr | CStr | RawCStr => true,
            Char | Byte => false,
        }
    }

    /// Are `\x80`..`\xff` allowed?
    fn allow_high_bytes(self) -> bool {
        use Mode::*;
        match self {
            Char | Str => false,
            Byte | ByteStr | CStr => true,
            RawStr | RawByteStr | RawCStr => unreachable!(),
        }
    }

    /// Are unicode (non-ASCII) chars allowed?
    #[inline]
    fn allow_unicode_chars(self) -> bool {
        use Mode::*;
        match self {
            Byte | ByteStr | RawByteStr => false,
            Char | Str | RawStr | CStr | RawCStr => true,
        }
    }

    /// Are unicode escapes (`\u`) allowed?
    fn allow_unicode_escapes(self) -> bool {
        use Mode::*;

        match self {
            Byte | ByteStr => false,
            Char | Str | CStr => true,
            RawByteStr | RawStr | RawCStr => unreachable!(),
        }
    }

    pub fn prefix_noraw(self) -> &'static str {
        use Mode::*;
        match self {
            Char | Str | RawStr => "",
            Byte | ByteStr | RawByteStr => "b",
            CStr | RawCStr => "c",
        }
    }
}

fn scan_escape<T: From<char> + From<u8>>(
    chars: &mut std::str::Chars<'_>,
    mode: Mode,
) -> Result<T, EscapeError> {
    // Previous character was '\\', unescape what follows.
    let res: char = match chars.next().ok_or(EscapeError::LoneSlash)? {
        '"' => '"',
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        '\\' => '\\',
        '\'' => '\'',
        '0' => '\0',
        'x' => {
            // Parse hexadecimal character code.

            let hi = chars.next().ok_or(EscapeError::TooShortHexEscape)?;
            let hi = hi.to_digit(16).ok_or(EscapeError::InvalidCharInHexEscape)?;

            let lo = chars.next().ok_or(EscapeError::TooShortHexEscape)?;
            let lo = lo.to_digit(16).ok_or(EscapeError::InvalidCharInHexEscape)?;

            let value = (hi * 16 + lo) as u8;

            return if !mode.allow_high_bytes() && !value.is_ascii() {
                Err(EscapeError::OutOfRangeHexEscape)
            } else {
                // This may be a high byte, but that will only happen if `T` is
                // `MixedUnit`, because of the `allow_high_bytes` check above.
                Ok(T::from(value))
            };
        }
        'u' => return scan_unicode(chars, mode.allow_unicode_escapes()).map(T::from),
        _ => return Err(EscapeError::InvalidEscape),
    };
    Ok(T::from(res))
}

fn scan_unicode(
    chars: &mut std::str::Chars<'_>,
    allow_unicode_escapes: bool,
) -> Result<char, EscapeError> {
    // We've parsed '\u', now we have to parse '{..}'.

    if chars.next() != Some('{') {
        return Err(EscapeError::NoBraceInUnicodeEscape);
    }

    // First character must be a hexadecimal digit.
    let mut n_digits = 1;
    let mut value: u32 = match chars.next().ok_or(EscapeError::UnclosedUnicodeEscape)? {
        '_' => return Err(EscapeError::LeadingUnderscoreUnicodeEscape),
        '}' => return Err(EscapeError::EmptyUnicodeEscape),
        c => c
            .to_digit(16)
            .ok_or(EscapeError::InvalidCharInUnicodeEscape)?,
    };

    // First character is valid, now parse the rest of the number
    // and closing brace.
    loop {
        match chars.next() {
            None => return Err(EscapeError::UnclosedUnicodeEscape),
            Some('_') => continue,
            Some('}') => {
                if n_digits > 6 {
                    return Err(EscapeError::OverlongUnicodeEscape);
                }

                // Incorrect syntax has higher priority for error reporting
                // than unallowed value for a literal.
                if !allow_unicode_escapes {
                    return Err(EscapeError::UnicodeEscapeInByte);
                }

                break std::char::from_u32(value).ok_or({
                    if value > 0x10FFFF {
                        EscapeError::OutOfRangeUnicodeEscape
                    } else {
                        EscapeError::LoneSurrogateUnicodeEscape
                    }
                });
            }
            Some(c) => {
                let digit: u32 = c
                    .to_digit(16)
                    .ok_or(EscapeError::InvalidCharInUnicodeEscape)?;
                n_digits += 1;
                if n_digits > 6 {
                    // Stop updating value since we're sure that it's incorrect already.
                    continue;
                }
                value = value * 16 + digit;
            }
        };
    }
}

#[inline]
fn ascii_check(c: char, allow_unicode_chars: bool) -> Result<char, EscapeError> {
    if allow_unicode_chars || c.is_ascii() {
        Ok(c)
    } else {
        Err(EscapeError::NonAsciiCharInByte)
    }
}

fn unescape_char_or_byte(chars: &mut std::str::Chars<'_>, mode: Mode) -> Result<char, EscapeError> {
    let c = chars.next().ok_or(EscapeError::ZeroChars)?;
    let res = match c {
        '\\' => scan_escape(chars, mode),
        '\n' | '\t' | '\'' => Err(EscapeError::EscapeOnlyChar),
        '\r' => Err(EscapeError::BareCarriageReturn),
        _ => ascii_check(c, mode.allow_unicode_chars()),
    }?;
    if chars.next().is_some() {
        return Err(EscapeError::MoreThanOneChar);
    }
    Ok(res)
}
