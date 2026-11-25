# Lexical Elements

This chapter covers the fundamental building blocks of Taro source code.

## Identifiers

Identifiers name variables, functions, types, and other program elements.

```ebnf
identifier ::= letter { letter | digit }
             | '`' { escaped_identifier_char } '`'

letter     ::= 'a'..'z' | 'A'..'Z' | '_'
digit      ::= '0'..'9'
escaped_identifier_char ::= ? any character except backtick or newline ?
```

An unescaped keyword or the standalone `_` token is not an identifier; use
backticks when a name would otherwise be a keyword.

### Examples

```taro
// Standard identifiers
myVariable := 10
_private := 20
camelCase := 30

// Escaped identifiers (for reserved words)
var `type` = "string"
var `func` = 42
```

---

## Literals

### Boolean Literals

```taro
true
false
```

### Nil Literal

```taro
nil
```

### Integer Literals

Taro supports decimal, binary, octal, and hexadecimal integer literals.

```taro
// Decimal
42
1_000_000      // Underscores for readability

// Binary (0b prefix)
0b1010         // 10 in decimal
0b1111_0000    // With underscores

// Octal (0o prefix)
0o77           // 63 in decimal
0o755          // Unix permissions style

// Hexadecimal (0x prefix)
0xFF           // 255 in decimal
0xDEAD_BEEF    // With underscores
```

Integer suffixes select a fixed-width type: `_i8`, `_i16`, `_i32`, `_i64`,
`_u8`, `_u16`, `_u32`, and `_u64` (the `i`/`u` is also accepted in uppercase).
For example, `255_u8` and `0xFF_u8` have type `uint8`. Unsuffixed integer
literals use context, defaulting to `int32` when unconstrained.

An integer literal must fit its final type. A leading minus is included in
that check, so `-128_i8` and `var x: int8 = -128` are valid, while `128_i8`
and `-129_i8` are errors. The same boundaries apply to constant initializers
and patterns. Negating an already negative value remains an operation and
uses the configured overflow checks.
Unsigned expression negation also remains an arithmetic operation: its
positive operand must fit, and the result follows the overflow policy.
Negative unsigned pattern values are rejected.

### Float Literals

```taro
3.14
3.14159
1.5e10         // Scientific notation
1.5e-10        // Negative exponent
1.5E+10        // Explicit positive exponent
2.5e3          // 2500.0
```

### String Literals

Ordinary strings use double quotes. Backslash escapes are decoded once, and
`${expression}` inserts a value using the existing `std::sprintf` formatting
rules. Expressions are evaluated once in argument order; formatting follows
ordinary calls to that function. There is no `f` prefix or `$name` shorthand.
A value whose type has `std::fmt::Display` prints its display text. Otherwise,
if the type has `std::fmt::Debug`, it prints its debug text, so a derived
`Debug` struct can be interpolated directly. The choice is made at compile
time, and a type with neither is an error.

```taro
"Hello, World!"
"Line 1\nLine 2"
"Tab\there"
"Quote: \"hello\""
"Unicode: \u{1F600}"
"Hello, ${name}"
"sum=${score + 5}"
"${name:<12}${price:>8.2}"
"mask=0x${mask:x} (0b${mask:b})"
"debug=${value:?}"
"Cost: $${amount}"           // A dollar sign, then the interpolated amount
"$HOME $$ {name}"            // Ordinary text; $$ and braces have no special effect
"Write \${name} here"         // Literal interpolation marker
```

An interpolation hole may include a format specifier after a top-level `:`:

```text
[[fill]align][0][width][.precision][presentation]
```

- `align` is `<` (left), `>` (right), or `^` (center, odd padding rune on the right). An optional single Unicode scalar `fill` precedes the alignment character (default `' '`; `:` is reserved for `::` and `}` closes the hole).
- `0` enables sign-aware zero padding when right-aligned with the default fill (e.g. `${-7:04}` yields `-007`).
- `width` pads the formatted text to at least that many Unicode scalar values (`runeCount()`), never splitting multi-byte UTF-8 sequences.
- `.precision` sets fractional digits for floating-point values (rounded half-to-even from the value's shortest decimal representation) and maximum kept runes for strings. Other built-in types ignore precision unless a custom `std::fmt::Formattable` inspects `FormatState.hasPrecision` and `FormatState.precision`.
- `presentation` selects `x` (lowercase hexadecimal, two's-complement bits for signed integers), `b` (binary), `e` (scientific notation for floats), or `?` (`Debug` formatting even when `Display` is also implemented).
- Custom `std::fmt::Formattable` implementations receive the presentation rune (`'v'` by default, or `'x'`, `'b'`, `'e'`, `'?'`) and the populated `FormatState`. Built-in types reject incompatible presentations (`x`/`b` on non-integer primitives, `e` on non-float primitives) at compile time; dynamic or generic mismatches panic at runtime.
- Colons inside nested parentheses, brackets, or braces (such as labeled arguments `${f(label: 1)}` or struct literals `${Point { x: 1, y: 2 }}`) remain part of the expression.

Strings and runes accept `\r`, `\0`, and ASCII hexadecimal escapes such as
`\x41`. Unicode escapes must name a Unicode scalar value. Only strings accept
`\${` as a literal `${`; other unrecognized backslash escapes are errors.
Interpolation is recognized in source before escape decoding: `"\u{24}{name}"`
is literal `${name}`, not interpolation. Inserted values are never rescanned.

Quoted strings without an active interpolation remain literals, including in
constants, patterns, attributes, ABI names and configuration predicates.
Interpolated strings are expressions and are rejected in literal-only contexts,
even when their expression would be constant. Braces, quoted strings and comments
inside an interpolation use normal Taro expression rules. Empty or unfinished
interpolations are errors. Ordinary quoted strings occupy one source line,
including their interpolation expressions.

### Raw Strings and Matching Hashes

One or more matching hashes around the quotes preserve backslashes literally.
Interpolation requires exactly the same number of hashes between `$` and `{`:

```taro
#"C:\notes\file\"#
#"Literal ${name}"#
#"C:\users\$#{name}\notes"#
##"Literal ${name} and $#{name}; inserted $##{name}"##
##"The shorter delimiter "# is ordinary text."##
```

In a one-hash string, only `$#{expression}` interpolates; `${expression}` and
`$##{expression}` are literal. Backslashes do not escape interpolation markers or
quotes in raw text. To include an active marker literally, increase the outer
hash count. A quote closes the string only when followed by the required hashes;
additional hashes after a closing delimiter belong to subsequent tokens.
Rawness applies to literal text, not expressions: an ordinary `"\n"` inside a
raw interpolation still produces a newline.

### Multiline Strings

Triple quotes allow source newlines. The opening delimiter must be immediately
followed by a newline, and the closing delimiter must be on its own line. Without
hashes, escapes work and `${expression}` interpolates. With hashes, backslashes
are literal and interpolation uses matching hashes.

```taro
html := """
    <html>
        <body>Hello, ${name}</body>
    </html>
    """

script := #"""
    const serverName = "$#{name}";
    const greeting = `Hello, ${browserName}`;
    C:\notes\file
    """#
```

The newline after the opener and the newline before the closing delimiter are
excluded. The closing delimiter's exact spaces/tabs prefix is removed from each
content line; every nonblank content line must have that prefix. Blank lines may
have less indentation. Additional indentation and trailing spaces are preserved.
An empty multiline literal is valid. Backslash line continuations are unsupported.

Interpolations may span source lines inside multiline strings. Expression lines
are parsed as code and are not subject to the literal's indentation requirement.
Indentation removal applies only to literal source text, never to inserted values.
An inserted value containing newlines is copied without automatic indentation.

Source files accept LF and CRLF line endings. CRLF pairs are normalized to LF
before tokenization, including in raw text. Bare CR is whitespace between tokens
and is rejected inside literal text. Raw multiline strings therefore preserve
backslashes, not the source file's exact bytes or indentation.

### Rune Literals

Runes represent single Unicode code points and are enclosed in single quotes.

```taro
'a'
'Z'
'\n'           // Newline
'\t'           // Tab
'\''           // Single quote
'\\'           // Backslash
'\u{1F600}'    // Unicode escape (emoji)
```

---

## Keywords

### Reserved Keywords

```
any         as          is          break       case        const       continue
async       await       defer       else        enum        export      extern      false
for         func        guard       if          extend      conform     import
in          init                    interface   loop        match
mod         namespace   nil         operator    private     public      readonly
return      static      struct      true        type        var
where       while       mut         unsafe      class       final       override
```

`init` introduces initializer declarations in owning-package `extend`
blocks. Classes use explicit initializers; structs use literals unless they
provide an initializer. `extend` declares inherent members and `conform` supplies
interface implementations. Legacy `impl` syntax is rejected.

`class`, `final` and `override` are active keywords. `fileprivate`, `protected`
and `ref` remain reserved without a supported declaration meaning, and `let`
stays reserved so its removal can be diagnosed.

### Contextual Keywords

`get`, `set`, `address` and `subscript` are contextual accessor/declaration
keywords. Computed properties support getters; native subscripts support all
three capabilities. `required` and `convenience` modify initializers; `some`
introduces an anonymous generic parameter type or an opaque return type. These words remain valid identifiers elsewhere.
`weak` and `move` are ordinary identifiers, with no storage/capture modifier role.

---

## Operators

### Arithmetic Operators

| Operator | Description |
|----------|-------------|
| `+` | Addition |
| `-` | Subtraction |
| `*` | Multiplication |
| `/` | Division |
| `%` | Remainder (modulo) |

### Comparison Operators

| Operator | Description |
|----------|-------------|
| `==` | Equal |
| `!=` | Not equal |
| `<` | Less than |
| `>` | Greater than |
| `<=` | Less than or equal |
| `>=` | Greater than or equal |

### Logical Operators

| Operator | Description |
|----------|-------------|
| `&&` | Logical AND |
| `\|\|` | Logical OR |
| `!` | Logical NOT when used as a prefix; propagation when used as a postfix on `Optional` or `Result` |

### Bitwise Operators

| Operator | Description |
|----------|-------------|
| `&` | Bitwise AND |
| `\|` | Bitwise OR |
| `^` | Bitwise XOR |
| `~` | Bitwise NOT |
| `<<` | Left shift |
| `>>` | Right shift |

### Assignment Operators

| Operator | Description |
|----------|-------------|
| `=` | Assignment |
| `:=` | New writable local with inferred type |
| `+=` | Add and assign |
| `-=` | Subtract and assign |
| `*=` | Multiply and assign |
| `/=` | Divide and assign |
| `%=` | Remainder and assign |
| `&=` | Bitwise AND and assign |
| `\|=` | Bitwise OR and assign |
| `^=` | Bitwise XOR and assign |
| `<<=` | Left shift and assign |
| `>>=` | Right shift and assign |

### Other Operators

| Operator | Description |
|----------|-------------|
| `->` | Arrow (return type, closure) |
| `=>` | Fat arrow (match arms) |
| `..` | Exclusive range |
| `..=` | Inclusive range |
| `...` | Variadic parameter or postfix spread |
| `?.` | Optional chaining |
| `??` | Nil coalescing |
| `\|>` | Pipe operator |
| `as` | Type cast |
| `as?` | Conditional existential cast |
| `is` | Existential type assertion |

---

## Punctuation

| Symbol | Usage |
|--------|-------|
| `(` `)` | Grouping, tuples, function calls |
| `[` `]` | Array/list/dictionary literals and types, generics |
| `{` `}` | Blocks, struct literals |
| `.` | Member access |
| `,` | List separator |
| `:` | Type annotation, labeled arguments |
| `;` | Statement terminator |
| `@` | Attributes |
| `#` | Inline configuration check: `#cfg(...)` |
| `_` | Wildcard pattern |

---

## Comments

```taro
// Single-line comment

/*
   Multi-line
   block comment
*/

/* Outer comment /* nested comment */ still inside the outer comment */
```

Block comments nest: every `/*` requires a matching `*/`. Reaching the end of
the file with an open comment is an error. Delimiters inside a block comment
count even if they appear within quoted text or after `//`. Newlines inside
comments participate in automatic semicolon insertion.
