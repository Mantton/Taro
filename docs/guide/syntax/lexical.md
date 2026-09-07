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
let myVariable = 10
let _private = 20
let camelCase = 30

// Escaped identifiers (for reserved words)
let `type` = "string"
let `func` = 42
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

Strings are enclosed in double quotes and support escape sequences.

```taro
"Hello, World!"
"Line 1\nLine 2"           // Newline
"Tab\there"                 // Tab
"Quote: \"hello\""          // Escaped quote
"Backslash: \\"             // Escaped backslash
"Unicode: \u{1F600}"        // Unicode escape
```

Strings and runes also accept `\r`, `\0`, and ASCII hexadecimal escapes such as
`\x41`. Unicode escapes must name a Unicode scalar value. The current lexer accepts LF
line endings but rejects raw carriage returns, including CRLF line endings.
This is an implementation limitation; use LF when compiling with the current compiler.

### F-String Literals

F-strings are prefixed with `f` and support interpolation with `{expr}`.

```taro
let name = "Ada"
let score = 7
f"Hello, {name} (score={score})"
f"sum={score + 5}"          // Full expression support
f"{{ok}}"                   // Escaped braces -> "{ok}"
```

Rules:
- Use `{expr}` for interpolation.
- Use `{{` and `}}` for literal braces.
- F-strings are single-line, like normal strings.

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
for         func        guard       if          impl        import
in          init        interface   let         loop        match
mod         namespace   nil         operator    private     public      readonly
return      static      struct      true        type        var
where       while       mut         unsafe
```

`init` is reserved and cannot be used as an identifier or declared as a method,
but it is accepted at member-access position. Taro has no `init` declaration
form: initializers are static `new` methods, reachable through the type-call
shorthand described in [Declarations](./declarations.md#initializer-shorthand).

### Future Reserved Keywords

These keywords are reserved for future use:

```
class       final       override    fileprivate protected ref
```

### Contextual Keywords

`get` and `set` are contextual keywords for computed-property accessor blocks.
`move` is contextual before a closure, and `some` is contextual in an opaque
return type. They remain valid identifiers elsewhere.

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
| `...` | Variadic parameter |
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

/* Block comments end at the first closing delimiter. */
```

The current lexer does not implement nested block comments: the first `*/`
closes the comment. Earlier documentation described nesting, so this remains
a discrepancy between the documented language and its implementation.
