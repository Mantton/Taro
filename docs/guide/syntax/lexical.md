# Lexical Elements

This chapter covers the fundamental building blocks of Taro source code.

## Identifiers

Identifiers name variables, functions, types, and other program elements.

```ebnf
identifier ::= letter { letter | digit }
             | '`' escaped_identifier_char+ '`'

letter     ::= 'a'..'z' | 'A'..'Z' | '_'
digit      ::= '0'..'9'
```

### Examples

```taro
// Standard identifiers
let myVariable = 10
let _private = 20
let camelCase = 30

// Escaped identifiers (for reserved words)
let `type` = "string"
let `func` = someFunction
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
any         as          break       case        const       continue
defer       else        enum        export      extern      false
for         func        guard       if          impl        import
in          init        interface   let         loop        match
namespace   nil         operator    private     public      readonly
return      static      struct      true        type        var
where       while       mut
```

### Future Reserved Keywords

These keywords are reserved for future use:

```
class       final       override    fileprivate protected
async       await       ref
```

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
| `===` | Pointer equality |

### Logical Operators

| Operator | Description |
|----------|-------------|
| `&&` | Logical AND |
| `\|\|` | Logical OR |
| `!` | Logical NOT |

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
| `=>` | Fat arrow (match arms, shorthand if) |
| `..` | Exclusive range |
| `..=` | Inclusive range |
| `...` | Variadic parameter |
| `?` | Optional unwrap |
| `?.` | Optional chaining |
| `??` | Nil coalescing |
| `\|>` | Pipe operator |
| `as` | Type cast |

---

## Punctuation

| Symbol | Usage |
|--------|-------|
| `(` `)` | Grouping, tuples, function calls |
| `[` `]` | Arrays, subscripts, generics |
| `{` `}` | Blocks, struct literals |
| `.` | Member access |
| `,` | List separator |
| `:` | Type annotation, labeled arguments |
| `;` | Statement terminator |
| `@` | Attributes |
| `_` | Wildcard pattern |

---

## Comments

```taro
// Single-line comment

/*
   Multi-line
   block comment
*/

/* Nested /* comments */ are supported */
```
