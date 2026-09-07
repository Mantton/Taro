# Special Syntax

This chapter covers automatic semicolon insertion, shorthands, and edge cases.

## Automatic Semicolon Insertion (ASI)

Taro automatically inserts semicolons, reducing syntactic noise while maintaining clarity.

### How ASI Works

A semicolon is inserted after certain tokens at a newline or end of file,
unless the next line starts with a continuation token. ASI also runs inside
parentheses and brackets.

### Tokens That Can End a Statement

Semicolons are inserted after:
- Identifiers: `foo`, `myVar`
- Literals: `42`, `"string"`, `true`, `false`, `nil`
- Keywords: `break`, `continue`, `return`
- Closing brackets: `)`, `]`, `}`
- Special: `?`, `!`, and the import/export suffix `.*`

### Line Continuation Tokens

These tokens at the start of a line prevent ASI:

**Binary operators:**
```taro
let x = a
    + b     // Continues the expression

let y = a
    - b * c
```

**Comparison operators:**
```taro
if value
    == expected {   // Continues
}
```

**Member access and chaining:**
```taro
result
    .map(f)
    .filter(g)
    .collect()

optional
    ?.property
    ?.method()
```

**Assignment operators:**
```taro
x
    += 1    // Continues
```

**Arrow operators:**
```taro
func process()
    -> int32 {   // Continues
    42
}
```

### ASI Examples

```taro
// These are equivalent:
let x = 1
let y = 2

let x = 1;
let y = 2;

// Line continuation works:
let sum = a
    + b
    + c     // All one expression

// This is TWO statements (not continuation):
let a = 1
*ptr = 2    // '*' is unary dereference here, not continuation
```

### Important: `&` and `*` Don't Continue

Unlike some operators, `&` and `*` at line start are treated as unary operators:

```taro
let x = value
&x              // A separate reference expression

let y = value
*ptr = y        // Two statements! *ptr is dereference
```

`else` and `where` are not continuation starters. Keep `else` on the same
line as the preceding `}`: `} else {` or `} else if condition {`. Likewise,
start a function's `where` clause on the line containing its return type or
closing parameter delimiter.

---

## Trailing Commas

Trailing commas are accepted in delimited argument, parameter, field, and
literal lists. If the closing delimiter starts on a new line, the final
element needs a comma too, because otherwise ASI inserts a semicolon.
Enum variants within one `case` are an exception: they do not allow a trailing
comma.

```taro
// Arrays
[1, 2, 3,]

// Tuples
(a, b, c,)

// Function parameters
func foo(
    a: int32,
    b: string,
    c: bool,    // OK
) { }

// Function calls
foo(
    1,
    "hello",
    true,       // OK
)

// Struct literals
Point {
    x: 1,
    y: 2,       // OK
}

// Generics
Dictionary[
    string,
    int32,      // OK
]

// Enum cases
enum Color {
    case red,
         green,
         blue    // No trailing comma on an enum case
}
```

---

## Shorthands

### Struct Field Shorthand

When field name matches variable name:

```taro
let x = 1
let y = 2

// Shorthand
let point = Point { x, y }

// Equivalent to
let point = Point { x: x, y: y }

// Mix of shorthand and explicit
let point = Point { x, y: 10 }
```

### Optional Binding Shorthand

```taro
// Full form
if let value = optionalValue { }

// Shorthand when names match
if let optionalValue { }
// Same as: if let optionalValue = optionalValue { }
```

### Closure Shorthand

```taro
// Single expression body (no braces)
let double = |x| x * 2

// Empty parameters
let random = || generateRandom()
```

### Inferred Member Access

When type is known from context, enum variants and static members can be accessed with `.name`:

```taro
let color: Color = .red        // Inferred Color.red

match result {
    case .ok(v) => v           // Inferred Result.ok
    case .err(e) => panic(e)   // Inferred Result.err
}

func setColor(_ color: Color) { }
setColor(.blue)                // Inferred Color.blue
```

---

## Disambiguation

### Struct Literal vs Block

In some positions, `{` is ambiguous between struct literal and block:

```taro
// AMBIGUOUS in control flow conditions:
if User { isAdmin: true }.isAdmin { }  // Is `{` a literal or the body?
```

Struct literals are rejected anywhere inside an `if`, `while`, or `guard`
condition — including nested in parentheses or a call argument. All of these
fail with *struct literals are not allowed in this context*:

```taro
if (User { isAdmin: true }).isAdmin { }   // parentheses do not help
if check(User { isAdmin: true }) { }      // nor does a call argument
```

Bind the value first:

```taro
let admin = User { isAdmin: true }
if admin.isAdmin { }
```

Conditions must also be `bool`; there is no truthiness conversion.

### Type Cast vs Comparison

The `as` keyword binds tighter than comparison:

```taro
x as int32 < y     // (x as int32) < y
x < y as int32     // x < (y as int32)
```

### Square Brackets Are Always Generics

After an expression, `[` `]` is always type specialization. Taro has no subscript
operator, so there is nothing to disambiguate:

```taro
List[int32]         // Type specialization
identity[string]    // Type specialization

list[0]             // Rejected — parsed as specializing `list` with `0`
```

Element access uses `.get()` and `.at()` instead. See
[Expressions](./expressions.md#element-access).

---

## Semicolon-Separated Lists

Some constructs use semicolons as separators:

| Construct | Separator | Example |
|-----------|-----------|---------|
| Struct fields | `;` | `x: int32; y: int32;` |
| Enum cases | `;` | `case a; case b;` |
| Match arms | `;` (via ASI) | `case .a => 1; case .b => 2;` |

```taro
struct Point {
    x: int32;
    y: int32;
}

enum Status {
    case ok;
    case pending;
    case error(string);
}
```

---

## Comma-Separated Lists and Newlines

For delimited comma-separated lists, **commas are required before newlines**,
including before a closing delimiter on the following line:

```taro
// CORRECT: Trailing comma before newline
let arr = [
    1,
    2,
    3,
]

// INCORRECT: ASI would insert semicolon!
let arr = [
    1
    2   // Error! Semicolon inserted after 1
    3
]
```

---

## Edge Cases

### Empty Tuple vs Unit

```taro
()      // Empty tuple / unit type
(x)     // Parenthesized expression (NOT a tuple)
(x,)    // Single-element tuple
```

### Optional Type Precedence

```taro
*int32?     // Pointer to optional: *( int32? )
(*int32)?   // Optional pointer
[int32]?    // Optional list
[int32?]    // List of optionals
```

### Closure vs Bitwise OR

```taro
|x| x + 1       // Closure
a | b           // Bitwise OR

// Closure at start of expression uses ||
|| doSomething()    // Empty parameter closure
```

### Range vs Member Access

```taro
0..10       // Range
x.y         // Member access

// No ambiguity due to spacing:
0 ..10      // Range (space before ..)
0.. 10      // Range (space after ..)
```
