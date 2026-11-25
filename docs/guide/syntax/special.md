# Special Syntax

This chapter covers automatic semicolon insertion, shorthands, and edge cases.

## Automatic Semicolon Insertion (ASI)

Taro automatically inserts semicolons, reducing syntactic noise while maintaining clarity.

### How ASI Works

A semicolon is inserted after certain tokens at a newline or end of file,
unless the next line starts with a continuation token or the newline is
directly inside parentheses or brackets.

### Newlines Inside Parentheses and Brackets

ASI tracks the innermost open delimiter. Directly inside `( )` or `[ ]`, a
newline never inserts a semicolon, so a multi-line list needs no comma before
its closing delimiter:

```taro
total := sum(
    first,
    second          // no trailing comma needed
)

matrix := [
    [1, 2, 3],
    [4, 5, 6]
]
```

Directly inside `{ }`, ASI works as usual, including braces nested inside
parentheses or brackets: blocks, closure bodies, `match` bodies and struct
literals. String interpolations `${ ... }` follow the same rule as braces.
After a closing delimiter, the enclosing delimiter's rule applies again.

```taro
result := compute(
    base
        + offset,       // `+` continues the line
    items.map(item => {
        log(item)       // statements inside braces still end at newlines
        item * 2
    })
)
```

Explicit semicolons inside brackets are unaffected: `[0; 20]` and
`[uint8; 20]` keep working, but the `;` must be written.

Because no semicolon separates the lines, a line that starts with `(` or `[`
directly inside `( )` or `[ ]` continues the previous line's expression as a
call or a subscript, and a line that starts with `&` or `*` continues it as a
binary operator. When an element's comma is missing, that changes the
meaning silently, so the compiler warns:

```taro
pairs := [
    first           // missing comma
    (second, third) // warning: this line continues the expression on the
]                   // previous line; add a ',' if a new element was meant
```

`[first(second, third)]` is still what the list contains. The `&` and `*`
case warns only when the operand follows without a space (`&flags`,
`*pointer`), which reads as a new reference or dereference element; `* scale`
is taken as a deliberate continuation. Method chains (`.name` at the start of
a line) and lines inside braces never warn. The warning comes from the
parser, so it is reported even when type errors follow, and only for the
package being compiled, not its dependencies.

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
x := a
    + b     // Continues the expression

y := a
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

**`else` and `where`:** `else` only follows an `if` block or a `guard`
condition, and `where` only opens a where clause or a `for` filter, so a line
that begins with either continues the previous line:
```taro
if ready {
    start()
}
else if retry {
    wait()
}
else {
    stop()
}

guard value > 0
else { return }

func largest[T](_ values: [T]) -> T
    where T: Ord {
    ...
}

for item in items
    where item.enabled {
    ...
}
```

### ASI Examples

```taro
// These are equivalent:
x := 1
y := 2

x := 1;
y := 2;

// Line continuation works:
sum := a
    + b
    + c     // All one expression

// This is TWO statements (not continuation):
a := 1
*ptr = 2    // '*' is unary dereference here, not continuation
```

### Important: `&` and `*` Don't Continue

Unlike some operators, `&` and `*` at line start are treated as unary operators:

```taro
x := value
&x              // A separate reference expression

y := value
*ptr = y        // Two statements! *ptr is dereference
```

### Important: `{` Doesn't Continue

An opening brace at the start of a line is not a continuation token. Keep the
`{` that opens a body on the line that ends its header, including after a
`where` clause:

```taro
func f() -> int32
{                   // Error: ASI already ended the declaration
    1
}
```

---

## Trailing Commas

Trailing commas are accepted in delimited argument, parameter, field, and
literal lists. Inside parentheses and brackets the trailing comma is always
optional. Inside braces, such as struct literals and import groups, a closing
`}` on a new line needs a comma after the final element, because otherwise ASI
inserts a semicolon. Enum variants within one `case` are an exception: they do
not allow a trailing comma.

```taro
// Arrays
[1, 2, 3,]

// Tuples
(a, b, c,)

// Function parameters
func foo(
    a: int32,
    b: string,
    c: bool,    // OK, and optional
) { }

// Function calls
foo(
    a: 1,
    b: "hello",
    c: true,    // OK
)

// Struct literals
Point {
    x: 1,
    y: 2,       // Required: `}` is on the next line
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
x := 1
y := 2

// Shorthand
point := Point { x, y }

// Equivalent to
point := Point { x: x, y: y }

// Mix of shorthand and explicit
point := Point { x, y: 10 }
```

### Optional Binding Shorthand

```taro
// Full form
if var value = optionalValue { }

// Shorthand when names match
if var optionalValue { }
// Same as: if var optionalValue = optionalValue { }
```

### Closure Shorthand

```taro
// Single expression body (no braces)
double := (x) => x * 2

// Empty parameters
random := () => generateRandom()
```

### Inferred Member Access

When type is known from context, enum variants and static members can be accessed with `.name`:

```taro
var color: Color = .red        // Inferred Color::red

match result {
    case .ok(v) => v           // Inferred Result::ok
    case .err(e) => panic(e)   // Inferred Result::err
}

func setColor(_ color: Color) { }
setColor(.blue)                // Inferred Color::blue

func reply() -> Result[Response, Error] {
    return .text(200, "ok")    // Response::text, then contextual .ok
}
```

In a Result context, lookup checks Result's own members first. A missing member
may resolve on its known success type. An existing outer overload set keeps
priority, even if none of its signatures accepts the arguments.

---

## Disambiguation

### Struct Literal vs Block

In some positions, `{` is ambiguous between struct literal and block:

```taro
// AMBIGUOUS in control flow conditions:
if User { isAdmin: true }.isAdmin { }  // Is `{` a literal or the body?
```

Bare struct literals are rejected in `if`/`while`/`guard` conditions, `for`
iterators and filters, and `match` scrutinees. Parentheses and other delimited
expressions lift this restriction within their delimiters:

```taro
if (User { isAdmin: true }).isAdmin { }   // parenthesized literal
if check(User { isAdmin: true }) { }      // literal inside a call argument
```

Collection literals, block expressions, and string interpolations also
provide delimiters. The restriction resumes after the closing delimiter:
`if check(true) && User { isAdmin: true }.isAdmin { }` is still rejected.
Alternatively, bind the value first:

```taro
admin := User { isAdmin: true }
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

Inside parentheses and brackets, commas separate elements and newlines are
ignored. Inside braces, **commas are required before newlines**, including
before a closing `}` on the following line:

```taro
// CORRECT: newlines inside brackets need no comma
arr := [
    1,
    2,
    3
]

// INCORRECT: the elements need separators
arr := [
    1
    2   // Error: expected `,` or `]`, found `2`
    3
]

// Braces: the final comma is required
point := Point {
    x: 1,
    y: 2,
}
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
(x) => x + 1       // Closure
a | b           // Bitwise OR

// Empty parameter closures use parentheses and an arrow.
() => doSomething()
```

### Range vs Member Access

```taro
0..10       // Range
x.y         // Member access

// No ambiguity due to spacing:
0 ..10      // Range (space before ..)
0.. 10      // Range (space after ..)
```
