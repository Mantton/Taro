# Patterns

This chapter covers all pattern types used in pattern matching, variable bindings, and destructuring.

## Where Patterns Are Used

Local `var` bindings accept identifiers, `_`, tuple patterns, and named struct patterns. A local binding must be irrefutable: it must
match every possible value of its type. Match arms and loop/binding conditions
accept additional patterns. Optional-binding conditions (`if var`, `while var`, `guard var`)
accept a single identifier; use `case` for destructuring in a condition:

```taro
// Variable declarations
pattern := expression
var pattern = expression

// Match arms
match value {
    case pattern => body
}

// For loops
for pattern in sequence { }

// If/while/guard conditions
if case pattern = expression { }
guard case pattern = expression else { }
```

---

## Wildcard Pattern

Matches anything and discards the value.

```taro
var _ = someValue        // Ignore the value

match result {
    case .ok(_) => "success"   // Ignore associated value
    case _ => "other"          // Match anything
}
```

---

## Identifier Pattern

Binds a value to a name.

```taro
x := 42                  // Binds 42 to 'x'

match opt {
    case .some(value) => value  // Binds to 'value'
    case .none => 0
}
```

---

## Tuple Pattern

Destructures tuples.

```taro
var (a, b) = (1, 2)

var (x, y, z) = point3d

match pair {
    case (0, 0) => "origin"
    case (x, 0) => "on x-axis"
    case (0, y) => "on y-axis"
    case (x, y) => "elsewhere"
}
```

---

## Rest Pattern

Matches remaining elements in a tuple.

```taro
var (first, ..) = tuple     // Match first, ignore rest

match triple {
    case (a, ..) => a          // Just get first element
}

// With other patterns
var (first, second, ..) = longTuple
```

---

## Path Pattern

Matches enum variants. A qualified constant such as `Limits::MAX` is not an
enum-variant pattern; use a literal or a guard to compare against constants.

### Qualified Path

Full path to the variant.

```taro
match result {
    case Result::ok(v) => v
    case Result::err(e) => panic(e)
}

match color {
    case Color::red => 0xFF0000
    case Color::green => 0x00FF00
    case Color::blue => 0x0000FF
}
```

### Inferred Path

Type inferred from context (common with enums).

```taro
match result {
    case .ok(v) => v
    case .err(e) => panic(e)
}

if case .some(value) = optional { }
```

### With Associated Values

```taro
match message {
    case .quit => exit()
    case .move(x, y) => moveTo(x, y)
    case .write(text) => print(text)
}
```

---

## Named Field Patterns

Structs and struct-style enum variants match fields by name. Fields can be
listed in any order; `name: pattern` renames or further destructures a field,
and a final `..` ignores omitted fields. Without `..`, every field is required.

```taro
match shape {
    case .rect { height, width: w } => w * height
    case .empty {} => 0
}
var Point { x, .. } = point
if case .rect { width, .. } = shape { print(width) }
```

Bindings are writable value copies. Matching a reference automatically reads
its target; changing a binding does not change the source’s inline fields.
Class and reference values still share their targets. Reference patterns are
not supported. Tuple variants use parentheses; struct-style variants use braces.
Classes cannot be destructured with named patterns.

---

## Or Pattern

Matches if any alternative matches. Or-patterns are supported at the top
level of a match arm. Alternatives must bind the same names with compatible
types.

```taro
match value {
    case 1 | 2 | 3 => "small"
    case 4 | 5 | 6 => "medium"
    case _ => "large"
}

match result {
    case .ok(v) | .cached(v) => use(v)
    case .err(e) => panic(e)
}
```

---

## Literal Pattern

Matches specific literal values. Integer and floating-point patterns may have
a leading minus sign, such as `case -1` or `case -1.5`. Integer patterns must
fit their type, including signed minima such as `-128_i8`; negative patterns
cannot match unsigned integer types. Literal alternatives can use `|`, as in
`case -1 | 0 | 1`.

General expressions such as `-(1 + 2)` and f-strings with interpolation are
not literal patterns. Use a guard when a comparison requires computation.

```taro
match x {
    case 0 => "zero"
    case 1 => "one"
    case 42 => "answer"
    case _ => "other"
}

match char {
    case 'a' => "first"
    case 'z' => "last"
    case _ => "middle"
}

match name {
    case "Alice" => greetAlice()
    case "Bob" => greetBob()
    case _ => greetStranger()
}
```

---

## Value Bindings and References

All pattern bindings are writable value copies, including bindings introduced
by `match` and `if case`. Editing an inline payload binding does not edit the
source enum. Copies of class, List, and reference values still share their
targets, as with ordinary assignment.

Structural match/if-case patterns automatically read through reference layers.
Payload bindings remain values; explicit dereferencing is also accepted:

```taro
var optional: int32? = .some(42)
reference := &optional
match reference {
    case .some(value) => {
        value += 1 // Changes the local copy; optional still contains 42.
    }
    case .none => {}
}
if case .some(value) = reference { value = 0 }
```

`&pattern` is removed. Enum, tuple and literal patterns automatically read
referents, including nested structural patterns. A plain identifier pattern
copies the matched reference value itself; it does not read the pointee.
Use ordinary dereferencing for local values, such as `var copy = *reference`.

Matching can inspect the discriminant and bind selected fields directly from
existing storage; explicit dereferencing does not require copying the whole
enum. Guarded matches conservatively snapshot the scrutinee before testing
arms, because a guard can replace the source through an alias. Each candidate's
guard and body share the same binding copies; a failed guard discards them.
There are no runtime borrow checks or reference protection tokens.

---

## Nested Patterns

Patterns can be nested for complex destructuring.

```taro
// Nested tuples
var ((a, b), (c, d)) = nestedTuple

// Enum with tuple
match result {
    case .ok((x, y)) => Point { x, y }
    case .err(msg) => panic(msg)
}

// Complex nesting
match data {
    case .user(name, .premium(level)) => "Premium user: " + name
    case .user(name, .free) => "Free user: " + name
    case .guest => "Guest"
}
```

---

## Pattern Guards

Additional conditions on match arms.

```taro
match value {
    case n if n > 100 => "large"
    case n if n > 10 => "medium"
    case n if n > 0 => "small"
    case 0 => "zero"
    case n => "negative"
}

match point {
    case (x, y) if x == y => "diagonal"
    case (x, 0) => "on x-axis"
    case (0, y) => "on y-axis"
    case (x, y) => "general"
}
```

---

## Exhaustiveness

Match expressions must be exhaustive—all possible values must be covered.

```taro
enum Switch { case on, off; }
var state: Switch = .on

// Must cover all cases
match state {
    case .on => 1
    case .off => 0
    // Compiler ensures exhaustiveness
}

// Wildcard makes it exhaustive
match number {
    case 0 => "zero"
    case _ => "non-zero"  // Covers everything else
}
```

## Conditional Value Bindings and Scope

Conditional patterns preserve their source on both success and failure.
Their bindings are writable value copies, with the same shallow sharing rules
as ordinary assignment. Structural matching automatically reads references.

```taro
struct Token { value: int32 }
enum State { case empty; case token(Token) }

func main() {
    var state: State = .token(Token { value: 1 })
    if case .token(token) = &state {
        token.value += 1 // Edits the binding copy.
    }
    if case .token(original) = state {
        assert(original.value == 1, "source is unchanged")
    }
    guard case .token(saved) = state else { return }
    state = .empty
    assert(saved.value == 1, "guard binding is independent of the source")
}
```

Bindings introduced by `if` and each `while` iteration have their branch's
lexical scope. A successful `guard` makes its bindings available to subsequent
statements and defer blocks. References that escape to a binding copy keep its
GC storage alive independently of that lexical scope. Failed match guards do
not write their binding copies back to the scrutinee; the successful arm uses
the same copies that its guard inspected or edited.
