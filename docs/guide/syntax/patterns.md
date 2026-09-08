# Patterns

This chapter covers all pattern types used in pattern matching, variable bindings, and destructuring.

## Where Patterns Are Used

Local `let`/`var` bindings accept identifiers, `_`, tuple patterns, and reference
patterns at the outermost level. A local binding must be irrefutable: it must
match every possible value of its type. Match arms and loop/binding conditions
accept additional patterns. Optional-binding conditions (`if let`, `while let`, `guard let`)
accept a single identifier; use `case` for destructuring in a condition:

```taro
// Variable declarations
let pattern = expression
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
let _ = someValue           // Ignore the value

match result {
    case .ok(_) => "success"   // Ignore associated value
    case _ => "other"          // Match anything
}
```

---

## Identifier Pattern

Binds a value to a name.

```taro
let x = 42                  // Binds 42 to 'x'

match opt {
    case .some(value) => value  // Binds to 'value'
    case .none => 0
}
```

---

## Tuple Pattern

Destructures tuples.

```taro
let (a, b) = (1, 2)

let (x, y, z) = point3d

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
let (first, ..) = tuple     // Match first, ignore rest

match triple {
    case (a, ..) => a          // Just get first element
}

// With other patterns
let (first, second, ..) = longTuple
```

---

## Path Pattern

Matches enum variants. A qualified constant such as `Limits.MAX` is not an
enum-variant pattern; use a literal or a guard to compare against constants.

### Qualified Path

Full path to the variant.

```taro
match result {
    case Result.ok(v) => v
    case Result.err(e) => panic(e)
}

match color {
    case Color.red => 0xFF0000
    case Color.green => 0x00FF00
    case Color.blue => 0x0000FF
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

## Reference Pattern

An explicit `&pattern` matches through one reference layer. Its inner
bindings have the pointee types, rather than gaining another reference:

```taro
let value = 42
match &value {
    case &x => {
        let copied: int32 = x
    }
}
```

`&const pattern` is the explicit immutable spelling. `&mut pattern` requires a
mutable reference. Reference patterns also work in local bindings, including
inside tuples:

```taro
func main() {
    let value = 42
    let &copy = &value
    let (&nested,) = (&value,)
    let &(first, second) = &(19, 23)
    assert(copy == nested && first + second == 42, "reference bindings")
}
```

`let` or `var` controls whether the new bindings can be reassigned. The `mut`
in `let &mut x = ...` describes the reference being matched; it does not make
`x` a mutable binding. Copying a pointee does not modify the referenced value,
and a non-`Copy` value cannot be moved through an immutable reference.

Match arms and `case` conditions retain a different binding rule: an explicit
`&mut pattern` makes its inner bindings mutable. The `let`/`var` rule above
applies to local declarations.

Without an explicit reference pattern, matching an enum or tuple through a
reference automatically borrows the payload bindings:

```taro
let optional: int32? = .some(42)
match &optional {
    case .some(v) => {
        let borrowed: &int32 = v
    }
    case .none => {}
}
```

---

## Nested Patterns

Patterns can be nested for complex destructuring.

```taro
// Nested tuples
let ((a, b), (c, d)) = nestedTuple

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
let state: Switch = .on

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
