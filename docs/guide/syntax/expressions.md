# Expressions

This chapter covers all expression types in Taro, organized by precedence (lowest to highest).

## Expression Precedence

From lowest to highest precedence:

1. Assignment: `=`, `+=`, `-=`, etc.
2. Pipe: `|>`
3. Ternary: `? :`
4. Nil-coalescing: `??`
5. Range: `..`, `..=`
6. Logical OR: `||`
7. Logical AND: `&&`
8. Comparison: `<`, `>`, `<=`, `>=`, `==`, `!=`
9. Bitwise OR: `|`
10. Bitwise XOR: `^`
11. Bitwise AND: `&`
12. Bit shift: `<<`, `>>`
13. Term: `+`, `-`
14. Factor: `*`, `/`, `%`
15. Cast / Type Assertion: `as`, `as?`, `is`
16. Prefix: `!`, `-`, `~`, `&`, `*`
17. Postfix: `.`, `()`, `[]` (specialization or indexing), `!`, `?.`
18. Primary

`await` scopes the following expression. Async calls complete before their results
are used: `await operation() + 1` and `await operation()!`.

---

## Primary Expressions

### Literals

```taro
42                  // Integer
3.14                // Float
"hello"             // String
f"hello, {name}"    // Interpolated string (f-string)
'a'                 // Rune
true                // Bool
false               // Bool
nil                 // Nil
```

### Identifiers

```taro
foo
myVariable
_privateVar
```

### Inferred Member

Access enum variant or static member without type prefix.

```taro
.some(value)        // Inferred enum variant
.none               // Inferred enum variant
.MAX_VALUE          // Inferred static constant
```

If a new line begins with `.`, it is treated as postfix continuation of the previous expression unless the previous statement is explicitly terminated.

```taro
out := value
.some(out)          // parsed as: value.some(out)

out := value;
.some(out)          // standalone inferred member expression
```

### Wildcard

`_` discards a value in a binding pattern (`var _ = expression`). As an
expression, it is only supported as one top-level argument placeholder on the
right-hand side of a pipe:

```taro
value |> combine(other, _)   // combine(other, value)
```

A standalone `_`, a nested placeholder, or multiple placeholders is rejected.

### Parenthesized Expression

```taro
(a + b) * c
(complexExpression)
```

---

## Tuple Expressions

```taro
()                  // Empty tuple (unit)
(1,)                // Single-element tuple
(1, 2)              // Two-element tuple
(1, 2, 3)           // Three-element tuple
(a, b, c,)          // Trailing comma allowed
```

---

## List and Array Expressions

```taro
var list: [int32] = [1, 2, 3]
var empty: [int32] = []
var array: [int32; 3] = [1, 2, 3]

// Repeat expressions construct fixed-size arrays, with a constant count.
var zeros: [int32; 10] = [0; 10]
```

Element literals default to fixed-size arrays when no collection type is
determined by context. An expected `List[T]` type selects list construction,
including when a generic call's other arguments or result determine that type:

```taro
var values: [int32] = [1, 2, 3]
func assign[T](_ destination: &T, _ value: T) { *destination = value }
previous := values
assign(&values, [])
// values selects a new empty list; previous keeps the original handle.
```

This applies to literals, not to existing array values: passing an array does
not implicitly convert it into a list. `[value; count]` requires a compile-time
count and constructs an array; it does not construct a dynamic list.

---

## Dictionary Expressions

```taro
[:]                 // Empty dictionary
["a": 1, "b": 2]    // Dictionary with pairs
[
    "key1": value1,
    "key2": value2,  // Trailing comma allowed
]
```

---

## Struct and Named Variant Literals

```taro
Point { x: 1, y: 2 }

// Shorthand (field name matches variable name)
x := 1
y := 2
Point { x, y }      // Same as Point { x: x, y: y }

// Mixed
Point { x, y: 10 }

// Trailing comma
Point { x: 1, y: 2, }
```

Named enum variants use the same braces, in any field order. A leading dot
infers the enum type from context:

```taro
enum Shape[T] { case rect { width: T, height: T }; case empty {} }
var shape: Shape[int64] = .rect { height: 4, width: 3 }
shape = Shape::rect { width: 5, height: 6 }
shape = .empty {}
```

Duplicate, unknown, and missing required fields are errors. Tuple and unit
variants do not accept braces. Labeled constructor calls such as
`Shape::rect(width: 5, height: 6)` remain callable constructors.

Struct updates use a final `..base` to copy every omitted field:

```taro
var original = Point { x: 1, y: 2 }
var changed = Point { x: 3, ..original }  // y is copied from original
var x = 4
var shorthand = Point { x, ..original }
```

Explicit field expressions evaluate left to right in source order, followed by
one evaluation of the base. The base must have exactly the resulting struct
type; a reference needs an explicit read, as in `..*reference`. Omitted fields
come from the base even when the declaration has field defaults. Inline fields
are value copies; copied references and class handles retain their shared
targets. No `Clone` conformance is needed. A place base is read through its
omitted field projections, without an extra whole-struct copy.

Updates require every field to be visible. They apply only to structs without
`init`: a struct declaring an initializer must use it, and accepts no literal
form, including updates. Classes and enum variants reject update syntax.
Destructure an enum and reconstruct its variant explicitly instead. If every
field is already supplied, the redundant base emits a warning and still
evaluates once. The base must appear once, after all explicit fields; a trailing
comma is allowed.

In `if`/`while`/`guard` conditions, `for` iterators and filters, and `match`
scrutinees, put struct literals inside parentheses or another delimited
expression, such as a call argument or collection literal. This distinguishes
the literal's braces from the control-flow body. For example,
`if (Flag { enabled: true }).enabled { }` is accepted. See
[Special Syntax](./special.md#struct-literal-vs-block).

---

## Block Expressions

Blocks can be used as expressions; the value is the last expression.

```taro
result := {
    a := compute()
    b := process(a)
    a + b   // This is the block's value
}
```

---

## Prefix (Unary) Expressions

```taro
!flag               // Logical NOT
-value              // Negate
~bits               // Bitwise NOT

&value              // Take a writable GC reference

*pointer            // Dereference
```

Unary `*` reads one reference or raw-pointer level. On another type it calls
its `Deref` implementation and reads the referenced target. A storage receiver
uses the same auto-reference rule as other receiver methods:

```taro
struct Point { x: int32 }
struct Wrapper { point: Point }
conform &Wrapper to Deref {
    type Target = Point
    func deref() -> &Point { &self.point }
}
var wrapper = Wrapper { point: Point { x: 1 } }
wrapper.x = 2
copy := *wrapper          // Point value copy
address := &wrapper.x    // Reference into the original target
```

Member lookup tries the wrapper's own fields and methods first, then follows
`deref()` one step at a time. This includes numeric tuple fields. Each step is
an ordinary method call, evaluated once; cycles and paths beyond 32 steps are
compiler diagnostics. Private own members retain their visibility restrictions.
Deref provides unary `*` and member lookup; interface bounds and argument type
checks still apply to the wrapper's own type. Match patterns keep their existing
reference auto-dereference and value-binding rules.

An inline wrapper can implement `Deref` on `&Wrapper` to expose its actual
storage. A wrapper carrying a shared handle or reference can implement it by
value. Erased `any Deref` values need a known `Target` binding for target reads.

---

## Postfix Expressions

### Member Access

```taro
object.field
object.method()
user.profile.name
```

Computed properties are also accessed through member syntax:

```taro
counter.value        // getter read
counter.value = 10   // stored-field assignment; computed getters cannot be assigned
```

Computed getters are synchronous. Async operations use methods with an enclosing
`await` expression.

### Tuple Access

```taro
tuple.0             // First element
tuple.1             // Second element
```

### Function Calls

```taro
foo()                       // No arguments
foo(1, 2, 3)               // Positional arguments
foo(a: 1, b: 2)            // Labeled arguments
foo(1, named: 2)           // Mixed
foo(arg1, arg2,)           // Trailing comma allowed
```

### Element Access

Subscripts are native `get`, `set` and `address` declarations. Reads copy the
result. List, array and Span element subscripts expose writable storage through
`&values[index]`; references keep the original allocation alive after growth or
clear. Shifting or replacing slots can change their contents: a reference tracks
storage, not an element's logical identity.

```taro
var values: List[int32] = [3_i32, 5_i32]
first := &values[0]
values[0] = 7
values[0] += values[0]
assert(*first == 14, "reference observes the stored element")
```

Dictionary brackets take a key value. Reads panic for a missing key, while
assignment inserts or replaces. Numeric compound assignment requires a successful
read. `get(&key)` returns an optional value copy for expected absence. A dictionary
has no entry address accessor, so `&dictionary[key]` and nested writes into inline
payloads are rejected. Copied class, list and reference values retain their
ordinary shared targets.

```taro
var counts: [string: int32] = [:]
counts["visits"] = 3
counts["visits"] += 1
snapshot := counts.get(&"visits").unwrap()
assert(snapshot == 4 && counts.get(&"missing").isNone(), "value lookup")
```

Array and List ranges (`values[start..end]` or `values[start..=last]`) produce a
new List with copied elements. Span ranges share a Span view of the same storage.
Bounds are checked, reversed ranges panic, and an empty half-open range at the
logical end is valid. Taking a reference to an Array element requires addressable
array storage, following ordinary reference receiver rules.

List, array and Span retain explicit `at` reference and optional `get` reference
methods. Native indexing supports multiple arguments, range values, nested
subscripts and callable elements. Assignment snapshots RHS before evaluating its
receiver and indices, once each. A user-defined interface can require native
capabilities for generic or erased indexing. Generic specialization uses the same
brackets, as in `identity[int32](3)` and `List[int32]`.

When an annotation fixes a List, array, or tuple element type, each initializer
receives the same value conversions as a local binding. For example, a
`List[any Read]` literal can contain different owned values implementing `Read`.
This follows ordinary copy/move rules; it does not introduce shared identity for
struct values. An unannotated array literal still infers one exact element type.

### Type Specialization

```taro
List[int32]
identity[string]
Result[User, Error]
```

### Propagation

```taro
optionalValue!      // Extract T from Optional[T], or return .none
resultValue!        // Extract T from Result[T, E], or return .err(error)
```

`expr!` is only valid for `Optional[T]` and `Result[T, E]`.

- `Optional[T]!` requires the enclosing function, closure, or default-value provider to return `Optional[_]`.
- `Result[T, E]!` requires the enclosing function, closure, or default-value provider to return `Result[_, TargetE]`.
- When `E` and `TargetE` are identical, propagation forwards the error directly.
  Otherwise, `TargetE` must implement `From[E]`; propagation calls that
  conversion before returning `.err`.
- `Optional` and `Result` do not mix. You cannot propagate an `Optional` from a `Result` context or vice versa.
- To propagate an awaited value, write `await expr!` or `(await expr)!`.

### Optional Chaining

```taro
user?.profile?.name
object?.method()
```

---

## Binary Expressions

### Arithmetic

```taro
a + b               // Addition
a - b               // Subtraction
a * b               // Multiplication
a / b               // Division
a % b               // Remainder
```

### Comparison

```taro
a == b              // Equal
a != b              // Not equal
a < b               // Less than
a > b               // Greater than
a <= b              // Less or equal
a >= b              // Greater or equal
```

### Logical

```taro
a && b              // Logical AND (short-circuit)
a || b              // Logical OR (short-circuit)
```

### Bitwise

```taro
a & b               // Bitwise AND
a | b               // Bitwise OR
a ^ b               // Bitwise XOR
a << n              // Left shift
a >> n              // Right shift
```

---

## Assignment Expressions

```taro
x = value           // Simple assignment

// Compound assignments
x += 1              // Add and assign
x -= 1              // Subtract and assign
x *= 2              // Multiply and assign
x /= 2              // Divide and assign
x %= 3              // Remainder and assign
x &= mask           // Bitwise AND and assign
x |= flags          // Bitwise OR and assign
x ^= bits           // Bitwise XOR and assign
x <<= 1             // Left shift and assign
x >>= 1             // Right shift and assign
```

For user-defined types, compound assignments use the distinct `AddAssign`,
`SubAssign`, `MulAssign`, `DivAssign`, `RemAssign`, `BitAndAssign`, `BitOrAssign`,
`BitXorAssign`, `ShlAssign`, and `ShrAssign` interfaces rather than their
value-producing operator interfaces.

An operator selects its designated interface using the receiver and RHS types.
A same-named inherent method does not enable the operator. The RHS is passed as
the interface declares it; it is not automatically borrowed. Result-producing
interfaces declare an associated `Output` type, which defaults to `Self` but can
be overridden. A generic function that requires that equality must state it:

```taro
func sum[T: Add[T, Output = T]](_ left: T, _ right: T) -> T {
    left + right
}
```

The RHS is evaluated first, then the receiver is evaluated once. Custom compound
operators follow ordinary method receiver rules: an implementation on `&T` can
change the original storage, while a class or shared-handle value can mutate
shared state. There is no fallback from `+=` to `+` followed by assignment, and
no implicit writeback of a value receiver. `counter += counter` is allowed.

Built-in numeric compound assignment writes back to its destination and requires
writable storage or a native subscript setter. A custom value receiver can operate on a
getter result without a setter. As with named methods, `readonly` blocks direct
assignment to a stored field; it does not make references or referenced objects
immutable. A reference receiver still requires addressable storage.

---

## Range Expressions

```taro
1..10               // Exclusive range [1, 10)
1..=10              // Inclusive range [1, 10]
start..end
start..=end
```

---

## Nil Coalescing

Provide a default value for optionals.

```taro
optional ?? default
user?.name ?? "Unknown"
getValue() ?? computeDefault()
```

---

## Ternary Expression

```taro
condition ? thenValue : elseValue

x > 0 ? "positive" : "non-positive"
```

---

## Pipe Expression

Chain function calls in a readable left-to-right style.

```taro
data |> transform |> validate |> save

// Equivalent to:
save(validate(transform(data)))
```

---

The left value is inserted as the first argument when the right side is a
call without a placeholder: `value |> transform(extra)` means
`transform(value, extra)`. One direct `_` argument can select another position.

## Cast Expression

```taro
value as int64
number as double
unsafe { ptr as *uint8 }
```

---

## If Expression

If-else as an expression (returns a value).

```taro
result := if condition { value1 } else { value2 }

// Chained
status := if x > 0 {
    "positive"
} else if x < 0 {
    "negative"
} else {
    "zero"
}

// If without else has unit type; the body must produce unit or diverge.
if condition { doSomething() }
```

---

## Match Expression

Pattern matching expression.

```taro
match value {
    case pattern1 => result1
    case pattern2 => result2
    case _ => defaultResult
}

// With guards
match x {
    case n if n > 0 => "positive"
    case n if n < 0 => "negative"
    case _ => "zero"
}

// Block bodies
match opt {
    case .some(v) => {
        process(v)
        v * 2
    }
    case .none => 0
}
```

---

## Closure Expressions

Anonymous functions.

```taro
// Basic closure
(x) => x * 2

// Empty parameters
() => 42

// Multiple parameters
(a, b) => a + b

// With type annotations
(x: int32, y: int32) -> int32 => x + y

// Block body
(x) => {
    y := x * 2
    y + 1
}

// Explicit async closure
() async => {
    await std::testing::yieldNow()
    42 as int32
}

// Contextual async inference for inline call arguments
std::task::spawn(() => {
    await std::testing::yieldNow()
    42 as int32
})

// Trailing comma allowed
(a, b,) => a + b
```

Closure literals share their captured variables. Reading after an outer write
observes the new value, and closure writes are visible to the enclosing code.
The GC retains escaping variable storage. Copies of a closure share that state.
There is no `move` capture mode.

Named inline fields may be captured separately; overlapping paths merge. Class
field access captures the class variable so later handle rebinding is observed.
`Fn` and `AsyncFn` both support repeated stateful calls. Async calls require an
enclosing `await` expression; independent tasks can invoke the same callable,
using explicit synchronization when their shared writes need ordering.

### Bound methods

`value.method` evaluates its receiver once. A value receiver copies its value;
a reference receiver retains the selected storage; a class receiver retains the
selected object. Rebinding a class or reference variable does not retarget the
callback. Closure literals such as `() => value.method()` reread the variable
on each call. Both synchronous and asynchronous method values are repeatable.
Callback arguments are positional and omit the already bound receiver.

```taro
struct Counter { value: int32 }
extend Counter {
    func read() -> int32 { self.value }
}
extend &Counter {
    func add(_ amount: int32) { self.value += amount }
}
func main() {
    var counter = Counter { value: 7 }
    read := counter.read
    add := counter.add
    add(2)
    assert(read() == 7, "value receiver captured once")
    assert(counter.value == 9, "reference receiver retains selected storage")
}
```

A reference receiver and its bound callback keep their selected GC storage
alive, including when the callback escapes. An async method produces an async
callback; extraction does not need `await`, while invocation does. A generic
method value needs its argument types from the context at creation. There are
no callable borrowing or Escapable bounds.

---

## Opaque Return Types

`some Interface` hides a function's concrete return type while preserving its
interface conformances:

```taro
func makeNamed() -> some Named {
    HiddenName { value: "Taro" }
}
```

Every return path must resolve to the same hidden concrete type. Callers can use
the declared interfaces, but cannot name or depend on that concrete type. Opaque
return types also work across package boundaries and on async functions.

---

## Binding Conditions

Special expressions for pattern matching in conditions.

### Case Binding

```taro
if case .some(value) = optional {
    use(value)
}

while case .some(item) = iterator.next() {
    process(item)
}
```

### Optional Binding Shorthand

```taro
if var value = optional {
    use(value)
}

// Shorthand (same name)
if var value {
    use(value)
}

guard var value = optional else { return }
```

### Qualified and instance access

Use `::` for module, namespace, static-member, and qualified enum-case paths;
use `.` for fields and instance methods. The separator is checked during name
resolution, so an instance cannot be used as a namespace or type receiver.

```taro
import std::collections::{List}

func main() {
    var values = List[int32]::new()
    values.append(7)
    println(f"{values.len()}")
}
```

Types use the same qualification: `std::collections::List[int32]`. Inferred
enum cases retain the leading-dot shorthand, such as `.some(value)`.

### Await expressions

A prefix `await` authorizes suspension throughout its expression. Each resolved
async call completes before the surrounding synchronous operation uses its result:

```taro
response := await client.get(url).unwrap()
value := await fetch()!
total := await first() + second()
```

Calls follow ordinary evaluation order and short-circuit rules. This does not
spawn tasks or run calls in parallel. The scope stops at closure boundaries;
a callback body needs its own `await`. Nested markers are permitted. A marker
with no async operations warns. Await requires an async context and is forbidden
inside `defer`. Stored tasks remain explicit: `await task.result()`.

### Contextual Result success conversion

Where `Result[T, E]` is expected, a value of `T` can supply `.ok(value)`
implicitly. This applies to returns, tails, branches, annotated variables,
assignments and arguments. Ordinary payload coercions run before wrapping.

```taro
func app() -> Result[Response, Error] {
    return .text(200, "ok")
}
```

A leading member first resolves on Result itself; if absent, it may resolve on
the known success type (`Response` here). There is no global member search.
Matching Results pass through unchanged, including errors. A bare value always
means success, even when T and E are the same type. Failures require `.err(error)`.
Known Result values are never implicitly nested or unwrapped; nested Results use
explicit `.ok(innerResult)`. Postfix `!` remains explicit propagation.
For a unit success, use `()` or a void-valued expression. Empty-return and
fallible-initializer construction rules remain unchanged.
