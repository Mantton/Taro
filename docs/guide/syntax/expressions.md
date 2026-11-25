# Expressions

This chapter covers all expression types in Taro, organized by precedence (lowest to highest).

## Expression Precedence

From lowest to highest precedence:

1. Assignment: `=`, `+=`, `-=`, `??=`, etc.
2. Pipe: `|>`
3. Ternary: `? :`
4. Nil-coalescing: `??`
5. Range: `..`, `..=`
6. Logical OR: `||`
7. Logical AND: `&&`
8. Comparison: `<`, `>`, `<=`, `>=`, `==`, `!=`
9. Membership: `in`, `!in`
10. Bitwise OR: `|`
11. Bitwise XOR: `^`
12. Bitwise AND: `&`
13. Bit shift: `<<`, `>>`
14. Term: `+`, `-`
15. Factor: `*`, `/`, `%`
16. Cast / Type Assertion: `as`, `as?`, `is`
17. Prefix: `!`, `-`, `~`, `&`, `*`
18. Postfix: `.`, `()`, `[]` (specialization or indexing), `!`, `?.`
19. Primary

`await` scopes the following expression. Async calls complete before their results
are used: `await operation() + 1` and `await operation()!`.

---

## Primary Expressions

### Literals

```taro
42                  // Integer
3.14                // Float
"hello"             // String
"hello, ${name}"    // Interpolated string
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

`_` discards a value in a binding pattern (`var _ = expression` or
`_ := expression`), as an assignment destination (`_ = expression`), ignores a
tuple assignment component (`(value, _) = pair`), or consumes an ignored
closure parameter (`_ => 42`). It never binds a name. `_ = expression`
evaluates the expression once and drops its value; it is the usual way to
ignore a `Result` on purpose (see [Unused Results](#unused-results)).
As a value expression, it is only supported as one top-level argument
placeholder on the right-hand side of a pipe:

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

A repetition evaluates its element once. A fixed-array annotation or type
alias supplies the element type, including conversions such as wrapping a
value in an Optional. The count must match the length of the destination.

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

Postfix `...` inserts the elements of an `Iterable` into a collection literal.
Each source is evaluated once and exhausted before the next element expression.

```taro
var pair: [int32; 2] = [1, 2]
four := [0, pair..., 3]                // [int32; 4]
var more: List[int32] = [4, 5]
values := [four..., more...]           // List[int32]
var wrapped: List[int32?] = [pair...]  // converts each integer to Optional
```

A literal preserves a fixed array length when its contributions have a known
total length. A runtime-length source such as a List or Span produces a List
and is rejected in a fixed-array context. An explicit List context always
produces a List. The result owns its element slots.

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
- When `TargetE` is an existential such as `any std::error::Error` and `E` is
  not, propagation boxes the error, as returning it would; `E` must conform to
  the existential's interfaces.
- Otherwise, `TargetE` must implement `From[E]`; propagation calls that
  conversion before returning `.err`.
- `Optional` and `Result` do not mix. You cannot propagate an `Optional` from a `Result` context or vice versa.
- To propagate an awaited value, write `await expr!` or `(await expr)!`.

### Unused Results

A `Result` that is computed and then thrown away hides its error. The compiler
warns when the value of an expression whose type is `Result[T, E]` (including
an alias of it) is not used: an expression statement, the value of an `if`,
`match` or block used as a statement, or the last expression of a function,
loop or `defer` body that returns nothing.

```taro
file.write(data)            // warning: unused 'Result[usize, Error]'; handle it,
                            // propagate it with `!`, or discard it with `_ = ...`
file.write(data)!           // propagate the error
_ = file.write(data)        // discard it on purpose
match file.write(data) {    // handle it
    case .ok(_) => {}
    case .err(error) => report(error)
}
```

Binding the value (`var _ = expr`, `_ := expr`, `count := expr`), returning
it, passing it on, or using it as the value of a block does not warn.
`Optional` and other types are never reported.

A function whose result is normally ignored can opt out with
`@discardableResult`. Calls to it, including calls through a generic bound or
an `any` existential to an interface requirement that carries the attribute,
do not warn:

```taro
@discardableResult
func log(_ line: string) -> Result[(), Error] { ... }

log("started")              // no warning
```

The warning is reported only for the package being compiled, never for its
dependencies, and it does not change the exit status of `taro build`, `run`,
`test` or `check`. A package reused unchanged from the incremental cache is
not checked again; the warnings stored with its cached metadata are printed
again instead, so they do not disappear on the second build. The same holds
for the unused import and unused variable warnings below.

### Unused Imports

An imported name that nothing in its file uses warns once, at the name:

```taro
import std::fs                              // warning: unused import 'fs'
import std::fmt::{Display, Formatter}       // warning: unused import 'Formatter'
```

An import is used when code refers to it as a type, a value, a path prefix
(`fs::read(...)`), an interface in a conformance list or a bound, or inside a
string interpolation. Importing an interface also makes its methods callable
on conforming types, so an interface import is used when a method call finds
one of its methods, even if the interface is never named. A declaration that
`@cfg` removes for the current target still counts: an import it names does
not warn.

Glob imports (`import std::fmt::*`), `export` re-exports, imports inside a
`namespace` (other code can reach them as `Namespace::Name`) and the prelude
are never reported. Like the unused `Result` warning, it applies only to the
package being compiled and does not change the exit status.

### Unused Variables

A local that is declared and never read warns once, at its name:

```taro
func area(_ shape: Shape) -> int32 {
    scale := 2      // warning: unused variable 'scale'; prefix it with '_'
                    // if this is intended
    match shape {
        case .rect(width, height) => width   // warning: unused variable 'height'
        case .circle(radius) => radius * radius
    }
}
```

The check covers `:=` and `var` declarations, tuple and other destructuring
patterns, and the bindings of `match` arms, `if var`, `guard var`, `while var`
and `for` loops. A binding repeated across the alternatives of an or-pattern
is one variable and warns once. A local counts as read when any expression
reads it, including a closure body, a string interpolation, a `defer` block
or a compound assignment such as `count += 1`. Assigning it with `=` is not a
read, so a variable that is only ever assigned still warns.

Names that start with `_` are exempt, as are the parameters of functions,
methods, initializers and closures, `self`, and the bindings the compiler
creates for `for` loops, optional chaining and other desugaring. Use `_name`
to keep a binding on purpose, or `_ = expression` when only the effect of
the expression matters.

### Optional Chaining

```taro
user?.profile?.name
object?.method()
grid?.[row]?.[col]
callback?.("ready", 200)
```

Optional chaining short-circuits when the receiver is `.none`: subsequent
member accesses, index expressions, and call arguments are skipped and the whole
chain produces `.none`. Optional chains are read-only expressions and cannot be
used as assignment targets or reference places (`&`).

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

With overflow checks on (the debug default), integer `+`, `-` and `*` panic on
overflow; with checks off they wrap. To choose per operation, every integer
type has `checkedAdd`, `checkedSub` and `checkedMul` (returning `.none` on
overflow), `wrappingAdd`, `wrappingSub` and `wrappingMul` (two's complement,
never panic), and `saturatingAdd`, `saturatingSub` and `saturatingMul` (clamp
to the type's minimum or maximum). They behave the same in every build profile.

```taro
hash = (hash ^ (byte as uint64)).wrappingMul(0x100000001b3)
seed = seed.wrappingMul(1664525).wrappingAdd(1013904223)
count = count.saturatingAdd(1)
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

### Membership

```taro
x in 0..width       // (0..width).contains(&x)
word !in seen       // !seen.contains(&word)
'a' in "banana"     // a rune
"nan" in "banana"   // a substring
key in dictionary   // dictionary keys
code in [200, 204]  // array elements
```

`a in b` calls `contains` from `Contains[Element]` on `b`, passing `a` by
reference, so testing a large value does not copy it and you never write `&`.
`!in` negates the result. Ranges, `List`, `[T; N]`, `Span`, `Set`, `Deque`,
`Dictionary` and `Counter` (by key) and `string` (by `rune` or by substring)
conform; `Optional` does not. The element is evaluated before the container.

The container side binds a range tighter than `in`, and `in` binds tighter
than `==`, `!=`, `&&` and `||`:

```taro
x + 1 in 0..n               // (x + 1) in (0..n)
row in 0..rows && column in 0..columns
!(item in allowed)          // same as item !in allowed
```

Membership does not chain: `a in b in c` is an error, so write `(a in b) in c`.
`!in` needs `!` to touch the word `in`: `value !in set` and `value!in set` are
negated membership, while `value! in set` propagates `value` first and then
tests it.

A type takes part by conforming, once per element type it can contain:

```taro
struct Grid { width: int32; height: int32 }
struct Cell { column: int32; row: int32 }

conform Grid to Contains[Cell] {
    func contains(_ cell: &Cell) -> bool {
        cell.column in 0..self.width && cell.row in 0..self.height
    }
}

func countInside[C: Contains[Cell]](_ area: C, _ cells: List[Cell]) -> int32 {
    var count: int32 = 0
    for cell in cells where cell in area { count += 1 }
    count
}
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
_ = value           // Evaluate value and discard it

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

### Assigning a Default

`target ??= value` stores `value` only when `target` is nil:

```taro
var cache: [string: string?] = [:]
cache["home"] = nil
cache["home"] ??= "/Users/ada"   // assigns
cache["home"] ??= "/tmp"         // keeps "/Users/ada"

var retries: int32? = nil
retries ??= 3
```

The target must be an assignable `T?`, and the value may be a `T` or a `T?`.
The target's own parts, such as a receiver or an index, run once and first;
the value runs only when the target is nil, so it may be an expensive call,
an `await` or a `!` propagation. Like the other compound assignments,
`??=` produces `()`. A subscript target needs an address accessor or a set
accessor. A dictionary's subscript returns its value type, so
`counts[word] ??= 0` on `[string: int32]` is an error, and on
`[string: int32?]` it still panics for a missing key. For a key that may be
missing, test `word !in counts` first.

Built-in numeric compound assignment writes back to its destination and requires
writable storage or a native subscript setter. A custom value receiver can operate on a
getter result without a setter. As with named methods, `readonly` blocks direct
assignment to a stored field; it does not make references or referenced objects
immutable. A reference receiver still requires addressable storage.

---

## Range Expressions

```taro
1..10               // Range[T]: half-open [1, 10)
1..=10              // ClosedRange[T]: inclusive [1, 10]
start..             // RangeFrom[T]: lower-bounded [start, +∞)
..end               // RangeTo[T]: upper-bounded (-∞, end)
..=end              // RangeToInclusive[T]: inclusive upper-bounded (-∞, end]
..                  // RangeFull: unbounded
(1..=10).reversed() // 10, 9, ..., 1
```

Ranges operate over a bound type that conforms to `Step`. `Range`, `ClosedRange`,
and `RangeFrom` are `Iterable`; `RangeTo`, `RangeToInclusive`, and `RangeFull`
are not iterable and are rejected by `for ... in`. An empty or descending bounded
range (`5..5`, `5..3`, `5..=4`) yields nothing. `reversed()` yields the same
elements from the high end down; it never steps past either bound, so
`(0..n).reversed()` is safe for `usize` and a range may end at a type's maximum.
`RangeFrom` advances lazily on the next `next()` call so yielding `Bound::MAX`
(for example, `(254_u8..).take(2)`) does not step past the maximum; requesting an
element beyond `Bound::MAX` invokes `stepForward()` and follows integer overflow
rules (panicking in debug builds). A custom `Step` type implements `stepForward()`
and `stepBackward()`.

All six range types support membership tests via `Contains`:
- `value in start..end` tests `start <= value < end`
- `value in start..=end` tests `start <= value <= end`
- `value in start..` tests `start <= value`
- `value in ..end` tests `value < end`
- `value in ..=end` tests `value <= end`
- `value in ..` is always `true`

Range operators are non-associative (`a..b..c` is a syntax error) and `..=`
always requires an upper bound (`a..=` is rejected). An upper bound after `..`
is only parsed when it begins on the **same line**, and outside `()` and `[]`,
`..` / `..=` at the start of a new line do not continue the previous line:

```taro
r := start..        // ASI inserts `;` after `..`
nextCall()          // separate statement, not `start..nextCall()`
```

`Span`, `List`, `[T; N]`, and `string` support slicing with all six range forms
(`items[1..]`, `items[..3]`, `items[..=2]`, `items[..]`). `string` range
subscripts slice by **UTF-8 byte offset** (matching `string.sliceBytes`), panicking
when out of bounds or inverted; use `sliceRunes` when slicing by decoded rune
count.

---

## Nil Coalescing

Provide a default value for optionals.

```taro
optional ?? default
user?.name ?? "Unknown"
getValue() ?? computeDefault()
```

To store the default back into an optional, use `target ??= default`.

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
x => x * 2
(x) => x * 2 // Equivalent parenthesized form

// Ignored parameters still consume arguments, but bind no name
_ => 42
(_, value) => value
(_: int32) => 42

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

Parentheses may be omitted only for one unannotated parameter, including `_`.
Explicit parameter/result types, explicit async headers, and multiple parameters
require parentheses. Type inference, contextual async inference, captures, and
expression/block bodies behave identically in both forms. Nested arrows associate
to the right: `x => y => x + y` returns a closure capturing `x`.

Named inline fields may be captured separately; overlapping paths merge. Class
field access captures the class variable so later handle rebinding is observed.
`Fn` and `AsyncFn` both support repeated stateful calls. Async calls require an
enclosing `await` expression; independent tasks can invoke the same callable,
using explicit synchronization when their shared writes need ordering.

### Trailing closures and implicit `it`

When a call's final argument is a closure, it may be written as a brace-delimited
trailing closure on the same line as the call, omitting that parameter's label.
When it is the sole argument, empty parentheses may be omitted as well.

```taro
evens := numbers.filter { it % 2 == 0 }
sum := combine(base: 5) { a, b => a + b }
result := await runAsync { await compute() }
```

- An explicit header (`a, b =>`) declares parameters inside the braces.
- A headerless body that references a free `it` synthesizes a single `it` parameter;
  otherwise it takes zero parameters.
- Shadowing an outer `it` with a nested implicit `it` emits a compiler warning;
  name parameters explicitly when nesting.
- A brace on a new line does not attach as a trailing closure.
- `Name { ... }` retains struct literal recognition for explicit fields, update bases,
  and uppercase empty or single-identifier constructors.
- Bare trailing closures are excluded from `if`, `guard`, `while`, `for`, and `match`
  heads; wrap the call in parentheses when needed inside a condition.
- Async is inferred from the receiving parameter (`AsyncFn` or `async` function type)
  or from `await` inside the body.

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
    println("${values.len()}")
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

## Source locations and debug output

`#file` gives the source path relative to the package root, including `src/`.
In a standalone script it gives the filename. `#line` gives the one-based
line number as an `int32`. `#function` gives the nearest named function,
method or initializer. A closure inherits that name. At module scope the
value is `"<module>"`.

A location in an omitted parameter's default expression describes the call.
For example, calling `report()` on line 20 prints 20, including when
`report` comes from another package.

```taro
func report(line: int32 = #line) {
    println("${line}")
}
```

`dbg(expression)` evaluates its operand once, writes
`[file:line] expression = value` and a newline to standard error, and
returns the value with its original type. The type must implement `Debug`.
The prelude exports `dbg`, so a local declaration can shadow it.
Passing `dbg` as a function value prints the debug representation alone
when invoked indirectly.

```taro
total := dbg(subtotal + tax) * quantity
```

## Embedded assets

Both directives take a literal path relative to the source file containing the
directive. A library can embed its own assets and export their values to other
packages. Changing an asset rebuilds the library and its consumers.

```taro
const PAGE: string = #embed("../assets/index.html")
const MAGIC: [uint8; 4] = #embedBytes("../assets/magic.bin")
```

`#embed` preserves UTF-8 text, including original line endings and embedded
NULs. `#embedBytes` accepts arbitrary bytes. The file size determines the
fixed array length, so a local binding such as `icon := #embedBytes("icon.bin")`
infers it. Both forms support empty files. The compiled program can use the
values after the files are removed.
