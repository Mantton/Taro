# Statements

This chapter covers all statement types in Taro.

## Blocks

Blocks group statements and define scopes.

```taro
{
    x := 1
    y := 2
    printf("%d", x + y)
}
```

---

## Variable Statements

### Inferred and Typed Bindings

Local bindings are writable. `name := value` and `(a, b) := value` infer new
mutable bindings (evaluating the right-hand side before shadowing outer names);
`var` also supports explicit types and general irrefutable destructuring. `let`
is not supported.

```taro
x := 42                 // Type inferred
(a, b) := (1, 2)        // Tuple shorthand destructuring
((p, q), _) := nested() // Nested tuples and wildcards
var y: int32 = 42       // Explicit type
var (c, d) = (3, 4)     // Pattern destructuring
_ := calculate()        // Evaluate and discard; introduces no name
```

### Reassignment

```taro
var count = 0           // Mutable variable
count += 1              // Can be reassigned

var name: string = "initial"
name = "updated"
```

Tuples can assign to existing destinations, including nested tuples, fields,
indices, and dereferenced writable references. `_` discards a component:

```taro
(a, b) = (b, a)
(a, (b, _)) = getNestedTuple()
(point.x, values[index]) = getPair()
```

The complete right-hand tuple is evaluated once and saved before any writes.
Destinations are then evaluated once and assigned in depth-first, left-to-right
order, using ordinary assignment coercions and mutability/accessor checks.
Repeated destinations are allowed: `(a, a) = (1, 2)` leaves `a` equal to `2`.
Earlier writes affect later destinations: `(i, values[i]) = (1, 9)` writes
`values[1]`. A later failure does not roll back earlier writes. Reference-valued
components retain ordinary sharing semantics; saving the tuple is not a deep copy.

Tuple shape and arity must match exactly. Singleton tuples require a trailing
comma (`(a,) = (1,)`); `() = ()` is an empty assignment. Assignment returns `()`
and declares no names. Array/struct assignee patterns, rest patterns, and tuple
compound assignments are not supported. `_ := expression` is a local discard
declaration; it supplies no expected type and does not suppress diagnostics.

---

## Expression Statements

Any expression followed by a semicolon (explicit or via ASI).

```taro
print("Hello")          // Function call
x += 1                  // Assignment
calculate() |> process() // Pipe chain
```

---

## Formatted Output (`printf`)

`printf` and `sprintf` are available from the prelude.

Supported format specifiers:
- `%%` literal percent sign
- `%d` integer arguments only
- `%s` string arguments only
- `%v` any type conforming to `std::fmt::Formattable`

For `float` and `double`, `%v` and string interpolation use the shortest
decimal that round-trips at the value's own precision. Whole numbers can
render as `42`, and negative zero renders as `-0`. The non-finite values
render as `nan`, `inf`, and `-inf`. Normalized decimal exponents from −4
through 15 use fixed notation. Outside that range, scientific notation uses a
lowercase `e` without a positive sign or leading exponent zeros (for example,
`1e16`).

Formatting interfaces:
- `std::fmt::Display` writes a user-facing representation into `std::fmt::Formatter`.
- `std::fmt::Formattable` extends `Display` with verb-aware formatting using `FormatState`.
- `std::fmt::Debug` writes a programmer-facing representation: strings and runes
  quoted and escaped, structs and enums with their fields, collections in literal
  syntax. It is in the prelude and can be derived. `std::fmt::debugString(value)`
  returns the text.

`printf`, `sprintf` and `%v` require `Display`. String interpolation alone falls
back to `Debug` for a value without `Display`; `Display` wins when a type has both.

Validation behavior:
- Literal format strings are validated at compile time (specifier grammar, argument count, and `%d`/`%s` argument types).
- Non-literal (dynamic) format strings are validated at runtime and panic with a `printf:` message on invalid input.

```taro
func main() {
    printf("x=%d y=%s z=%v\n", 7, "ok", true)
    line := sprintf("x=%d", 7)
    println(line)
    printf("100%%\n")
}
```

F-strings provide a shorthand for `%v`-style formatting:

```taro
func main() {
    name := "Ada"
    score := 7
    line := "Hello, ${name} (score=${score})"
    println(line)
}
```

Notes:
- Interpolations use `${expr}` and support full expressions.
- An interpolated value without `Display` prints its `Debug` text.
- Literal braces use `{{` and `}}`.
- `%` in literal segments is preserved (compiler escapes it when lowering to `std::sprintf`).

---

## Assertions

`assert(condition)` and `assert(condition, message)` verify a boolean condition
and panic on failure. The message argument is optional and `@lazy`: it is only
evaluated if the condition fails. Direct calls to `std::assert` and
`std::debugAssert` capture evaluated operand values once, preserve
short-circuiting, and report the caller location, source expression, and
`Debug` values (`<non-Debug>` for operands without `Debug`, `<not evaluated>`
for subexpressions skipped by short-circuiting).

`debugAssert` is active in debug builds and becomes a no-op outside debug builds
(neither the condition nor the message runs in release builds).

```taro
assert(queue.len() == expected)
assert(ready, "not ready yet")

func debugOnlyPath() {
    debugAssert(#cfg(profile("debug")), "expected debug profile")
}
```

---

## Return Statement

Returns a value from a function.

```taro
// With value
func add(a: int32, b: int32) -> int32 {
    return a + b
}

// Without value (unit return)
func process() {
    if done { return }
    // more work...
}

// Implicit return (last expression in block)
func double(x: int32) -> int32 {
    x * 2   // No return keyword needed
}
```

---

## Loop Expression

Infinite loop with explicit exit. An unconditional `loop` is an expression whose
type is inferred from its reachable value `break`s (or `()` when exited only
with valueless `break`, or `!` when it never breaks).

```taro
loop {
    doWork()
    if finished { break }
}

// Returning a value from an unconditional loop
connection := loop {
    if var socket = tryConnect(address) { break socket }
}

// Labeled loop
outer: loop {
    inner: loop {
        if condition { break outer }
    }
}
```

A bare identifier after `break` targets an in-scope loop label if one is
visible (for example `break outer` breaks the `outer` loop even if a local
variable named `outer` is also in scope; parenthesize `break (outer)` to break
the innermost loop with the local's value). Mixing a reachable valueless `break`
with a value-bearing `break` in the same `loop` is an error, and `break <value>`
is only allowed in unconditional `loop`s, not `while` or `for`.

---

## While Statement

Conditional loop.

```taro
while condition {
    doWork()
}

// With complex condition
while x > 0 && !done {
    x -= 1
}

// Labeled while
outer: while running {
    while processing {
        if abort { break outer }
    }
}
```

---

## For Statement

Iterate over sequences.

```taro
// Basic iteration
for item in collection {
    process(item)
}

// With pattern destructuring
for (key, value) in dictionary {
    print(key + ": " + value)
}

// With where clause (filter)
for x in numbers where x > 0 {
    process(x)
}

// Labeled for
outer: for row in grid {
    for cell in row {
        if cell.isEmpty { continue outer }
    }
}

// Range iteration
for i in 0..10 {
    printf("%d\n", i)  // 0 to 9
}

for i in 0..=10 {
    printf("%d\n", i)  // 0 to 10 (inclusive)
}

// Reverse range iteration
for i in (0..10).reversed() {
    printf("%d\n", i)  // 9 down to 0
}
```

### Async Iteration

`for await` iterates an async sequence, suspending between elements. It is only
valid inside an async context, and combines with `where` like the sync form.

```taro
for await value in stream {
    process(value)
}

for await value in stream where value % 2 == 0 {
    process(value)
}
```

---

## Break Statement

Exit a loop early.

```taro
loop {
    if done { break }
}

// With label
outer: loop {
    inner: loop {
        break outer  // Exits outer loop
    }
}
```

---

## Continue Statement

Skip to next iteration.

```taro
for x in items {
    if x < 0 { continue }
    process(x)
}

// With label
outer: for row in grid {
    for cell in row {
        if cell.skip { continue outer }
        process(cell)
    }
}
```

---

## Scoped resource bindings

`using name = expression` evaluates the expression once and binds its value in the
current scope. The resource must conform to the prelude interface `Closeable`.
After a successful acquisition, the binding registers a deferred call to its
`Closeable.close` witness. The call reads the binding at scope exit and discards
its result. Use an explicit close when the caller needs to handle a close error.

```taro
func makeFile(_ path: string) -> Result[(), std::io::Error] {
    using file = std::fs::File::create(path)!
    return .ok(())
}
```

Resources and ordinary defers run together in reverse registration order on
normal exit, early return, loop exits and panic unwinding. If acquisition
propagates an error, previously acquired resources still close. A custom
resource supplies its close return type as `CloseResult`. A generic resource can
use a `T: Closeable` bound. An erased resource specifies its result type, for
example `any Closeable[CloseResult = ()]`, so its close witness can be called.
The word `using`
can also name an ordinary variable or function.

## Defer Statement

Execute code when leaving the current scope, in reverse registration order.
`defer expression` is shorthand for `defer { expression }`: its callable,
receiver, arguments and assignment target are evaluated during cleanup, not
when the defer is registered. Both forms observe later changes to captured
variables. Copy a value into a fresh local to retain a particular value or
resource handle, following ordinary value semantics.

```taro
func process() {
    file := openFile()
    defer file.close()
    
    // Use file...
    // file.close() called automatically when function exits
}

// Multiple defers (LIFO order)
func example() {
    defer print("3")
    defer print("2")
    defer print("1")
    // Prints: 1, 2, 3
}
```

Only reached defer statements register cleanup. Registered actions run on normal
and early exits, ordinary panic unwinding and observed task cancellation. Deferred
code remains synchronous; `await`, `return`, `break` and `continue` keep the same
restrictions as in a defer block. Inline expressions use the existing scope and
unwind machinery, including nested blocks.

### Error-only cleanup

`errdefer` registers a cleanup for the current scope. It runs when the
enclosing function returns a `Result.err` while that scope is active, or
when a panic unwinds through it. Ordinary defers and error-only defers share
reverse registration order.

```taro
func openDatabase(_ path: string) -> Result[Database, Error] {
    handle := connect(path)!
    errdefer { var _ = handle.close() }
    migrate(handle)!
    return .ok(Database { handle })
}
```

The returned value controls cleanup, including a forwarded Result, a function
body’s tail expression, a branch that supplies the return value directly, and
an error propagated with `!`. A successful
nested block exit, `break`, or `continue` retires registrations in the scopes
it leaves. An Optional returning `.none` and ordinary task cancellation skip
error-only cleanup. If a later-registered defer panics, the remaining active
error cleanups run during unwinding.

Both `errdefer release(handle)` and the block form evaluate the cleanup on
exit. The contextual spelling preserves calls such as `errdefer(handle)`,
indexing, and assignments to a variable named `errdefer`. Use braces when
a cleanup starts with an ambiguous operator or parenthesis.


---

## Guard Statement

Early exit if a `bool` condition fails. An optional is not a condition by
itself; use `guard var` to unwrap it. The `else` block must exit the current
control-flow path, for example with `return`, `break`, `continue`, or a
never-returning call.

```taro
func process(value: int32?) {
    guard var v = value else { return }
    // 'v' is non-optional int32
    
    printf("%d\n", v)
}

// With else block
func validate(input: string) -> bool {
    guard !input.isEmpty() else {
        print("Input cannot be empty")
        return false
    }
    return true
}
```

---

## Declaration Statements

Functions can be declared inside other functions.

```taro
func outer() {
    func inner() {
        print("Inner function")
    }
    
    inner()
}
```

---

## Labeled Statements

Labels can be attached to loops for targeted break/continue.

```taro
// Label syntax: identifier followed by colon
outer: loop {
    inner: while condition {
        if x { break outer }
        if y { continue inner }
    }
}
```

### Eager transforms and lazy traversal

`Iterable::map` and `Iterable::filter` return a new `List` and run their callbacks
before returning. Filter predicates receive ordinary element values: inline
values are copied and class/reference targets remain shared.

```taro
var items: List[int32] = [1, 2, 3]
results := items.filter((item: int32) => item > 1).map((item: int32) => item * 2)
pipeline := items.lazy().filter((item: int32) => item > 1).map((item: int32) => item * 2)
collected := pipeline.collect()
```

A lazy pipeline retains its source and defers callbacks until traversal. Each
`collect()`, terminal operation, or `for` loop starts a fresh traversal of a
collection source and reruns callbacks; results are not cached. A List pipeline
keeps the selected handle, sees changes made before traversal, and is not
retargeted by assigning a different List to the original variable. Callback
captures read their current bindings. `items.copy().lazy()` explicitly copies
outer storage. Inline arrays are copied; `array.asSpan().lazy()` shares storage.

Standard cursors also implement `Iterable`. For generic `I: Iterator` code,
`std::iter::fromIterator(cursor).lazy()` exposes the same pipeline operations.
An explicit cursor remains single pass: its copies share progress and repeated
traversal continues from that cursor rather than restarting. Structural changes
to a collection invalidate active cursors; replacement of an existing element
is allowed and subsequent reads see the new value. An exhausted cursor stays
exhausted. These checks diagnose mutation and do not synchronize concurrent code.
