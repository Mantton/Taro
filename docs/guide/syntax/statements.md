# Statements

This chapter covers all statement types in Taro.

## Blocks

Blocks group statements and define scopes.

```taro
{
    let x = 1
    let y = 2
    print(x + y)
}
```

---

## Variable Statements

### Let (Immutable)

```taro
let x = 42              // Type inferred
let y: int32 = 42       // Explicit type
let (a, b) = (1, 2)     // Pattern destructuring
```

### Var (Mutable)

```taro
var count = 0           // Mutable variable
count += 1              // Can be reassigned

var name: string = "initial"
name = "updated"
```

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

`printf` and `sprintf` are available from the prelude (`printf`, `sprintf`) and as `std.printf` / `std.sprintf`.

Supported format specifiers in v1:
- `%%` literal percent sign
- `%d` integer arguments only
- `%s` string arguments only
- `%v` any type conforming to `std.fmt.Formattable`

Formatting interfaces:
- `std.fmt.Display` writes a user-facing representation into `std.fmt.Formatter`.
- `std.fmt.Formattable` extends `Display` with verb-aware formatting using `FormatState`.

Validation behavior:
- Literal format strings are validated at compile time (specifier grammar, argument count, and `%d`/`%s` argument types).
- Non-literal (dynamic) format strings are validated at runtime and panic with a `printf:` message on invalid input.

```taro
func main() {
    printf("x=%d y=%s z=%v\n", 7, "ok", true)
    let line = sprintf("x=%d", 7)
    std.printf("100%%\n")
}
```

---

## Assertions

`assert` always panics on failure.

`debugAssert` uses an inline `#cfg(profile("debug"))` guard and becomes a no-op outside debug builds.

```taro
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

// Without value (void return)
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

## Loop Statement

Infinite loop with explicit exit.

```taro
loop {
    doWork()
    if finished { break }
}

// Labeled loop
outer: loop {
    inner: loop {
        if condition { break outer }
    }
}
```

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
    print(i)  // 0 to 9
}

for i in 0..=10 {
    print(i)  // 0 to 10 (inclusive)
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

## Defer Statement

Execute code when leaving the current scope.

```taro
func process() {
    let file = openFile()
    defer { file.close() }
    
    // Use file...
    // file.close() called automatically when function exits
}

// Multiple defers (LIFO order)
func example() {
    defer { print("3") }
    defer { print("2") }
    defer { print("1") }
    // Prints: 1, 2, 3
}
```

---

## Guard Statement

Early exit if condition fails.

```taro
func process(value: int32?) {
    guard value else { return }
    // 'value' is still optional here
    
    guard let v = value else { return }
    // 'v' is non-optional int32
    
    print(v)
}

// With else block
func validate(input: string) -> bool {
    guard input.length > 0 else {
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
