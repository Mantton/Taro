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
17. Postfix: `.`, `()`, `[]` (specialization), `!`, `?.`
18. Primary

`await` consumes the following expression. Parenthesize the awaited operation
when applying another operator to its result: `(await operation()) + 1` and
`(await operation())!`.

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
let out = value
.some(out)          // parsed as: value.some(out)

let out = value;
.some(out)          // standalone inferred member expression
```

### Wildcard

`_` discards a value in a binding pattern (`let _ = expression`). As an
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
let list: [int32] = [1, 2, 3]
let empty: [int32] = []
let array: [int32; 3] = [1, 2, 3]

// Repeat expressions construct fixed-size arrays, with a constant count.
let zeros: [int32; 10] = [0; 10]
```

Element literals default to fixed-size arrays when no collection type is
determined by context. An expected `List[T]` type selects list construction,
including when a generic call's other arguments or result determine that type:

```taro
var values: [int32] = [1, 2, 3]
let previous = std.mem.replace(&mut values, [])
// values is now an empty list; previous owns the original list.
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

## Struct Literals

```taro
Point { x: 1, y: 2 }

// Shorthand (field name matches variable name)
let x = 1
let y = 2
Point { x, y }      // Same as Point { x: x, y: y }

// Mixed
Point { x, y: 10 }

// Trailing comma
Point { x: 1, y: 2, }
```

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
let result = {
    let a = compute()
    let b = process(a)
    a + b   // This is the block's value
}
```

---

## Prefix (Unary) Expressions

```taro
!flag               // Logical NOT
-value              // Negate
~bits               // Bitwise NOT

&value              // Take immutable reference
&const value        // Explicit immutable reference
&mut value          // Take mutable reference

*pointer            // Dereference
```

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
counter.value = 10   // setter write (if a setter exists)
```

If the property getter is async, reads must be directly awaited:

```taro
let s = await store.current
```

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

Taro has no subscript operator. Collections expose element access as methods so
that the failure mode is visible at the call site:

```taro
list.get(0)             // Optional[&Element] — .none when out of bounds
list.at(0)              // &Element — panics when out of bounds
dictionary.get(&key)    // Optional[&Value] — keys are passed by reference
```

Mutable receiver overloads can instead return `&mut Element` or
`Optional[&mut Element]`. To copy a `Copy` element out of a reference,
dereference it:

```taro
let first = *list.at(0)
```

`[` `]` after an expression is always type specialization, never indexing. Writing
`list[0]` parses as a specialization of `list` and is rejected.

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
- To propagate an awaited value, write `(await expr)!`. `await expr!` is rejected on purpose because `await` consumes the following expression.

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

For computed properties:

- `obj.prop = value` is valid only when a setter is declared.
- `obj.prop += value` and other compound assignments read through the getter,
  apply the corresponding assignment operator, then write through the setter.
- The receiver, getter, and right-hand side are each evaluated exactly once.
- Async getters cannot be used in compound assignment.

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
let result = if condition { value1 } else { value2 }

// Chained
let status = if x > 0 {
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
|x| x * 2

// Empty parameters
|| 42

// Multiple parameters
|a, b| a + b

// With type annotations
|x: int32, y: int32| -> int32 x + y

// Block body
|x| {
    let y = x * 2
    y + 1
}

// Move closure: capture referenced outer variables by value
move |x| x + offset

// Owned captures can still be reusable when the body only reads them
let len = move || items.len()

// Explicit async closure
|| async {
    await std.testing.yieldNow()
    42 as int32
}

// Contextual async inference for inline call arguments
std.task.spawn(|| {
    await std.testing.yieldNow()
    42 as int32
})

// Trailing comma allowed
|a, b,| a + b
```

`move` captures referenced outer variables by value. For synchronous closures,
this does not by itself make the closure one-shot: it is `FnOnce` when the body
moves a captured value out of the closure. An owned capture that is only read
can remain reusable.

Async closures with only immutable `Copy` or borrowed captures are reusable and
satisfy `AsyncFn`. Mutable borrowed captures make a closure `AsyncFnMut`, so it
can be called repeatedly in sequence through a mutable closure value. Moving a
non-`Copy` capture makes the closure `AsyncFnOnce`. Async closure calls must be
immediately awaited; overlapping futures are rejected so they cannot share a
mutable capture.

---

## Opaque Return Types

`some Interface` hides a function's concrete return type while preserving its
interface conformances:

```taro
func makeNamed() -> some Named {
    HiddenName { value: "Taro" }
}

func makeCopyNamed() -> some Named & Copy {
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

### Let Binding (Optional Shorthand)

```taro
if let value = optional {
    use(value)
}

// Shorthand (same name)
if let value {
    use(value)
}

guard let value = optional else { return }
```
