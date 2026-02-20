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
8. Comparison: `<`, `>`, `<=`, `>=`, `==`, `!=`, `===`
9. Bitwise OR: `|`
10. Bitwise XOR: `^`
11. Bitwise AND: `&`
12. Bit shift: `<<`, `>>`
13. Term: `+`, `-`
14. Factor: `*`, `/`, `%`
15. Cast: `as`
16. Prefix: `!`, `-`, `~`, `&`, `*`
17. Postfix: `.`, `()`, `[]`, `?`, `?.`
18. Primary

---

## Primary Expressions

### Literals

```taro
42                  // Integer
3.14                // Float
"hello"             // String
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

The wildcard expression represents an ignored value.

```taro
_                   // Wildcard
```

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

## Array Expressions

```taro
[]                  // Empty array
[1, 2, 3]           // Array with elements
[1, 2, 3,]          // Trailing comma allowed

// Repeat expression
[0; 10]             // [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
[default; count]    // Repeat 'default' 'count' times
```

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

> **Note**: Struct literals are not allowed in certain positions where they would be ambiguous with blocks (e.g., `if`, `while`, `guard` conditions). Use parentheses if needed.

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

&value              // Take reference (mutable)
&const value        // Take const reference

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

### Tuple Access

```taro
tuple.0             // First element
tuple.1             // Second element
point.0             // Access by index
```

### Function Calls

```taro
foo()                       // No arguments
foo(1, 2, 3)               // Positional arguments
foo(a: 1, b: 2)            // Labeled arguments
foo(1, named: 2)           // Mixed
foo(arg1, arg2,)           // Trailing comma allowed
```

### Subscript (Index)

```taro
array[0]
dictionary["key"]
matrix[row][col]
```

### Type Specialization

```taro
List[int32]
identity[string]
Result[User, Error]
```

### Optional Unwrap

```taro
optionalValue?      // Unwrap, propagates nil on failure
```

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
a === b             // Pointer equality
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

## Cast Expression

```taro
value as int64
number as float64
ptr as *void
```

---

## If Expression

If-else as an expression (returns a value).

```taro
let result = if condition { value1 } else { value2 }

// Chained
let status = if x > 0 { "positive" }
             else if x < 0 { "negative" }
             else { "zero" }

// If without else (returns optional or void)
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

// Trailing comma allowed
|a, b,| a + b
```

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
