# Types

This chapter covers all type syntax in Taro.

## Nominal Types

Named types refer to structs, enums, interfaces, and type aliases.

```taro
// Simple type
int32
string
bool

// Qualified path
std.io.File
package.module.Type

// Generic type
List[int32]
Map[string, User]
Result[int32, Error]

// Nested generic
Map[string, List[int32]]
```

---

## Pointer Types

Pointers provide direct memory access. Mutable by default.

```taro
*int32           // Mutable pointer to int32
*const int32     // Immutable (const) pointer to int32

// Nested pointers
**int32          // Pointer to pointer
***int32         // Triple pointer

// Pointer to other types
*[int32]         // Pointer to list
*(int32, string) // Pointer to tuple
```

---

## Reference Types

References provide borrowed access to values. Mutable by default.

```taro
&int32           // Mutable reference
&const int32     // Immutable (const) reference

// Nested references
&&int32          // Reference to reference

// Mixed pointer/reference
*&int32          // Pointer to reference
&*int32          // Reference to pointer
```

---

## Tuple Types

Tuples group multiple values of different types.

```taro
()                      // Empty tuple (unit type)
(int32,)                // Single-element tuple (trailing comma required)
(int32, string)         // Two-element tuple
(int32, string, bool)   // Three-element tuple

// Nested tuples
((int32, int32), string)

// Trailing comma allowed
(int32, string,)
```

---

## Function Types

Function types describe callable signatures.

```taro
() -> void                    // No parameters, no return
(int32) -> int32              // Single parameter
(int32, string) -> bool       // Multiple parameters
(int32, int32) -> (int32, int32)  // Returns tuple

// Higher-order functions
((int32) -> int32) -> int32   // Takes function, returns int
```

---

## Collection Types

### List Type

Dynamic, growable arrays.

```taro
[int32]              // List of int32
[string]             // List of strings
[[int32]]            // List of lists (nested)
[User]               // List of User structs
```

### Dictionary Type

Hash maps with key-value pairs.

```taro
[string: int32]      // String keys, int32 values
[int32: User]        // Int32 keys, User values
[string: [int32]]    // String keys, list values
```

### Array Type

Fixed-size arrays with compile-time known length.

```taro
[int32; 10]          // Array of 10 int32s
[byte; 256]          // Array of 256 bytes
[Point; 4]           // Array of 4 Points
```

---

## Optional Types

Optional types represent values that may be absent.

```taro
int32?               // Optional int32
string?              // Optional string
User?                // Optional User

// Nested optionals
int32??              // Optional of optional

// Optional with other types
[int32]?             // Optional list
(int32, string)?     // Optional tuple
(*int32)?            // Optional pointer (use parens for clarity)
```

---

## Existential Types

Existential types (boxed trait objects) enable dynamic dispatch.

```taro
any Drawable                    // Any type conforming to Drawable
any Hashable & Equatable        // Multiple interface bounds
```

---

## Special Types

### Never Type

The `!` type indicates a function never returns (e.g., panics, infinite loops).

```taro
func panic(msg: string) -> ! {
    // Never returns
}
```

### Infer Type

The `_` type lets the compiler infer the type.

```taro
let x: _ = 42           // Inferred as int32
let list: [_] = [1, 2]  // Inferred as [int32]
```

### Parenthesized Type

Parentheses can be used for grouping or creating single-element tuples.

```taro
(int32)                 // Parenthesized type (still int32)
(*int32)?               // Clarifies precedence
```

---

## Type with Generics

Types can be parameterized with type arguments.

```taro
// Single type argument
List[int32]
Optional[string]

// Multiple type arguments
Map[string, int32]
Result[User, Error]

// Nested generics
Map[string, List[int32]]

// Const generics
Array[int32, 10]         // Type and const value

// Trailing comma allowed
Map[string, int32,]
```

---

## Self Type

Within interfaces and implementations, `Self` refers to the implementing type.

```taro
interface Cloneable {
    func clone(&self) -> Self;
}
```
