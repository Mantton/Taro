# Types

This chapter describes Taro's type syntax. Blocks containing bare types are
syntax fragments, not complete programs. Names such as `User`, `Point`, and
`Error` stand for types declared or imported by the surrounding program.

## Nominal Types

Paths name structs, enums, and type aliases. Interface names also appear in
bounds and existential types.

```taro
// Simple type
int32
string
bool

// Qualified path
std.fs.File
package.module.Type

// Generic type
List[int32]
Dictionary[string, User]
Result[int32, Error]

// Nested generic
Dictionary[string, List[int32]]
```

---

## Pointer Types

Pointers provide direct memory access. They are immutable by default; `mut`
permits mutation through the pointer. `const` explicitly spells the default.

```taro
*int32           // Immutable pointer to int32
*mut int32       // Mutable pointer to int32
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

References provide borrowed access to values. They are immutable by default;
`mut` permits mutation through the reference. `const` explicitly spells the default.

```taro
&int32           // Immutable reference
&mut int32       // Mutable reference
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

Function types describe function pointer signatures.

```taro
() -> ()                      // No parameters, unit return
(int32) -> int32              // Single parameter
(int32, string) -> bool       // Multiple parameters
(int32, int32) -> (int32, int32)  // Returns tuple

// Higher-order functions
((int32) -> int32) -> int32   // Takes function, returns int
```

## Callable Interface Shorthand

Callable interface names support shorthand in generic bounds and type syntax.

```taro
Fn() -> string
Fn(int32) -> int32
FnMut(int32, string) -> bool
FnOnce(int32) -> Result[string, Error]
AsyncFn(int32) -> string
```

For example:

```taro
func map[F: Fn(int32) -> int32](_ f: F, _ x: int32) -> int32 {
    f(x)
}

func main() {
    let double = |x: int32| x * 2
    assert(map(double, 3) == 6, "generic callable result")
}
```

This is shorthand for the existing callable interfaces:

```taro
Fn() -> string                  // Fn[(), string]
Fn(int32) -> int32              // Fn[int32, int32]
FnMut(int32, string) -> bool    // FnMut[(int32, string), bool]
```

Taro keeps `(A, B) -> R` for function pointers. It does not use lowercase `fn(A) -> R`.

Current limitation: converting closures such as `|x: int32| x * 2` and
`|a: int32, b: int32| a + b` to `any Fn(int32) -> int32` and
`any Fn(int32, int32) -> int32` is rejected. The unary form also conflicts with
the interface's `Tuple` requirement; wrapping its input type in a singleton
tuple does not fix the conversion. Generic bounds, as above, support these closures.

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
[uint8; 256]         // Array of 256 bytes
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
(*int32)?            // Optional pointer (parentheses are required here)
```

---

## Existential Types

Existential types (boxed trait objects) enable dynamic dispatch.

```taro
any Drawable                    // Any type conforming to Drawable
any std.io.Reader & std.io.Writer // Multiple interface bounds
```

Here `Drawable` is a user-defined interface. Each value has a concrete
underlying type that implements the listed interfaces.

## Opaque Return Types

`some Interface` in a return position hides one concrete implementing type.
Unlike `any Interface`, the concrete type is fixed by the function's definition.

```taro
interface Counted {
    func count(&self) -> int32;
}

struct One {}
impl Counted for One {
    func count(&self) -> int32 { 1 }
}

func one() -> some Counted { One {} }
```

---

## Special Types

### Never Type

The `!` type indicates a function never returns (e.g., panics, infinite loops).

```taro
func stop(_ message: string) -> ! {
    panic(message)
}
```

The prelude's `panic` function returns this type.

### Infer Type

The `_` type lets the compiler infer the type.

```taro
func main() {
    let x: _ = 42           // Inferred as int32
    let list: [_] = [1, 2]  // Inferred as [int32]
}
```

### Parenthesized Type

Parentheses can be used for grouping or creating single-element tuples.

```taro
(int32)                 // Parenthesized type (still int32)
(*int32)?               // Optional pointer; *int32? points to an optional
```

---

## Type with Generics

Types can be parameterized with type arguments.

```taro
// Single type argument
List[int32]
Optional[string]

// Multiple type arguments
Dictionary[string, int32]
Result[User, Error]

// Nested generics
Dictionary[string, List[int32]]

// Const generics
Array[int32, 10]         // Type and const value

// Trailing comma allowed
Dictionary[string, int32,]
```

---

## Self Type

Within interfaces and implementations, `Self` refers to the implementing type.

```taro
interface Cloneable {
    func clone(&self) -> Self;
}
```
