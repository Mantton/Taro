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
std::fs::File
package::module::Type

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

Raw pointers carry addresses, without checked validity or borrowing permission.
Dereferencing one—including implicit dereference for field or method access—
requires `unsafe { ... }`. The pointer memory methods `read`, `write`, copying,
and byte filling are unsafe too. Address arithmetic does not itself dereference.
Under GC storage, live pointers in traced memory retain managed allocations,
including interior pointers; native memory lifetimes remain the caller's
responsibility. A raw pointer into a native stack slot does not trace GC fields
inside that slot; use `std::runtime::keepAlive(owner)` after the final raw access
when its owner must remain a GC root. Prefer references and checked slices in
safe APIs.

`nil` constructs a null raw pointer or an empty Optional when its target type
is known from context. It has no standalone runtime type. Blocks, branches and
generic calls retain their normal evaluation effects around the literal.

```taro
func main() {
    var value: int32 = 7
    unsafe {
        var pointer: *mut int32 = &value as *mut int32
        pointer.write(9_i32)
    }
    assert(value == 9, "checked access resumes after the raw operation")
}
```

---

## Reference Types

`&T` is a writable GC reference. Copies address the same value, and a reference
keeps its storage alive even when returned or stored in another value. Overlapping
references are allowed. Programs synchronize concurrent writes themselves.
There are no reference lifetime parameters or mutable/immutable reference modes;
`&mut T` and `&const T` are rejected. Raw pointers retain `*mut` and `*const`.

```taro
&int32           // Reference to int32
&&int32          // Reference to reference
*&int32          // Raw pointer to reference
&*int32          // Reference to raw pointer

func takeList(_ values: &[int32]) -> [int32] {
    previous := *values
    *values = []
    previous
}
```

Reading through a reference copies an ordinary value. A copied struct/array is
independent; class and collection handles still share their targets. A reference
to an array or collection element keeps that backing allocation alive. List
resizing may replace the active buffer; outstanding references retain the old one.
Reference slots are invariant: `&Derived` cannot become `&Base`, because writing
a Base into it would violate the original slot's type. Inherited method receivers
use a separate checked adaptation that cannot replace or export the caller's slot.

---

## Weak references (GC storage)

`std::weak::Weak[T]` observes the storage addressed by `&T` without keeping it
alive, as on main. Copies share a GC weak cell; `value()` returns `Optional[&T]`.
A successful snapshot is a normal strong reference and keeps the target alive
while used. A cleared cell stays empty.

```taro
var value: int32 = 7
weak := std::weak::Weak[int32]::new(&value)
snapshot := weak.value().unwrap()
assert(value == 7, "keep the original strong through the snapshot")
assert(*snapshot == 7, "the snapshot is a strong reference")
```

Referenced locals are promoted when needed. Interior references clear with
their containing allocation, and static targets remain available. The API
observes the referenced storage; it does not implicitly dereference a class or
list handle. Unsafe foreign storage keeps its manual lifetime obligations.

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

Callable shorthand works in both generic bounds and existential types:
`Fn(A) -> R` describes a callable taking one `A` and returning `R`.

```taro
Fn() -> string
Fn(int32) -> int32
Fn(int32, string) -> bool
Fn(int32) -> Result[string, Error]
AsyncFn(int32) -> string
```

For example:

```taro
func map[F: Fn(int32) -> int32](_ f: F, _ x: int32) -> int32 {
    f(x)
}

func main() {
    double := (x: int32) => x * 2
    assert(map(double, 3) == 6, "generic callable result")
}
```

Callable interfaces represent their argument list as a tuple:

```taro
Fn() -> string                  // Fn[(), string]
Fn(int32) -> int32              // Fn[(int32,), int32]
Fn(int32, string) -> bool    // Fn[(int32, string), bool]
Fn((int32, string)) -> bool     // Fn[((int32, string),), bool]
```

Taro keeps `(A, B) -> R` for function pointers. It does not use lowercase `fn(A) -> R`.
Safe Taro function pointers implement `Fn`, so named functions can be passed
straight to generic or erased callable parameters. Async named functions
implement `AsyncFn`; an inferred local such as `callback := asyncFunction`
retains that async signature and requires `await` when called. Unsafe functions
and foreign ABI function pointers do not implement these safe callable interfaces.
Use an explicit closure to perform an unsafe or foreign call inside a callback.

The older spelling `Fn[int32, int32]` remains accepted for one scalar argument.
An explicit tuple pack, such as `Fn[(int32, string), bool]`, describes two
arguments. Generic `Args: Tuple` parameters can forward an argument pack through
`call(args: ...)`.

An existential stores a conforming callable and dispatches calls through its
interface:

```taro
func main() {
    var double: any Fn(int32) -> int32 = (x) => x * 2
    assert(double(21) == 42, "existential callable")
    var sum: any Fn((int32, int32)) -> int32 = (pair) => pair.0 + pair.1
    assert(sum((19, 23)) == 42, "one tuple argument")
}
```

`Fn` and `AsyncFn` are repeatable. Mutating captured variables does not change
the callable type. Their explicit invocation method is `call(args: ...)`.
`FnMut`, `FnOnce`, `AsyncFnMut` and `AsyncFnOnce` are removed spellings.

`AsyncFn` invocations require `await`; each invocation creates its own future
that retains the shared environment. Closure parameter and result types can be
inferred from the expected interface. An inline closure in an async context is
inferred as async; an already typed synchronous closure is not converted.
Concurrent calls use the ordinary synchronization rules for shared values.

A callable intersection with incompatible signatures, or with both synchronous
and asynchronous interfaces, requires conversion to one callable interface before
invocation.

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

### Slice Type (GC storage)

`[T; ..]` is shorthand for `std::mem::Span[T]`, a writable view over an
existing range. Its two-word header contains a data pointer and a length.
Copying or slicing the header shares the elements; iteration yields element
copies. There is one slice type, with no read-only/mutable distinction.

```taro
var values: [int32] = [10, 20, 30]
var slice: [int32; ..] = values.asSpan()
slice[1] = 21
tail := slice.slice(1, 2) // start, count; shares values[1] and values[2]
assert(*tail.at(0) == 21, "slices share elements")
```

Indexing and `slice(start, count)` check bounds. A slice's pointer keeps its
GC allocation alive. When a list grows, an existing slice continues to address
the old allocation and keeps its original length. Slices do not append or resize.

Strings keep their separate immutable representation. Explicit conversions
between strings and writable byte slices copy bytes. Raw slice construction
and typed-storage-to-byte reinterpretation require `unsafe`; native storage
must remain valid for every use.

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
any std::io::Reader & std::io::Writer // Multiple interface bounds
```

Here `Drawable` is a user-defined interface. Each value has a concrete
underlying type that implements the listed interfaces.

## Opaque Return Types

`some Interface` in a return position hides one concrete implementing type.
Unlike `any Interface`, the concrete type is fixed by the function's definition.

```taro
interface Counted {
    func count() -> int32;
}

struct One {}
conform One to Counted {
    func count() -> int32 { 1 }
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
    var x: _ = 42           // Inferred as int32
    var list: [_] = [1, 2]  // Inferred as [int32]
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
    func clone() -> Self;
}
```
