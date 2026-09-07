# Declarations

This chapter describes top-level and nested declarations in Taro. Declaration
examples without `main` can be checked with an empty `func main() {}` appended.
Examples that continue earlier definitions are identified in the surrounding text.

## Visibility

Declarations are public by default. Use `private` to restrict access to the
containing scope.

```taro
public struct PublicType { }    // Accessible everywhere
private struct PrivateType { }  // Private to this module
struct DefaultPublicType { }    // Public when no modifier is present

public func publicFunction() { }
private func privateFunction() { }
```

## Attributes

Attributes provide metadata for declarations.

```taro
@inline
func fastFunction() { }

@noinline
func separateFunction() { }
```

---

## Struct Declaration

Structs define composite data types with named fields.

```taro
// Basic struct
struct Point {
    x: int32;
    y: int32;
}

// With visibility on fields
struct User {
    public name: string;
    private password: string;
}

// Readonly fields (immutable after construction)
struct Config {
    readonly version: int32;
    readonly name: string;
}

// Generic struct
struct Box[T] {
    value: T;
}

// Multiple generics
struct Pair[A, B] {
    first: A;
    second: B;
}
```

### Struct Layout (`@repr`)

Struct layout representation can be selected with `@repr("...")`:

```taro
// Default if omitted: @repr("Taro")
@repr("Taro")
struct PackedPoint {
    x: int8;
    y: int64;
    z: int8;
}

// C-compatible declaration-order layout
@repr("C")
struct CHeader {
    tag: uint16;
    len: uint32;
}
```

- `@repr("Taro")`: optimization-oriented layout (field order is not source-stable).
- `@repr("C")`: standard C-style declaration-order layout for FFI-sensitive types.

---

## Enum Declaration

Enums define sum types with multiple variants.

```taro
// Simple enum (unit variants)
enum Color {
    case red, green, blue;
}

// With explicit discriminants
enum Status {
    case ok = 0, err = 1;
}

// Associated values (tuple variants)
enum Result[T, E] {
    case ok(T), err(E);
}

// Mixed variants
enum Message {
    case quit;                     // Unit variant
    case move(x: int32, y: int32); // Named fields
    case write(string);            // Positional field
}

// Multiple case statements
enum Direction {
    case north;
    case south;
    case east, west;
}
```

---

## Interface Declaration

Interfaces define contracts that types can implement.

```taro
// Basic interface
interface Drawable {
    func draw(&self);
}

// With return types
interface Cloneable {
    func clone(&self) -> Self;
}

// Interface inheritance
interface Equal {
    func equal(&self, other: &Self) -> bool;
}

interface Comparable: Equal {
    func compare(&self, other: &Self) -> int32;
}

// Associated types
interface Container {
    type Item;
    func get(&self) -> Self.Item?;
}

// Associated constants
interface Named {
    const NAME: string;
}

// Multiple methods
interface Collection {
    type Element;
    func count(&self) -> int32;
    func isEmpty(&self) -> bool;
    func contains(&self, element: Self.Element) -> bool;
}
```

Current limitation: inheriting from imported standard interfaces with declarations
such as `interface Derived: Clone {}` or `interface Derived: Equatable {}`
triggers an internal compiler failure. Inheritance between local interfaces,
as in the example above, works.

Interfaces may require computed properties and may provide default accessor
bodies. A conforming type can satisfy an accessor with a stored field, an
inherent computed property, or an accessor declared in the conformance:

```taro
interface Counted {
    var count: int32 {
        get(&self)
        set(&mut self, value: int32)
    };
}

interface DefaultCount {
    var count: int32 {
        get(&self) { 0 }
    };
}
```

If multiple interfaces expose the same property name, qualify the access with
the interface when the receiver type does not identify a unique candidate.

---

## Function Declaration

Functions are the primary units of code.

```taro
struct Point {
    x: int32;
    y: int32;
}

// Basic function
func greet() {
    print("Hello!")
}

// With parameters
func add(a: int32, b: int32) -> int32 {
    return a + b
}

// Labeled parameters
func move(from source: Point, to destination: Point) {
    // 'from' and 'to' are external labels
    // 'source' and 'destination' are internal names
}

// Default parameter values
func greetPerson(name: string = "World") {
    print("Hello, " + name)
}

// Variadic parameters
func sum(_ nums: int32...) -> int32 {
    // nums is a Span[int32]; iteration produces immutable references.
    var total = 0
    for n in nums { total += *n }
    return total
}

// Generic functions
func identity[T](value: T) -> T {
    return value
}

// With where clause
func compare[T](a: T, b: T) -> bool where T: Equatable {
    return a == b
}

// Async functions place `async` after the parameter list
func loadCount() async -> int32 { 42 }

func fetchCount() async -> int32 {
    return await loadCount()
}

func main() {
    let origin = Point { x: 0, y: 0 }
    move(from: origin, to: Point { x: 1, y: 2 })
    greetPerson()
    let result = add(a: 1, b: sum(2, 3, 4))
}
```

Parameter names are also argument labels unless `_` suppresses the label.
A separate label, as in `from source: Point`, keeps the external and internal
names distinct. Variadic parameters must be last and cannot have defaults.

Self parameters appear in interfaces and implementations:

```taro
interface Value {
    func value(&self) -> int32;       // Immutable borrow (the default)
    func constant(&const self) -> int32; // Explicitly immutable borrow
    func update(&mut self);          // Mutable borrow
    func consume(self) -> int32;     // By value
}
```

---

## Implementation Declaration

Implementations add functionality to existing types.

```taro
struct Point {
    x: int32;
    y: int32;
}

interface Drawable {
    func draw(&self);
}

struct Stack[T] {
    items: List[T];
}

// Basic implementation
impl Point {
    func magnitudeSquared(&self) -> int32 {
        return self.x * self.x + self.y * self.y
    }
}

// Implementation of interface
impl Drawable for Point {
    func draw(&self) {
        println(f"({self.x}, {self.y})")
    }
}

// Generic implementation
impl[T] Stack[T] {
    func first(&self) -> Optional[&T] {
        return self.items.get(0)
    }
}

// Constrained implementation
impl[T] Stack[T] where T: PartialEq {
    func contains(&self, item: &T) -> bool {
        for element in &self.items {
            if element == item { return true }
        }
        return false
    }
}
```

Inherent methods can only be added to types declared in the current package.
`impl[T] List[T] { ... }` is rejected outside std with *cannot add inherent
methods to type from another package without interface conformance*. A local
interface may instead be implemented for a foreign type, such as
`impl MyInterface for int32`, subject to conformance coherence rules.

### Initializer Shorthand

A static method named `new` can be called through the type itself. The type-call
form is the idiomatic spelling for initialization; the explicit `.new` form is
also valid.

```taro
struct Point {
    x: int32
    y: int32
}

impl Point {
    func new(x: int32, y: int32) -> Self {
        return Point { x, y }
    }
}

func main() {
    let point = Point(x: 10, y: 20)
    let samePoint = Point.new(x: 10, y: 20)
}
```

The shorthand participates in normal overload resolution. Generic types include
their type arguments before the call, for example `Box[int32](42)` when `Box[T]`
defines `func new(_ value: T) -> Self`.

### Computed Properties

Computed properties use explicit `get`/`set` accessor blocks and are accessed
with field-like syntax.

```taro
struct Counter { raw: int32; }

impl Counter {
    var value: int32 {
        get(&self) {
            return self.raw
        }
        set(&mut self, value: int32) {
            self.raw = value
        }
    }
}
```

Getter-only properties are read-only:

```taro
struct User { _id: int64; }

impl User {
    var id: int64 {
        get(&self) {
            return self._id
        }
    }
}
```

Getters may be async:

```taro
struct Session { id: int64; }
struct SessionStore {}

impl SessionStore {
    func loadCurrent(&self) async -> Session {
        Session { id: 1 }
    }

    var current: Session {
        get(&self) async {
            return await self.loadCurrent()
        }
    }
}
```

Rules:

- Exactly one `get` accessor is required.
- `set` is optional.
- `set` must use `set(&mut self, value: T)` where `T` matches the property type.
- `set` cannot be `async`.
- Async getters require explicit await at the read site: `await obj.prop`.
- Compound assignment on a writable property evaluates the receiver once, reads
  through `get`, applies the assignment operator, and writes through `set`.
- Async getters cannot be used in compound assignment.
- Interfaces can require accessors or provide default accessor bodies.
- Stored fields and matching inherent properties can satisfy interface accessors;
  conformances may also declare explicit property implementations.
- `get` and `set` are contextual keywords only inside accessor blocks.

---

## Type Alias Declaration

Type aliases create alternative names for types.

```taro
import std.hash.Hashable

// Simple alias
type Meters = int32
type UserId = string

// Generic alias
type StringMap[V] = Dictionary[string, V]
type Callback[T] = (T) -> ()

interface Readable[Value] {
    func read(&self) -> Value;
}

interface Writable[Value] {
    func write(&mut self, _ value: Value);
}

// Transparent interface-set aliases
type ReadWrite = Readable[int32] & Writable[int32]
type Resource[Value] = Readable[Value] & Writable[Value]
type ResourceAlias[Value] = Resource[Value]

// Associated type constraints belong to interfaces.
interface Indexed {
    type Key: Hashable;
    type Element: Equatable & Hashable;
}
```

Continuing those definitions, an interface-set alias expands wherever an
interface list is accepted:

```taro
func copy[Value: ReadWrite](_ value: Value) {}
func erase(_ value: any ReadWrite) {}

struct Cell { value: int32; }
impl Readable[int32] for Cell {
    func read(&self) -> int32 { self.value }
}
impl Writable[int32] for Cell {
    func write(&mut self, _ value: int32) { self.value = value }
}
func cell() -> some ReadWrite { Cell { value: 0 } }
```

Interface-set aliases may be generic, nested, and exported across package
boundaries. Expansion is transparent and duplicate constituents are removed.
They are not concrete types, so a bare field or parameter type must use
`any ReadWrite` when dynamic dispatch is intended.

An interface set is also not a single conformance declaration. Implement each
constituent explicitly; `impl ReadWrite for File` and `struct File: ReadWrite`
are rejected. Circular interface-set aliases are diagnosed.

The `any` spelling remains significant: `type Boxed = any ReadWrite` aliases
one concrete existential type, while `type ReadWrite = Readable[int32] &
Writable[int32]` aliases the interface requirements themselves.

---

## Namespace Declaration

Namespaces group related declarations.

```taro
namespace Math {
    const PI: double = 3.14159;
    const E: double = 2.71828;
    
    func abs(x: int32) -> int32 {
        if x < 0 { return -x }
        return x
    }
}

// Nested namespaces
namespace Graphics {
    namespace Colors {
        const RED: int32 = 0xFF0000;
    }
}
```

---

## Extern Block

Extern blocks declare foreign functions (FFI).

```taro
extern "C" {
    func puts(_ text: *const uint8) -> int32;
    func malloc(_ size: usize) -> *mut uint8;
    func free(_ ptr: *mut uint8);
}
```

Use the `blocking` ABI for foreign calls that may park indefinitely. It uses
the C calling convention and symbol name while publishing the current GC
stack-map roots for the duration of the call.

```taro
extern "blocking" {
    func read(fd: int32, buffer: *mut uint8, count: usize) -> isize;
}
```

Blocking foreign functions must not call back into Taro before returning.

---

## Import Declaration

Imports bring items into scope.

```taro
// Import single item
import std.fs.File

// Import with alias
import std.fs.File as FsFile

// Import multiple items
import std.{io, fs, net}

// Glob import (all public items)
import std.io.*

// Nested path
import std.collections.{Dictionary, List, Set}
```

The standard prelude is available automatically unless a package sets
`no_std_prelude = true`. It provides common results, optionals, collections,
operators, marker interfaces, iteration interfaces, memory views, assertions,
and printing functions. Prefer their unqualified names in application code:

```taro
func copyAll[T: Copy](_ values: List[T]) -> Result[List[T], string] {
    return .ok(values)
}
```

The standard library itself disables the prelude and imports its dependencies
explicitly.

---

## Export Declaration

Exports re-export items from the current module.

```taro
export std.fs.File
export std.collections.*
```

---

## Constant Declaration

Constants define compile-time values.

```taro
const PI: double = 3.14159
const MAX_SIZE: int32 = 1024
const NAME: string = "Taro"
```

Constant initializers support literals, references to other constants, unary
and binary operators, primitive numeric and rune casts, and `if` expressions.
Only the selected `if` branch is evaluated. Aggregate construction and general
function calls are not constant expressions.

---

## Static Variable Declaration

Module and namespace state must use explicit static declarations.

```taro
static let applicationName: string = "Taro"
static var counter: int32 = 0
```

---

## Operator Overloading

Operators are overloaded by implementing the corresponding standard library
interface, not with an `operator` declaration. `operator` is reserved but
unimplemented.

```taro
struct Point {
    x: int32;
    y: int32;
}

impl Add for Point {
    func add(self, rhs: Point) -> Point {
        return Point { x: self.x + rhs.x, y: self.y + rhs.y }
    }
}
```

`std.ops` provides `Add`, `Sub`, `Mul`, `Div`, `Rem`, the bitwise operators, and
their `…Assign` counterparts for compound assignment. `Neg` and `Not` cover the
unary operators, and `PartialEq` / `Equatable` cover equality.
