# Declarations

This chapter covers all top-level and nested declarations in Taro.

## Visibility

Declarations can have visibility modifiers.

```taro
public struct PublicType { }    // Accessible everywhere
private struct PrivateType { }  // Module-private (default)

public func publicFunction() { }
private func privateFunction() { }
```

## Attributes

Attributes provide metadata for declarations.

```taro
@inline
func fastFunction() { }

@deprecated
struct OldType { }
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
interface Comparable: Equatable {
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

---

## Function Declaration

Functions are the primary units of code.

```taro
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
func greet(name: string = "World") {
    print("Hello, " + name)
}

// Variadic parameters
func sum(nums: int32...) -> int32 {
    // nums is a list
    var total = 0
    for n in nums { total += n }
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

// Self parameters (in interfaces/implementations)
func double(&self) -> int32          // Mutable borrow
func value(&const self) -> int32     // Immutable borrow
```

---

## Implementation Declaration

Implementations add functionality to existing types.

```taro
// Basic implementation
impl int32 {
    func double(&self) -> int32 {
        return self * 2
    }
}

// Implementation of interface
impl Hashable for int32 {
    func hash(&self) -> int64 {
        return self as int64
    }
}

// Generic implementation
impl[T] List[T] {
    func first(&self) -> T? {
        return self[0]
    }
}

// Constrained implementation
impl[T] List[T] where T: Equatable {
    func contains(&self, item: T) -> bool {
        for element in self {
            if element == item { return true }
        }
        return false
    }
}
```

---

## Type Alias Declaration

Type aliases create alternative names for types.

```taro
// Simple alias
type Meters = int32
type UserId = string

// Generic alias
type StringMap[V] = Map[string, V]
type Callback[T] = (T) -> void

// Associated type constraint
type Key: Hashable
type Element: Equatable & Hashable
```

---

## Namespace Declaration

Namespaces group related declarations.

```taro
namespace Math {
    const PI: float64 = 3.14159;
    const E: float64 = 2.71828;
    
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
    func printf(format: *const int8) -> int32;
    func malloc(size: usize) -> *void;
    func free(ptr: *void);
}
```

---

## Import Declaration

Imports bring items into scope.

```taro
// Import single item
import std.io.File

// Import with alias
import std.io.File as IoFile

// Import multiple items
import std.{io, fs, net}

// Glob import (all public items)
import std.io.*

// Nested path
import std.collections.{List, Map, Set}
```

---

## Export Declaration

Exports re-export items from the current module.

```taro
export std.io.File
export internal.utils.*
```

---

## Constant Declaration

Constants define compile-time values.

```taro
const PI: float64 = 3.14159
const MAX_SIZE: int32 = 1024
const NAME: string = "Taro"
```

---

## Variable Declaration (Top-Level)

Top-level variables are module-level state.

```taro
let globalConfig: Config = Config { }
var counter: int32 = 0
```

---

## Operator Declaration

Custom operator implementations for types.

```taro
impl Point {
    operator +(a: Point, b: Point) -> Point {
        return Point { x: a.x + b.x, y: a.y + b.y }
    }
    
    operator ==(a: Point, b: Point) -> bool {
        return a.x == b.x && a.y == b.y
    }
}
```
