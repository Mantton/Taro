# Generics

This chapter covers type parameters, constraints, and generic programming in Taro.
Each code block is an independent example. Blocks containing only declarations
can be checked with an empty `func main() {}` appended.

## Type Parameters

Type parameters make types and functions polymorphic.

```taro
// Single type parameter
struct Box[T] {
    value: T;
}

// Multiple type parameters
struct Pair[A, B] {
    first: A;
    second: B;
}

// On functions
func identity[T](value: T) -> T {
    return value
}

func swap[T, U](pair: (T, U)) -> (U, T) {
    return (pair.1, pair.0)
}
```

---

## Type Parameter Bounds

Constraints on what types can be used as arguments.

```taro
import std.hash.Hashable

// Single bound
func same[T: Equatable](_ a: T, _ b: T) -> bool { a == b }

// Multiple bounds (intersection)
func process[T: Hashable & Equatable](item: T) { }

// On structs
struct Cache[K: Hashable, V] {
    data: Dictionary[K, V];
}
```

---

## Where Clauses

More complex constraints using where clauses.

```taro
import std.hash.Hashable

// Basic conformance
func compare[T](a: T, b: T) -> bool where T: Equatable {
    return a == b
}

// Multiple requirements
func pair[K, V](_ key: K, _ value: V) -> (K, V) where K: Hashable, V: Clone {
    return (key, value.clone())
}

// Same-type requirements
interface Source {
    type Item;
    func get(&self) -> Self.Item;
}

func readInt[C](_ source: C) -> int32 where C: Source, C.Item == int32 {
    return source.get()
}

// Complex constraints
func combine[A, B, R](
    a: A,
    b: B,
    with f: (A, B) -> R,
) -> R where A: Clone, B: Clone {
    return f(a.clone(), b.clone())
}
```

For functions, `where` follows the return type (or the parameter list when no
return type is written). Keep it on that line: a newline before `where` can
insert a semicolon and end the declaration. Multiline parameter lists need a
comma before each newline, including after the final parameter.

---

## Const Generics

Compile-time constant values as generic parameters.

```taro
// Array with compile-time size
struct FixedArray[T, const N: usize] {
    data: [T; N];
}

func main() {
    let arr: FixedArray[int32, 3] = FixedArray[int32, 3] { data: [1, 2, 3] }
}

// Default const values
struct Buffer[T, const SIZE: usize = 1024] {
    data: [T; SIZE];
}
```

Array lengths use `usize`. Supply the const argument when constructing
`FixedArray`; the result annotation does not infer it for a bare `FixedArray { ... }`.

---

## Default Type Parameters

Type parameters can have default types.

```taro
import std.hash.{Hasher, DefaultHasher}

struct HashState[H: Hasher = DefaultHasher] {
    hasher: H;
}

func main() {
    // Can omit defaulted parameters: HashState means HashState[DefaultHasher].
    let state: HashState = HashState { hasher: DefaultHasher() }
}
```

`Hashable`, `Hasher`, and `DefaultHasher` come from `std.hash`; they are not
part of the prelude. The standard library's
`Dictionary[Key: Hashable, Value]` does not take a hasher parameter.

---

## Associated Types

Types defined within interfaces.

```taro
interface Container {
    type Element;

    func get(&self, index: usize) -> Optional[&Self.Element];
    func set(&mut self, index: usize, value: Self.Element);
}

// Constraining associated types
func firstOrZero[C](container: C) -> int32 where C: Container, C.Element == int32 {
    match container.get(index: 0) {
        case .some(value) => *value
        case .none => 0
    }
}
```

The prelude's iteration protocol is `Iterator`, which declares
`type Element` and `func next(&mut self) -> Optional[Self.Element]`:

```taro
func sum[I](iter: I) -> int32 where I: Iterator, I.Element == int32 {
    var total = 0
    var source = iter
    while let item = source.next() {
        total += item
    }
    return total
}
```

---

## Generic Implementations

Implementations can be generic and constrained.

```taro
struct Stack[T] {
    items: List[T];
}

// Unconditional implementation
impl[T] Stack[T] {
    func isEmpty(&self) -> bool {
        return self.items.isEmpty()
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

// Implementation with additional type parameters
impl[T] Stack[T] {
    func mapped[U](&self, _ f: (&T) -> U) -> Stack[U] {
        var result = List[U]()
        for item in &self.items {
            result.append(f(item))
        }
        return Stack[U] { items: result }
    }
}
```

These target `Stack` rather than `List` because inherent methods can only be
added to types from the current package. See
[Declarations](./declarations.md#implementation-declaration).

### Universal Blanket Implementations

An interface implementation may target its type parameter directly. This
provides an implementation for every type that satisfies the `where` clause.

```taro
interface Renderable {
    func render(&self) -> string;
}

interface Display {
    func display(&self) -> string;
}

impl[T] Renderable for T where T: Display {
    func render(&self) -> string {
        return self.display()
    }
}
```

Universal blanket implementations are intentionally coherent: the interface
must be declared in the current package, and a blanket implementation may not
overlap another blanket or concrete implementation. Taro does not specialize
one implementation over another. Inherent implementations such as `impl[T] T`
are not permitted.

---

## Type Argument Inference

The compiler can infer type arguments in many contexts.

```taro
func newList[T]() -> List[T] { return [] }
func consumeInts(_ values: List[int32]) {}

func main() {
    // Explicit
    let ints = newList[int32]()

    // Inferred from annotation
    let strings: List[string] = newList()

    // Inferred from the parameter type in the same expression
    consumeInts(newList())
}
```

Later statements do not supply this context: `var nums = newList()` needs a
type annotation or explicit type argument even if a later statement appends an integer.

---

## Trailing Commas

Type parameter lists and argument lists allow trailing commas. Use a comma
before a newline that precedes the closing bracket, so automatic semicolon
insertion does not terminate the final element.

```taro
struct MultiGeneric[
    A: Clone,
    B: Copy,
    C,  // Trailing comma allowed
] { }

func main() {
    let value: MultiGeneric[
        string,
        int32,
        bool,  // Trailing comma allowed
    ] = MultiGeneric { }
}
```
