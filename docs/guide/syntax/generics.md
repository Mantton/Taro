# Generics

This chapter covers type parameters, constraints, and generic programming in Taro.

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
// Single bound
func sort[T: Comparable](items: [T]) -> [T] { }

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
// Basic conformance
func compare[T](a: T, b: T) -> bool where T: Equatable {
    return a == b
}

// Multiple requirements
func merge[K, V](a: Dictionary[K, V], b: Dictionary[K, V]) -> Dictionary[K, V]
    where K: Hashable, V: Clone {
    // ...
}

// Same-type requirements
func process[C](container: C) where C: Container, C.Item == int32 {
    // C.Item must be int32
}

// Complex constraints
func combine[A, B, R](
    a: A,
    b: B,
    with f: (A, B) -> R
) -> R where A: Clone, B: Clone {
    // ...
}
```

---

## Const Generics

Compile-time constant values as generic parameters.

```taro
// Array with compile-time size
struct FixedArray[T, const N: int32] {
    data: [T; N];
}

// Usage
let arr: FixedArray[int32, 10] = FixedArray { }

// Default const values
struct Buffer[T, const SIZE: int32 = 1024] {
    data: [T; SIZE];
}
```

---

## Default Type Parameters

Type parameters can have default types.

```taro
struct Table[K: Hashable, V, H: Hasher = DefaultHasher] {
    // ...
}

// Can omit defaulted parameters
let table: Table[string, int32] = Table { }
// Same as: Table[string, int32, DefaultHasher]
```

`Hasher` and `DefaultHasher` come from `std.hash`. Note that std's own
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
func firstOrZero[C](container: C) -> int32
    where C: Container, C.Element == int32 {
    match container.get(0) {
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
func make[T]() -> List[T] { return [] }

// Explicit
let ints: List[int32] = make[int32]()

// Inferred from annotation
let strings: List[string] = make()

// Inferred from usage
let nums = make[int32]()
nums.append(42)  // Type known from append
```

---

## Trailing Commas

Type parameter lists and argument lists allow trailing commas.

```taro
struct MultiGeneric[
    A: SomeBound,
    B: OtherBound,
    C,  // Trailing comma allowed
] { }

let value: MultiGeneric[
    TypeA,
    TypeB,
    TypeC,  // Trailing comma allowed
] = MultiGeneric { }
```
