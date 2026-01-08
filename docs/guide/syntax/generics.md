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
    data: Map[K, V];
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
func merge[K, V](a: Map[K, V], b: Map[K, V]) -> Map[K, V]
    where K: Hashable, V: Cloneable {
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
) -> R where A: Cloneable, B: Cloneable {
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
struct Map[K: Hashable, V, H: Hasher = DefaultHasher] {
    // ...
}

// Can omit defaulted parameters
let map: Map[string, int32] = Map { }
// Same as: Map[string, int32, DefaultHasher]
```

---

## Associated Types

Types defined within interfaces.

```taro
interface Iterator {
    type Item;
    
    func next(&self) -> Self.Item?;
}

interface Container {
    type Element;
    
    func get(&self, index: int32) -> Self.Element?;
    func set(&self, index: int32, value: Self.Element);
}

// Constraining associated types
func sum[I](iter: I) -> int32 where I: Iterator, I.Item == int32 {
    var total = 0
    while let item = iter.next() {
        total += item
    }
    return total
}
```

---

## Generic Implementations

Implementations can be generic and constrained.

```taro
// Unconditional implementation
impl[T] List[T] {
    func isEmpty(&self) -> bool {
        return self.count == 0
    }
}

// Constrained implementation
impl[T] List[T] where T: Equatable {
    func contains(&self, element: T) -> bool {
        for item in self {
            if item == element { return true }
        }
        return false
    }
}

// Implementation with additional type parameters
impl[K, V] Map[K, V] {
    func mapValues[U](f: (V) -> U) -> Map[K, U] {
        var result: Map[K, U] = [:]
        for (key, value) in self {
            result[key] = f(value)
        }
        return result
    }
}
```

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
