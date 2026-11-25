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
import std::hash::Hashable

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

## Custom bound diagnostics

An interface can tell callers how to satisfy its bound. When a missing
conformance causes a call to fail, the compiler displays the message at the use site.

```taro
@onUnsatisfied("{Self} has no ranking; supply a ranking function or conform it to Ranked")
public interface Ranked {
    func rank() -> int32;
}
```

Write `{Self}` for the type that lacks the conformance. Write `{{` or `}}` for
a literal brace. The attribute takes one nonempty string literal. Imported
interfaces supply their messages to clients, including when a build reuses a
cached library.

## Where Clauses

More complex constraints using where clauses.

```taro
import std::hash::Hashable

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
    func get() -> Self::Item;
}

func readInt[C](_ source: C) -> int32 where C: Source, C::Item == int32 {
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
return type is written). It may start a new line, because a line that begins
with `where` continues the declaration; keep the body's `{` on the `where`
line. In multiline parameter lists the comma after the final parameter is
optional.

---

## Const Generics

Compile-time constant values as generic parameters.

```taro
// Array with compile-time size
struct FixedArray[T, const N: usize] {
    data: [T; N];
}

func main() {
    var arr: FixedArray[int32, 3] = FixedArray[int32, 3] { data: [1, 2, 3] }
    println("${arr.data[0]}")
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
struct Envelope[Payload = string] {
    value: Payload;
}

func main() {
    // Envelope means Envelope[string] when its parameter is omitted.
    var message: Envelope = Envelope { value: "hello" }
    var count: Envelope[int32] = Envelope { value: 42 }
    println("${message.value} ${count.value}")
}
```

An explicit argument selects another payload type. The default is a declared
type choice, independent of later uses of a variable.

---

## Associated Types

Types defined within interfaces.

```taro
interface Container {
    type Element;

    func get(index: usize) -> Optional[&Self::Element];
    func set(index: usize, value: Self::Element);
}

// Constraining associated types
func firstOrZero[C](container: C) -> int32 where C: Container, C::Element == int32 {
    match container.get(index: 0) {
        case .some(value) => *value
        case .none => 0
    }
}
```

When two interfaces declare an associated type with the same name, qualify
the projection with the interface. For example, `(T as Container).Element`
selects `Container`'s element type when `T: Container`. A concrete conforming
type can appear in place of `T`.

The prelude's iteration protocol is `Iterator`, which declares
`type Element` and `func next() -> Optional[Self::Element]`:

```taro
func sum[I](iter: I) -> int32 where I: Iterator, I::Element == int32 {
    var total = 0
    var source = iter
    while var item = source.next() {
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
extend[T] Stack[T] {
    func isEmpty() -> bool {
        return self.items.isEmpty()
    }
}

// Constrained implementation
extend[T] Stack[T] where T: PartialEq {
    func contains(item: &T) -> bool {
        for element in self.items {
            if element == *item { return true }
        }
        return false
    }
}

// Implementation with additional type parameters
extend[T] Stack[T] {
    func mapped[U, F: Fn(&T) -> U](_ f: F) -> Stack[U] {
        var result = List[U]::new()
        for item in self.items {
            result.append(f(&item))
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
    func render() -> string;
}

interface Display {
    func display() -> string;
}

conform[T] T to Renderable where T: Display {
    func render() -> string {
        return self.display()
    }
}
```

Universal blanket implementations are intentionally coherent: the interface
must be declared in the current package, and a blanket implementation may not
overlap another blanket or concrete implementation. Taro does not specialize
one implementation over another. Inherent implementations such as `extend[T] T`
are not permitted.

---

## Type Argument Inference

The compiler can infer type arguments in many contexts.

```taro
func newList[T]() -> List[T] { return [] }
func consumeInts(_ values: List[int32]) {}

func main() {
    // Explicit
    ints := newList[int32]()

    // Inferred from annotation
    var strings: List[string] = newList()

    // Inferred from the parameter type in the same expression
    consumeInts(newList())
    consumeInts(ints)
    println("${strings.len()}")
}
```

Later statements do not supply this context: `var nums = newList()` needs a
type annotation or explicit type argument even if a later statement appends an integer.

---

## Trailing Commas

Type parameter lists and argument lists allow trailing commas. They are
optional even when the closing bracket is on its own line, because newlines
inside brackets do not insert semicolons.

```taro
struct MultiGeneric[
    A: Clone,
    B,
    C,  // Trailing comma allowed
] { }

func main() {
    var value: MultiGeneric[
        string,
        int32,
        bool,  // Trailing comma allowed
    ] = MultiGeneric { }
    _ = value
}
```
