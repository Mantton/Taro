# Taro Language Syntax Guide

This guide describes Taro's syntax, with examples of declarations, expressions,
and generic programming. Type and signature fragments are identified separately
from complete examples.

## Table of Contents

1. [Lexical Elements](./lexical.md) - Identifiers, literals, keywords, operators
2. [Types](./types.md) - Type syntax including generics
3. [Declarations](./declarations.md) - Structs, enums, functions, interfaces, etc.
4. [Statements](./statements.md) - Control flow and variable declarations
5. [Expressions](./expressions.md) - All expression types and operators
6. [Patterns](./patterns.md) - Pattern matching syntax
7. [Generics](./generics.md) - Type parameters, bounds, and where clauses
8. [Special Syntax](./special.md) - ASI, shorthands, and edge cases

## Quick Overview

Taro is a statically-typed systems programming language with:
- Strong type inference
- Algebraic data types (enums with associated values)
- Pattern matching
- Interfaces for polymorphism
- References, raw pointers, and automatic garbage collection (GC)
- Automatic semicolon insertion (ASI)
- `printf`/`sprintf`-style formatted output (`%d`, `%s`, `%v`, `%%`) with compile-time checks for literal format strings
- Python-style f-strings: `f"Hello, {name}"` (desugared to `std.sprintf`)

### Hello World

```taro
func main() {
    println("Hello, World!")
}
```

### Key Features

```taro
// Struct definition
struct Point {
    x: int32;
    y: int32;
}

struct Profile {
    name: string;
}

struct User {
    profile: Profile?;
}

// Result is an enum provided by the standard prelude.
func handle(_ r: Result[int32, string]) -> int32 {
    match r {
        case .ok(value) => value
        case .err(_) => 0
    }
}

// Result propagation
func increment(_ input: Result[int32, string]) -> Result[int32, string] {
    let value = input!
    return .ok(value + 1)
}

func main() {
    let point = Point { x: 3, y: 4 }
    let double = |x: int32| x * 2
    let user: User? = .some(User { profile: .some(Profile { name: "Taro" }) })
    let name = user?.profile?.name ?? "Unknown"
    println(name)
    assert(double(point.x) == 6, "closure result")
    assert(handle(increment(.ok(41))) == 42, "propagated result")
}
```
