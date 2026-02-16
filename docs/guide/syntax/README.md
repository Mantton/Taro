# Taro Language Syntax Guide

Welcome to the comprehensive Taro language syntax guide. This documentation covers every aspect of the Taro programming language syntax.

## Table of Contents

1. [Lexical Elements](./lexical.md) - Identifiers, literals, keywords, operators
2. [Types](./types.md) - All type syntax including generics
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
- Memory safety through references and ownership
- Automatic semicolon insertion (ASI)
- `printf`/`sprintf`-style formatted output (`%d`, `%s`, `%v`, `%%`) with compile-time checks for literal format strings

### Hello World

```taro
func main() {
    print("Hello, World!")
}
```

### Key Features

```taro
// Struct definition
struct Point {
    x: int32;
    y: int32;
}

// Enum with associated values
enum Result[T, E] {
    case ok(T), err(E);
}

// Pattern matching
func handle(r: Result[int32, string]) -> int32 {
    match r {
        case .ok(value) => value
        case .err(_) => 0
    }
}

// Closures
let double = |x: int32| x * 2

// Optional chaining
let name = user?.profile?.name ?? "Unknown"
```
