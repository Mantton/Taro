# Monkey, in Taro

A tree-walking interpreter for the Monkey language from Thorsten Ball's *Writing
an Interpreter in Go*, written the way Taro wants to be written rather than
transliterated from the Go original.

Monkey's syntax and semantics are the specification. The implementation is not.

```
taro run .                     # REPL
taro run . -- script.monkey    # run a file
taro run . -- -e '1 + 2 * 3'   # evaluate one expression
taro test .                    # 45 tests
```

## Layout

| Path | What lives there |
| --- | --- |
| `src/token/` | `TokenKind` and its payload-free companion `TokenTag` |
| `src/lexer/` | Source to tokens, tracking line and column |
| `src/ast/` | `Expression` and `Statement`, plus a canonical renderer |
| `src/parser/` | A Pratt parser producing positioned errors |
| `src/object/` | Values, hash keys, environments, builtins |
| `src/eval/` | The evaluator and its error type |
| `src/repl/` | The interactive session |
| `src/tests/` | Lexer, parser and evaluator tests |

## Where it differs from the book, and why

**`return` and errors share one channel.** Evaluation returns
`Result[Object, Signal]`, where `Signal` is either `.failed(EvalError)` or
`.produced(Object)`. Both are non-local exits, so `!` does the unwinding: no
statement loop checks whether the previous statement returned or failed. The Go
version checks for *both* after every evaluation, and carries a `ReturnValue`
object type purely to make that work. Only `applyFunction` intercepts
`.produced`, which is exactly where a `return` should stop.

**Errors are structured, not formatted.** `EvalError` is a payload enum, so a
caller can react to `identifierNotFound` specifically instead of matching on
message text. The messages are a rendering choice, produced by `describe()`.

**Hash keys keep their value.** The book reduces each key to a 64-bit hash and
keys its map on that, so two distinct strings that collide silently become one
entry. `HashKey` carries the value and implements `Hashable`, letting
`Dictionary` settle collisions by equality — which also removes the need for the
book's parallel `HashPair` table holding the original keys.

**The AST is payload enums, matched exhaustively.** Recursive positions go
through `&Expression`, since Taro rejects a directly recursive enum. Operators
are enums rather than strings, so an unhandled operator is a compile error rather
than a runtime `unknown operator`. Dispatch is a `match` on token kind instead of
Go's two function maps, so a token that gains a new meaning cannot silently fall
through to "no prefix parse function found".

**Environments are shared by reference.** A closure holds `&mut Environment`, so
a binding made after the function literal is evaluated — including the one naming
the function itself — is visible from the body. That is what makes recursion
work, and it is a genuine reference cycle for the collector to handle.

### Things the reference implementation gets wrong

- **Division by zero** panics in Go. Here it is `error: division by zero`.
- **Argument count** is never checked; Go indexes the argument list by parameter
  position and crashes on a short call. Here it is reported.
- **`"a" == "a"`** fails in the book, because string comparison never reaches the
  string case. Here it works.
- **`add5`** lexes as `add` then `5`, because the book reuses its letter test for
  identifier continuation. Digits are allowed after the first character here.
- **`if x { }`** renders as `ifx`, because `IfExpression.String()` writes `if`
  straight against the condition. A space is added here, so the canonical form
  reads back.
- **`len` on a hash** reports `must be ARRAY`, though `len` also takes strings.
  The message names no single kind here.

### Limits

`MAX_NESTING_DEPTH` in the parser and `MAX_CALL_DEPTH` in the evaluator bound
recursion, reporting an ordinary error instead of exhausting the native stack.
Taro reports stack exhaustion rather than dying silently, but that report aborts
the process — an interpreter should hand the mistake back to the program that
made it.

## REPL

```
>> let adder = fn(x) { fn(y) { x + y } };
>> adder(2)(3)
5
>> :tree
showing the parse tree
>> 1 + 2 * 3
tree: (1 + (2 * 3))
7
```

Bindings persist across lines. `:help` lists the commands: `:tokens` prints a
token stream, `:tree` toggles the parse tree, `:reset` clears the environment.
Parse errors point at the offending column, which the book's REPL cannot do
because its errors carry no position.
