# Monkey

This package implements both Monkey books by Thorsten Ball: a tree-walking
evaluator and a bytecode compiler with a stack virtual machine. Both engines
share the lexer, parser, AST, object model, environments, and builtins.

The implementation stays algorithmically comparable to the Go reference while
using Taro's enums, results, interfaces, collections, and garbage collector.

## Run

```bash
taro run .                            # REPL using the VM
taro run . -- script.monkey           # run a file
taro run . -- -e '1 + 2 * 3'          # evaluate source
taro run . -- --engine eval -e '1+2'  # use the evaluator
taro run . -- --bench 35              # benchmark both engines
taro test .
```

## Layout

| Path | Contents |
| --- | --- |
| `src/token/` | Tokens and token tags |
| `src/lexer/` | Positioned tokenization |
| `src/ast/` | Syntax tree and rendering |
| `src/parser/` | Pratt parser and diagnostics |
| `src/object/` | Values, environments, and builtins |
| `src/eval/` | Tree-walking evaluator |
| `src/code/` | Bytecode encoding and decoding |
| `src/compiler/` | Symbols, scopes, and bytecode compiler |
| `src/vm/` | Frames and stack machine |
| `src/repl/` | Interactive session |
| `src/tests/` | Unit and cross-engine tests |

## Design

The AST and runtime values use payload enums with exhaustive matching.
Evaluator control flow uses `Result[Object, Signal]`, allowing errors and
Monkey `return` statements to unwind through the same path.

Hash keys retain their original values, so Dictionary equality resolves hash
collisions. Closures retain environments by reference, including recursive
bindings.

Bytecode remains a flat byte stream. Typed `Instruction` cases define operand
widths, and the VM and disassembler share one decoder. The compiler reports
operand, constant, local, free-variable, argument, and jump overflows.

Both engines use the same builtin definitions. The VM represents every
function as a closure and uses reserved stack and frame storage addressed by
indices.

## REPL

Bindings persist between lines. `:help` lists the available commands:

- `:engine vm|eval` selects the engine.
- `:bytecode`, `:tokens`, and `:tree` toggle diagnostics.
- `:reset` clears bindings.

## Limits

The parser bounds syntax nesting. The evaluator limits Monkey call depth to 128
because calls consume native frames. The VM stores frames separately and allows
up to 1,024 nested calls.
