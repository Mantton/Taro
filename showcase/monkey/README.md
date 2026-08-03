# Monkey, in Taro

Both books. A tree-walking interpreter for the Monkey language from Thorsten
Ball's *Writing an Interpreter in Go*, and the bytecode compiler and stack
machine from its sequel *Writing a Compiler in Go* — written the way Taro wants
to be written rather than transliterated from the Go original.

Monkey's syntax and semantics are the specification. The implementation is not.

Both engines are complete, and both are kept. They share the lexer, parser, AST
and object system, which is what makes it possible to run the same program
through each and check that they agree.

```
taro run .                          # REPL, on the bytecode machine
taro run . -- script.monkey         # run a file
taro run . -- -e '1 + 2 * 3'        # evaluate one expression
taro run . -- --engine eval …       # use the tree-walking evaluator instead
taro run . -- --bench 30            # time both engines on fibonacci(30)
taro test .                         # 108 tests
```

## Layout

| Path | What lives there |
| --- | --- |
| `src/token/` | `TokenKind` and its payload-free companion `TokenTag` |
| `src/lexer/` | Source to tokens, tracking line and column |
| `src/ast/` | `Expression` and `Statement`, plus a canonical renderer |
| `src/parser/` | A Pratt parser producing positioned errors |
| `src/object/` | Values, hash keys, environments, builtins |
| `src/eval/` | The tree-walking evaluator and its error type — book one |
| `src/code/` | Instruction encoding, decoding and disassembly — book two |
| `src/compiler/` | Symbol table, scopes, and the compiler |
| `src/vm/` | Frames and the stack machine |
| `src/repl/` | The interactive session, either engine |
| `src/tests/` | Lexer, parser, evaluator, code, compiler, VM and cross-engine tests |

## Book one: the evaluator

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

## Book two: the compiler and machine

**An instruction is a typed value; the bytecode is still bytes.** The reference
implementation represents an instruction as a bare opcode byte and passes its
operands separately as `...int`, checking them against a table of operand widths
at run time. Nothing ties an opcode to the number or size of the operands it
takes, so `Make(OpConstant)` with no operands, or `Make(OpGetLocal, 70000)` with
one too large for the byte it is written into, are both accepted and produce
silently wrong bytecode.

`Instruction` carries its operands in the case, declared at the width they
encode to:

```taro
case constant(uint16)
case getLocal(uint8)
case closure(constant: uint16, free: uint8)
```

Those mistakes stop being representable. What is left is a flat byte stream —
this is bytecode, not a tree of instruction objects — with `encode` and `decode`
as the only way in and out.

**One decoder, so the disassembler cannot lie.** The machine and the disassembler
both read instructions through the same `decode`. In the reference implementation
they are separate code paths that read operands independently, which is a second
place for the encoding to be misunderstood. Here a disassembly cannot describe
the bytes differently from how they will run.

**The operand widths became real errors.** Because an index has to be narrowed to
the `uint16` or `uint8` that carries it, the compiler has to say what happens when
it does not fit. `CompileError` names each case — `tooManyConstants`,
`tooManyLocals`, `tooManyFreeVariables`, `jumpOutOfRange`. The Go version checks
none of them: it writes whatever `int` it has into the reserved bytes and keeps
what fits, so a program with more than 65536 constants quietly runs the wrong
ones.

**Only jumps are patched.** A jump is emitted before its destination is known, so
it goes out with a placeholder. The reference implementation back-patches with a
general `changeOperand` that will overwrite any instruction with any operand,
guarded only by a comment noting the unchecked assumption that the replacement is
the same width. `patchJump` accepts only the one instruction that is ever
patched, so the assumption holds by construction — both jumps take a single
`uint16`, so the widths cannot differ.

**"Nothing emitted yet" is a state of the type.** The compiler tracks the last
instruction it emitted as `Optional[EmittedInstruction]`. The reference
implementation uses a zero-valued struct whose opcode field reads as
`OpConstant` — the first opcode — and then has to guard every inspection with a
separate length check to avoid acting on it.

**Symbol scopes are an enum.** The book makes `SymbolScope` a `string`, so
`SymbolScope("GLOBAL")` is a typo away from a run-time surprise, and loading a
symbol needs a default branch reporting "unresolved". Naming the alternatives
makes the load site exhaustive.

**Builtins have one implementation and one index.** They live in `src/object/`,
called by both engines, so the two cannot disagree about what `first([])` does.
`Builtin.index()` is the single source for the `OpGetBuiltin` operand, where the
reference implementation keeps a map in the evaluator and a parallel slice in the
machine and relies on them staying in step.

**Everything callable is a closure.** Even a function that captures nothing, so
the machine has no branch on whether a callee is a bare function or a closure,
and the top-level program is wrapped as one too — removing the special case for
the outermost frame.

### Things the reference implementation gets wrong

- **Division by zero** panics in Go, taking the interpreter with it. Both engines
  here report `division by zero`.
- **Argument count** is never checked by the evaluator; Go indexes the argument
  list by parameter position and crashes on a short call. Both engines report it.
- **`"a" == "a"`** fails in the book's evaluator, because string comparison never
  reaches the string case. Here it works.
- **`add5`** lexes as `add` then `5`, because the book reuses its letter test for
  identifier continuation. Digits are allowed after the first character here.
- **`if x { }`** renders as `ifx`, because `IfExpression.String()` writes `if`
  straight against the condition. A space is added here, so the canonical form
  reads back.
- **`len` on a hash** reports `must be ARRAY`, though `len` also takes strings.
  The message names no single kind here.

### Limits

`MAX_NESTING_DEPTH` in the parser bounds how deep a tree the parser will build.
`MAX_CALL_DEPTH` (128) bounds the evaluator, because each Monkey call costs
several native frames. The machine keeps frames in a list rather than on the
native stack, so its own bound — `MAX_FRAMES`, 1024 — is far higher, and a
recursion 500 deep runs there and is refused by the evaluator.

## REPL

```
>> let adder = fn(x) { fn(y) { x + y } };
>> adder(2)(3)
5
>> :bytecode
showing compiled instructions
>> 1 + 2 * 3
0000 OpConstant 0
0003 OpConstant 1
0006 OpConstant 2
0009 OpMul
0010 OpAdd
0011 OpPop
7
>> :engine eval
now running on the tree-walking evaluator (bindings are per engine)
```

Bindings persist across lines — the machine keeps its symbol table, constants and
globals between them, so a name bound on one line resolves on the next. `:help`
lists the commands: `:engine` switches engine, `:bytecode` toggles the
disassembly, `:tokens` prints a token stream, `:tree` toggles the parse tree,
`:reset` forgets every binding. Parse errors point at the offending column, which
the book's REPL cannot do because its errors carry no position.

## How Taro compares as a host language

The second book ends by timing `fibonacci(35)` on both engines, which makes it
the one benchmark every Monkey implementation reports. `--bench 35` here runs
the book's own benchmark source, so the numbers are comparable.

First, the two that matter most, measured on one machine (Apple M2, both
`--release`, both running the book's own benchmark source):

| Implementation | Tree-walking | Bytecode VM | VM speedup |
| --- | --- | --- | --- |
| Go 1.26.2 | 10.2 s | 3.6 s | 2.9x |
| **Taro — this implementation** | **217.1 s** | **144.3 s** | **1.5x** |

And published numbers for other hosts, each on its own machine, so read those as
ratios rather than absolute times:

| Implementation | Tree-walking | Bytecode VM | VM speedup |
| --- | --- | --- | --- |
| Go — reference | 12.8 s | 2.9 s | 4.4x |
| Kotlin / JVM | 2.8 s | 3.8 s | 0.7x |
| Kotlin / Native | 9.9 s | 4.3 s | 2.3x |
| C++ — `shared_ptr` | 126.2 s | 19.6 s | 6.4x |

Two things are worth taking from those before Taro's row:

**A bytecode VM is not automatically faster than a tree-walker.** On the JVM the
evaluator wins (2.8 s against 3.8 s), because a JIT does very well on the small
hot recursive functions a tree-walker spends its time in, while the VM's dispatch
loop is one big opaque switch. Go's 3–4× gap is a property of Go, not of the
architecture.

**The host's memory management dominates.** The C++ implementation is *slower
than Go* — 10× on the evaluator, 7× on the VM — and its author traces this to
`shared_ptr` overhead, noting that `fibonacci(35)` performs 1,191,418,117 heap
allocations totalling over 61 GB. Monkey is an allocation benchmark wearing a
Fibonacci costume, and whatever the host does per allocation is what gets
measured.

### Where Taro lands, and why

Against Go on the same machine and the same source: **21x** on the evaluator,
**40x** on the machine. Both engines answer 9227465, so this is a cost
question, not a correctness one.

The revealing figure is not either time but the gap between them. Compiling
Monkey buys **1.5x** here, against 2.9x for Go measured beside it. A bytecode VM
does strictly less work per operation than a tree-walker — no environment
rebuilt per call, no tree re-walked — so that win shrinking to 1.5x means
something is being paid per operation that swamps the difference. Both engines
pay it equally, which is why the ratio compresses.

That cost is Taro's per-call and per-loop runtime bookkeeping, and it is
measurable directly. A 10M-iteration loop of inline additions takes 76 ms; the
same loop calling a one-line function takes 201 ms. That is **12.5 ns of
overhead on a function call** that should cost a cycle or two, or nothing at all
once inlined. It is not inlined: every function is emitted with a preamble of
`__rt__logical_stack_push`, two `__gc__poll` calls and a matching
`__rt__logical_stack_pop`, and those opaque calls keep LLVM from inlining
anything they appear in. A safepoint poll is also emitted on every loop
back-edge.

An interpreter is the worst possible shape for that. Its hot loop is a tower of
small functions — fetch, decode, advance, push, pop — so the machine pays the
preamble several times per bytecode instruction it executes. That also explains
why the machine's advantage is *smaller* on the book's `fibonacci`, which nests
two conditionals per call, than on a flatter one written with `x < 2`: more
bytecode instructions per Monkey call means more preamble, so the more work the
machine does the more of its architectural advantage it hands back.

Most of that cost has since been removed, and the numbers above already include
the fix. Three changes, in increasing order of what they bought:

- `__gc__poll`'s fast path used to take the **global GC mutex** to compare an
  allocation counter against its threshold — a lock round-trip on every loop
  back-edge that also serialised every Taro thread against one lock. The answer
  is now published in an atomic.
- The logical stack is gone from generated code. Language-level frames are
  reconstructed from the native backtrace when a panic actually happens, rather
  than maintained by every call against the possibility of one.
- The safepoint poll became an inline load of a flag with a cold slow path,
  instead of an opaque call. That is what let LLVM start inlining small
  functions again.

Together those took the per-call overhead from **12.5 ns to 0.8 ns**, and this
benchmark from 760.6 s to 217.1 s on the evaluator and 653.2 s to 144.3 s on the
machine. The gap to Go narrowed from 69x to 21x, and from 173x to 40x. The
machine's advantage over the evaluator grew from 1.2x to 1.5x as the fixed cost
stopped masking it.

What is left is ordinary work rather than a structural problem: generic code is
now measurably slower than its monomorphic equivalent — `List[int64].at` costs
about twice a hand-written non-generic version, a difference that was invisible
while the poll dominated both.

None of this is Monkey's fault, and none of it is visible from the language
side — which is the point of building something like this against a young
compiler.

Sources: [monkey-plusplus](https://github.com/joshuanunn/monkey-plusplus),
[monkey.kt](https://github.com/MarioAriasC/monkey.kt), and Mario Arias'
[Kotlin/Go comparison](https://medium.com/@mario.arias.c/comparing-kotlin-and-go-implementations-of-the-monkey-language-ii-raiders-of-the-lost-performance-b9aa09945281).
