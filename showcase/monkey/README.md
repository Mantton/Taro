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
`--release`, both running the book's own benchmark source). Taro's row is the
median of three runs with `TARO_WORKERS=1`; the Go row is the same-machine
measurement retained from the original comparison:

| Implementation | Tree-walking | Bytecode VM | VM speedup |
| --- | --- | --- | --- |
| Go 1.26.2 | 11.0 s | 3.7 s | 3.0x |
| **Taro — this implementation** | **99.7 s** | **4.34 s** | **23.0x** |

And the same program written directly in each language, with no interpreter in
the way, which is what says how much of any gap belongs to the host:

| `fibonacci(35)`, written natively | Time |
| --- | --- |
| Go 1.26.2 | 39.1 ms |
| Taro | **34 ms** |

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

Written natively, Taro edges Go out — 34 ms against 39.1 ms. The bytecode
machine is now 1.17x slower than Go's on the same program, down from 4.9x. That
remaining gap is interpreter overhead, and finding each part of it is the reason
this exists.

It started far worse. The machine took **653 s** when it was first written, 173x
Go's. Getting from there to 4.34 s took changes in Monkey, the optimizer, and the
runtime; most of the gains apply to ordinary Taro programs too.

**The safepoint poll took a global lock.** `__gc__poll` is emitted on every loop
back-edge, and its fast path compared an allocation counter against a threshold
under the GC's global mutex — a lock round-trip per iteration that also
serialised every Taro thread against one lock. The answer is published in an
atomic now.

**Every function maintained a shadow call stack.** A thread-local list of
function names was pushed and popped by every call, so that a panic could print
language-level frames. Those opaque calls also stopped LLVM inlining anything
containing them. Frames are now recovered from the native backtrace when a panic
actually happens, and the poll became an inline flag load with a cold slow path.
Per-call overhead fell from **12.5 ns to under 1 ns**.

**GC roots moved to LLVM stack maps**, off a shadow stack the runtime maintained,
which removed the per-function frame bookkeeping too. Collecting frames now
publish a site selector as well, so rootless and same-address safepoints resolve
to the executed path instead of borrowing or unioning another path's roots.

**`List` told the collector its length on every push and pop.** `__gc__set_buf_len`
resolved the buffer to a span under that same global mutex, so a push/pop pair
on any element containing a pointer paid two lock round-trips — 87 ns for what
should be a store and a bump. Buffers are now scanned to their capacity and the
owner clears a slot it vacates, so the length never has to be published at all.

Only then was the remaining cost the machine's own. It had been built on
`List.append`/`pop` and re-derived the running frame's instruction stream two or
three times per instruction. Rewriting it the way the book does — storage
reserved once and addressed by a stack pointer, `ins` and `ip` held across the
loop, operands read inside the arm that already knows the opcode — halved it
again.

**`==` heap-allocated both of its operands.** A call to an interface method
names the requirement, not the implementation — `a == b` is a call to
`PartialEq.eq`, which has no body and so no escape summary. Every such call fell
back to "the arguments escape", so both operands were promoted to the heap. The
summary for the derived `eq` existed and said the parameters were safe; nothing
looked it up, because the call named `std`'s requirement rather than the local
implementation. Resolving the callee before asking made a derived `==` go from
364 ms to 14 ms per five million comparisons, and stop allocating entirely.

**GC maps stopped prohibiting useful inlining.** A collecting callee now inlines
in MIR, before safepoints and precise roots are computed; LLVM still cannot
inline a physical function after it has acquired a collecting site. The
optimized `VM.run` body consequently has no calls to `Opcode.fromByte`,
`readUint16`, `Instructions.raw`, `VM.push`, `VM.pop`, or `ptr.add`. The fixed
growth budget deliberately leaves less-profitable calls in some opcode arms.
For a smaller signal, 20 million `List.at` reads now take a median **11.024 ms**
and the optimized loop contains no `List.at` call, versus 95 ms before.

**Allocation stopped serialising warm mutators.** Small allocations now come
from per-mutator cached spans without taking the global GC mutex. The collector
zeroes reused storage before publication, paces itself from allocation debt and
a soft memory limit, and scavenges unused pages after sweep. Precise, tag-aware
layouts also avoid retaining dead locals and inactive enum payloads. The
collector remains stop-the-world, non-moving mark-sweep; this is a faster and
more exact version of that architecture, not a generational or concurrent one.

**Generic escape analysis now follows the concrete instance.** Dictionary
lookup used to analyze abstract interface requirements, so the compiler
heapified the string key and `SipHasher13` state even though the selected string
hash implementation retains neither. Placement now runs on concrete generic
instances after inlining and lowering. The finalized `hashKey<string>` keeps
both values on the stack; doubling lookup iterations no longer increases
managed allocations. This is a compiler change only—the Monkey implementation
and Dictionary/SipHash algorithms were not altered.

| `fibonacci(35)` on the machine | Time | Gap to Go |
| --- | --- | --- |
| As first written | 653.2 s | 173x |
| Safepoint and shadow-stack removal | 87.1 s | 24x |
| `List` push/pop off the global lock | 66.6 s | 18.6x |
| Machine rewritten to match the book | 33.1 s | 8.7x |
| Interface calls resolved before escape analysis | 18.1 s | 4.9x |
| Precise GC maps, MIR inlining, and allocator caches | **4.342 s** | **1.17x** |

The evaluator went from 760.6 s to 99.7 s over the same period without changing
its architecture, because the host-level fixes benefit its much heavier
allocation workload too.

The instance-aware escape checkpoint used `fibonacci(28)` so five complete
tree-walker runs remained practical. Both compilers used the same unchanged
Monkey source, release/O2, `TARO_WORKERS=1`, and fresh processes. Pause entries
are medians of each run's runtime statistic:

| `fibonacci(28)` full two-engine run | Before | Final | Change |
| --- | ---: | ---: | ---: |
| Tree-walking median | 3.077 s | **2.299 s** | 25.3% faster |
| Bytecode VM median | 142 ms | **142 ms** | unchanged |
| Managed allocations | 18,119,598 | **6,170,942** | 65.9% fewer |
| Allocated bytes | 1,944,133,392 | **1,466,187,648** | 24.6% fewer |
| Collections | 1,894 | **1,433** | 24.3% fewer |
| GC pause p50 | 599.4 us | **492.8 us** | 17.8% lower |
| GC pause p95 | 769.7 us | **616.1 us** | 20.0% lower |
| GC pause p99 | 1,058.7 us | **895.7 us** | 15.4% lower |
| GC pause max | 5.086 ms | **5.087 ms** | unchanged |

This checkpoint does not extrapolate a new `fibonacci(35)` result. The remaining
host gaps are measured separately before choosing another optimization target.

The number worth watching through all of it is the machine's advantage over the
evaluator: **1.2x, then 1.5x, then 2.4x, and now 23.0x**, against 3.0x for Go
beside it. Removing fixed dispatch and allocation costs lets the architectural
difference show through: this VM allocates only 118 managed objects while
running `fibonacci(35)`, whereas the evaluator allocates aggressively while
rebuilding environments and values.

Not one of those fixes was visible from the language side, and three of them were
in the compiler and runtime rather than in this directory. That is what a program
like this is for: it is large enough to have a hot loop, small enough that every
nanosecond in it can be accounted for, and written against a young compiler that
had never had anything shaped like an interpreter pointed at it.

Sources: [monkey-plusplus](https://github.com/joshuanunn/monkey-plusplus),
[monkey.kt](https://github.com/MarioAriasC/monkey.kt), and Mario Arias'
[Kotlin/Go comparison](https://medium.com/@mario.arias.c/comparing-kotlin-and-go-implementations-of-the-monkey-language-ii-raiders-of-the-lost-performance-b9aa09945281).
