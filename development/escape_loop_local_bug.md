# Escaping loop-local shares one heap cell

## Symptom

A `let` inside a loop whose reference escapes is promoted to a **single** heap
cell for the whole function, so every iteration overwrites the previous one.
Building a linked structure in a loop therefore produces a self-referential
node instead of a chain.

```taro
struct Node {
    value: int64
    next: Optional[&Node]
}

func main() {
    var head: Optional[&Node] = .none
    var i = 0 as int64
    while i < 4 {
        let node = Node { value: i, next: head }
        head = .some(&node)
        i += 1
    }
    // Walks forever, and every value reads 3.
}
```

Expected: a 4-node chain, values 3, 2, 1, 0. Actual: one node whose `next`
points at itself, so a walk never terminates.

## Cause

`ApplyEscapeAnalysis` (`compiler/src/mir/optimize/escape.rs`) heapifies an
escaping local by changing its type to `&mut T` and splicing a single
`Rvalue::Alloc` into the **entry block**:

```rust
if !allocs.is_empty() || !param_inits.is_empty() {
    let entry = body.start_block;
    let statements = &mut body.basic_blocks[entry].statements;
    statements.splice(0..0, insertions);
}
```

The MIR for the example above:

```
bb0:  %8 = alloc Node;      // once, for the whole function
bb2:  *%8 = move %5;        // every iteration writes the same cell
      %10 = &*%8;           // every reference names that one cell
```

On the second iteration `%5.1` holds `&*%8`, so `(*%8).next` becomes `&*%8`.

`rewrite_fresh_heapified_initializations` does not help: it decides "first
write" from a may-assigned dataflow, and a loop body's back edge puts the local
in the may-assigned set on entry, so writes after the first iteration are not
treated as initialisations.

## Why the obvious fix is wrong

Allocating before every full overwrite of `*heap` would break mutation through
an existing reference:

```taro
var x = 1
let r = &x
x = 2
// `*r` must read 2; a fresh cell at `x = 2` would leave `r` on the old one.
```

So the pass has to tell "this write starts a new binding" from "this write
mutates the binding that is already there". MIR carries no such distinction —
there is no `StorageLive`, and the `mutable` flag does not survive as a
reliable let/var signal (`node` above lowers to `%mut 8`).

## Fix requires a design decision

Either:

1. Give MIR a storage-liveness marker and allocate at each `StorageLive` for a
   heapified local, or
2. Have HIR→MIR lowering emit the allocation at the declaration point rather
   than letting the escape pass hoist it to the entry block.

Both are larger than a local patch to the pass, which is why this is written
down rather than fixed in place.

## Scope

Pre-existing; unrelated to the safepoint-poll change in the same session. The
Monkey showcase does not hit it — its `box*` helpers are called once per
function invocation, so each gets its own entry-block allocation.

## Repro file and expected output

`development/escape_loop_local_repro.tr` holds a runnable repro. It is kept out
of `language_tests/` for now: it fails today, the harness
(`development/scripts/language_tests.py`) has no expected-failure directive, and
a normal `taro run` test has no timeout — so a hanging test would wedge the
whole suite rather than report a failure. The walk in the repro is bounded for
the same reason.

Today it prints:

```
step 0 value 3
step 1 value 3
step 2 value 3
step 3 value 3
step 4 value 3
step 5 value 3
step 6 value 3
step 7 value 3
step 8 value 3
step 9 value 3
alias sees 2
counter is 3
```

After the fix it must print:

```
step 0 value 3
step 1 value 2
step 2 value 1
step 3 value 0
end after 4 steps
alias sees 2
counter is 3
```

Note the last two lines are **already correct today**. They are the guard rail:
allocating a fresh cell on every write to a heapified local would break them,
stranding `alias` on stale data. Any fix has to keep them passing.

Move the file to `language_tests/source_files/valid/escape_loop_local.tr` with
that expected output in `language_tests/outputs/valid/escape_loop_local.out` as
part of the fix, so it lands green.
