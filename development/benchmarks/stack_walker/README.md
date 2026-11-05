# LLVM frame-recipe diagnostics

`frame_rules_probe.py` inspects LLVM stack maps, unwind data and machine code
without changing Taro's compiler or runtime. Its fixed, large, realigned and
dynamic frame fixtures exercise caller-recovery assumptions across the target
combinations defined in the script. These are code-generation probes, not a
collector implementation or a performance benchmark.

Put LLVM 22's `llc`, `llvm-readobj`, `llvm-dwarfdump` and `llvm-objdump` on PATH.
Run from the repository root, writing output only to ignored storage:

```sh
mkdir -p target/frame-rules
python3 development/benchmarks/stack_walker/frame_rules_probe.py --output target/frame-rules/recipes.json
```

Optional repeated `--object /absolute/path/to/program.o` arguments audit ARM64
Mach-O objects and their adjacent `.pcmeta.o` sidecars. Temporary fixture objects
are deleted on exit; the local report includes IR, assembly, stack maps and
unwind data. Do not commit reports or compiled objects.

Root locations and physical caller recovery are separate contracts. A saved
frame pointer can skip a frameless witness thunk; bounds checks alone do not
make that traversal safe. The production reader retains native unwinding.
The rejected frame-chain replacement and its one-off bookkeeping experiment
are not part of this benchmark harness.
