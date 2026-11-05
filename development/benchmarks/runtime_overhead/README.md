# Runtime overhead microbenchmarks

These single-file programs probe compiler-inserted runtime bookkeeping in
release builds. Their source workloads are:

- `inline_additions.tr`: 10 million loop iterations with no source-level call.
- `function_calls.tr`: the same loop through a one-line function.
- `string_byte_len.tr`: 10 million direct reads from a rooted string value.
- `rooted_function_calls.tr`: 10 million calls through a one-line string
  identity function followed by the same string read.
- `list_reads.tr`: 20 million reads from a one-element list.

Build each program with `taro build <file> --release -o <binary>`. Each prints
its final value, but that preserves the result rather than every source-level
operation. Inlining, constant folding, and loop simplification can remove calls
or repeated work. Inspect generated code before interpreting a timing as
per-call or per-iteration overhead, and record the optimization level used.

`atomic_counter.tr` accepts increments per writer and writer count, and checks
then prints the total. `channel_pingpong.tr` accepts round trips per pair and
pair count; every echoed value is checked before it prints the total rounds.
Build with `--release -O 3`; set `TARO_WORKERS` explicitly. Alternate old/new
binaries without builds during timing. The review follow-up results record
checksums, load, CPU time and retired instructions for these workloads.
