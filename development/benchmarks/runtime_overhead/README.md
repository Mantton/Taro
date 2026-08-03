# Runtime overhead microbenchmarks

These single-file programs isolate the steady-state cost of compiler-inserted
runtime bookkeeping in release builds:

- `inline_additions.tr`: 10 million loop iterations with no source-level call.
- `function_calls.tr`: the same loop through a one-line function.
- `string_byte_len.tr`: 10 million direct reads from a rooted string value.
- `rooted_function_calls.tr`: 10 million calls through a one-line function
  around the same string read, isolating managed shadow-frame call overhead.
- `list_reads.tr`: 20 million reads from a one-element list.

Build each program with `taro build <file> --release -o <binary>`. Print the
final value so the optimizer must preserve the computation.
