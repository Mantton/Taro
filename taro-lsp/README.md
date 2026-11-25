# Taro language server

`taro-lsp` builds as a separate Cargo workspace with the compiler's LLVM feature disabled. The server keeps the editor's current buffers and uses one analysis process for each open workspace. The process runs disposable compiler sessions and returns owned results.

For a developer smoke test, generate a target descriptor with `taro target-facts`, then run the server with `taro-lsp --target-facts /path/to/target-facts.toml`. This starts stdio LSP transport with bootstrap analysis. The descriptor selects the target semantics for the compiler running in the worker.

From the checkout root, use its shared, ignored Cargo target directory.

```sh
CARGO_TARGET_DIR="$PWD/target" cargo test --manifest-path taro-lsp/Cargo.toml
```

The tests cover stdio lifecycle, unsaved inputs in the actual compiler worker, crash and hang recovery, and outdated replies arriving after new edits. The private protocol is versioned with the executable.
