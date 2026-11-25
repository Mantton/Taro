# Taro language server

`taro-lsp` builds as a separate Cargo workspace with the compiler's LLVM feature disabled. The server keeps the editor's current buffers and uses one analysis process for each open workspace. The process runs disposable compiler sessions and returns owned results.

## Install

Install a Taro SDK, then build the language server. Place it in the SDK's `bin/` directory or on your executable search path.

```sh
export CARGO_TARGET_DIR="$PWD/target"
cargo build --release --manifest-path taro-lsp/Cargo.toml
cp "$CARGO_TARGET_DIR/release/taro-lsp" "$TARO_HOME/bin/"
```

The server selects the SDK from `--sdk <directory>`, `TARO_HOME`, its own installation directory, or the first `taro` on `PATH`, in that order. The SDK supplies `$TARO_HOME/std` and `lib/taro/runtime/target-facts.toml`. Projects can also select a target-specific descriptor installed at `lib/taro/runtime/<target>/target-facts.toml`. The SDK's std source is used for Go to Definition. Restart the server when replacing or editing the SDK.

The first SDK analysis builds std metadata with the LLVM-free frontend. The per-user cache stores one snapshot keyed by frontend identity, std digest and target facts. Later workers reuse it, including after a restart. A missing or invalid cache is rebuilt from the SDK. The snapshot payload is limited to 128 MiB, with at most one equally sized staging file. Set `TARO_LSP_CACHE_DIR` to override the cache directory or set it to an empty string to use only the worker's in-memory snapshot.

### Portable installation

For machines without an SDK, assemble a bundle and pass its path explicitly. Generate each descriptor with the matching SDK's `taro target-facts` command. The first descriptor is the default.

```sh
export CARGO_TARGET_DIR="$PWD/target"
cargo build --release --manifest-path taro-lsp/Cargo.toml
mkdir -p "$lsp_install/bin" "$lsp_install/share"
cp "$CARGO_TARGET_DIR/release/taro-lsp" "$lsp_install/bin/"
"$lsp_install/bin/taro-lsp" --prepare-bundle "$lsp_install/share/taro-lsp" "$PWD/std" "$target_descriptor"
"$lsp_install/bin/taro-lsp" --bundle "$lsp_install/share/taro-lsp"
```

The bundle contains readable standard-library sources, target descriptors and a prechecked std snapshot for each target. The manifest binds them to the compiler build identity and records their content hashes. Workers verify the sources and load the matching snapshot when starting, resetting the source view or switching targets. If the snapshot is missing or damaged, the worker rebuilds it from verified sources. The worker keeps one snapshot of at most 128 MiB in memory. Bundles can move after packaging, and std definitions resolve into the installed copy.

A package can select one of the installed targets and optionally pin its standard-library digest in `package.toml`.

```toml
[language_server]
target = "aarch64-apple-darwin"
std_digest = "<digest from the installed bundle>"
```

The pilot reports typed analysis as unavailable when that target or source identity is missing or a project depends on an unresolved package. The `--target-facts` developer option starts bootstrap analysis with one descriptor.

## Use in VS Code

The Taro extension launches the installed server for local `.tr` documents. Set `taro.languageServer.path` in user settings when `taro-lsp` is outside the editor's executable search path. Set `taro.sdk.path` to choose an SDK explicitly, or `taro.languageServer.bundle` for a portable installation. The pilot provides live diagnostics, inferred-type hover, go-to-definition and member completion after a dot.

The server registers file watchers with supporting clients. Without watch registration it refreshes disk sources on each text edit and uses a full package check. It refreshes embedded assets on the next analysis. Installed std files opened from a definition are browsable source, and replacing an installed bundle requires restarting the server.

From the checkout root, use its shared, ignored Cargo target directory.

```sh
CARGO_TARGET_DIR="$PWD/target" cargo test --manifest-path taro-lsp/Cargo.toml
```

The tests cover stdio lifecycle, unsaved inputs in the actual compiler worker, crash and hang recovery, and outdated replies arriving after new edits. The private protocol is versioned with the executable.

## Release checks

Run the measurements on an otherwise idle machine with one release build and matching bundle. The stdio trace reports how often the worker checks a selected body or the full package. The worker tries a selected-body check after an edit inside one clean function when text and scalar coordinates outside it are unchanged. Syntax or semantic errors, warnings, header changes and displaced source ranges use the full package checker. The selected-body check still prepares package declarations. The compiler example measures it separately from the closed-body path, which only reads the edited file for functions that meet its narrower rules.

```sh
export CARGO_TARGET_DIR="$PWD/target"
cargo build --release --manifest-path taro-lsp/Cargo.toml --bin taro-lsp --example profile_edits
python3 -B development/scripts/lsp_reclamation.py --bin target/release/taro-lsp --target-facts "$target_descriptor" --rss
python3 -B development/scripts/lsp_release_gate.py --bin target/release/taro-lsp --sdk "$TARO_HOME" --edits 10000 --recoveries 3
target/release/examples/profile_edits "$target_descriptor" "$scratch_directory" showcase/adex_iris "$lsp_install/share/taro-lsp"
```

Use an empty existing directory for `scratch_directory`. Set `TARO_LSP_SOAK_EDITS=10000` when running the LLVM-free compiler allocation test to check exact requested bytes and live allocation counts across the extended trace.
