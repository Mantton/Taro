# Taro language server

`taro-lsp` builds as a separate Cargo workspace with the compiler's LLVM feature disabled. The server keeps the editor's current buffers and uses one analysis process for each open workspace. The process runs disposable compiler sessions and returns owned results.

## Install

Place the executable in `bin/taro-lsp` and prepare its data in the sibling `share/taro-lsp` directory. Generate each descriptor with the matching SDK's `taro target-facts` command on that target or with the corresponding target selection. The first descriptor is the default. The server loads the resulting bundle at runtime. Use `--bundle` to select a different installation.

```sh
export CARGO_TARGET_DIR="$PWD/target"
cargo build --release --manifest-path taro-lsp/Cargo.toml
mkdir -p "$lsp_install/bin" "$lsp_install/share"
cp "$CARGO_TARGET_DIR/release/taro-lsp" "$lsp_install/bin/"
"$lsp_install/bin/taro-lsp" --prepare-bundle "$lsp_install/share/taro-lsp" "$PWD/std" "$target_descriptor"
```

The bundle contains readable standard-library sources, target descriptors and the compiler build identity. The worker keeps one byte-bounded standard-library snapshot in memory and rebuilds it when the source view or target changes. Definitions in the standard library resolve into the installed copy.

A package can select one of the installed targets and pin the standard-library digest from `bundle.toml` in its `package.toml`.

```toml
[language_server]
target = "aarch64-apple-darwin"
std_digest = "<digest from the installed bundle>"
```

The pilot reports typed analysis as unavailable when that target or source identity is missing or a project depends on an unresolved package. The `--target-facts` developer option starts bootstrap analysis with one descriptor.

## Use in VS Code

The Taro extension launches the installed server for local `.tr` documents. Set `taro.languageServer.path` in user settings when `taro-lsp` is outside the editor's executable search path. The pilot provides live diagnostics, inferred-type hover, go-to-definition and member completion after a dot.

From the checkout root, use its shared, ignored Cargo target directory.

```sh
CARGO_TARGET_DIR="$PWD/target" cargo test --manifest-path taro-lsp/Cargo.toml
```

The tests cover stdio lifecycle, unsaved inputs in the actual compiler worker, crash and hang recovery, and outdated replies arriving after new edits. The private protocol is versioned with the executable.
