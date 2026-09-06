# Editor integrations

The integrations provide syntax highlighting and static editing support. Use
`taro check` for compiler diagnostics.

## VS Code

Open `editors/vscode` as a workspace and launch **Run Extension** from the debug
panel. The extension uses its TextMate grammar and has no build dependencies.

## Tree-sitter and Zed

The canonical Tree-sitter grammar is in `tree-sitter-taro`. Install its locked
development dependency and run the parser and editor-query checks:

```sh
cd tree-sitter-taro
npm ci
npm test
```

Generated parser sources remain ignored. The package is a grammar development
tool, with no Node native bindings.

Zed requires generated C sources in a grammar checkout. Prepare a local dev
extension from the current grammar and queries:

```sh
npm run prepare:zed
```

In Zed, run **Install Dev Extension** and select `tmp/zed-extension` at the
repository root. Rerun the preparation command and rebuild the dev extension
after changing the grammar or queries. The generated extension uses a local
checkout of this repository; no separate grammar mirror is required. The
tracked `editors/zed` directory is the source template, not the installation
folder.

The Tree-sitter grammar is an approximation for editor use, not the compiler's
parser. Some supported language constructs still require grammar coverage.
