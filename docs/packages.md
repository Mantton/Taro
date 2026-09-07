# Packages

Taro packages use a `package.toml` manifest, a conventional `src/` directory,
and a generated `package.lock`.

## Create a Package

`taro new` accepts a full three-segment package identifier:

```bash
taro new github.com/acme/app
taro new github.com/acme/lib --kind library
taro new github.com/acme/tool --kind both
```

Package kinds are:

- `executable`: `src/main.tr`
- `library`: `src/lib.tr`
- `both`: `src/lib.tr` and `src/main/main.tr`

## Manifest

`[package].name` must use exactly `<host>/<author>/<project>`. `kind` defaults
to `executable`. `no_std_prelude = true` disables the automatic `std.prelude`
scope for bootstrap packages such as std.

```toml
[package]
name = "github.com/acme/app"
kind = "executable"

[require]
"github.com/acme/parser" = { version = "^1.2", alias = "parser" }
"github.com/acme/local-lib" = { path = "../local-lib", alias = "local" }
```

Dependencies support inferred or explicit Git URLs, semantic-version requests,
tags, branches, commits, aliases, and root-local paths:

```toml
[require]
"github.com/acme/a" = "^1.0"
"github.com/acme/b" = { tag = "v2.1.0" }
"example.com/acme/c" = { git = "https://example.com/acme/c.git", branch = "main" }
"github.com/acme/d" = { commit = "0123456789abcdef" }
```

`version`, `tag`, `branch`, and `commit` are mutually exclusive selectors.
`path` cannot be combined with Git fields. An otherwise empty detailed Git
dependency uses the remote default branch. Semantic-version requests select
Git tags such as `1.2.3` or `v1.2.3`; the generated manifest
`[package].version` field is not used by the resolver.

## Resolution and Locking

The resolver selects one Git revision per package source that satisfies every
reachable request. Incompatible requests fail instead of installing multiple
versions of the same package source.

`package.lock` records resolved revisions, content hashes, dependency tree
hashes, and the requests satisfied by each package.

- `--locked` requires an existing up-to-date lockfile and never rewrites it.
- `--update-lock` resolves current requests and refreshes the lockfile.
- A truthy `CI` enables the same drift checks as `--locked`; unset, empty, `0`,
  `false`, and `no` disable this behavior (case-insensitively). `--update-lock`
  explicitly permits refreshing the lockfile even in CI.

Locked Git revisions are reused from the local cache and fetched only when
missing. Installed dependency contents are verified against their locked hash.

Path dependencies are allowed only in the root manifest; transitive path
dependencies are rejected.
