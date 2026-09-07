# Release Checklist

Use this checklist for compiler or language releases. Run commands from the
repository root.

## Code and tests

- [ ] Format Rust sources with `cargo fmt --all -- --check`.
- [ ] Run the complete compiler, distribution, standard-library, and language
      test pipeline with `make all-tests` (or
      `python3 development/scripts/test_all.py`). This uses debug Rust tests, a
      release compiler/runtime, debug std tests, and both generated-language
      profiles; it is not the full compiler-profile matrix.
- [ ] Run `cargo test --workspace --release` and the language suite with a
      debug compiler/runtime:
      `python3 development/scripts/language_tests.py --debug --codegen-profile both`.
- [ ] Run `TARO_HOME="$PWD/dist" dist/bin/taro test std --release` for release
      standard-library tests.
- [ ] Run `make runtime-stress` when runtime, async scheduling, GC, or generated
      runtime calls changed; also run
      `python3 development/scripts/runtime_stress.py --debug` for its debug
      compiler/runtime and generated-program configuration.
- [ ] Add a focused regression test for every bug fix. Prefer a test that fails
      on the parent commit and passes with the fix.
- [ ] Confirm `git diff --check` reports no whitespace errors.

## Language and compatibility

- [ ] Update `README.md`, `docs/GRAMMAR.md`, and the syntax guide for changed
      syntax, semantics, keywords, or feature status.
- [ ] Add or update positive and negative language fixtures, including exact
      diagnostic snapshots where applicable.
- [ ] Include cross-package coverage when a feature affects public signatures,
      metadata, default providers, generic instantiation, or linking.
- [ ] Bump `META_FORMAT_VERSION` whenever serialized compiler metadata or its
      standard-item mapping changes. Rebuild `dist/` so attached standard-library
      metadata matches the compiler.
- [ ] Verify corrupt caches fail safely and incompatible metadata is invalidated.
- [ ] Search the docs for stale `deferred`, `not yet implemented`, and
      `reserved for future` claims when enabling a feature.

## Packaging

- [ ] Build both debug and release distributions for each supported release
      target.
- [ ] Smoke-test `taro check`, `taro build`, `taro run`, and `taro test` with the
      packaged toolchain layout and inferred `TARO_HOME`.
- [ ] Confirm attached standard-library artifacts exist under
      `lib/taro/std/<target-triple>/` and were produced by the release compiler.
- [ ] Confirm every `libtaro_runtime.a` has an adjacent `.manifest.toml` sidecar
      and that host and cross-target smoke builds reject swapped archives.
- [ ] Review version numbers, release notes, and known limitations before
      publishing artifacts.
