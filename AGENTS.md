# Agents

## Testing

- For compiler changes, run the full compiler, language, and standard library test suites before finishing.
- For bug fixes, add focused regression tests that fail on `HEAD` and pass with the proposed changes.
- When practical, compare and document the observed behavior on `HEAD` versus the changed code so the regression test validates the actual bug, not just the intended implementation.

## Disk budget

- The checkout plus Taro temp caches must stay below 15 GiB. `development/scripts/disk_guard.py`
  enforces this; the build/test scripts and `make` build targets run it automatically.
- Run `make disk-usage` to inspect and `make disk-guard` to prune after raw `cargo` builds.
- Build validation SDKs in a temporary directory and delete them afterwards
  (`test_all.py --disposable-dist`); never leave SDK copies, logs or binaries under `tmp/`.

## Generated results

- Keep generated benchmark results, profiling data, raw samples, experiment ledgers,
  logs and disassembly dumps out of Git. Use an ignored `target/` directory,
  ignored `development/benchmarks/results/`, or an OS temporary directory, within
  the disk budget above.
- Before generating output inside the checkout, verify its destination with
  `git check-ignore -q <output-path>`. If it is not ignored, choose an ignored
  location or add a narrow ignore rule first. Do not force-add generated results
  or update existing tracked result archives.
- Commit reproducible benchmark/test programs, inputs and concise methodology.
  Do not embed generated result datasets or historical timing tables in READMEs
  or other tracked documents. Intentional test fixtures and diagnostic snapshots
  remain test assets and may be committed.

## Commits

- Use Conventional Commits for commit messages.
- Format commit subjects as `type(scope): imperative summary`.
- Prefer scopes that match the touched subsystem, such as `codegen`, `compiler`, `mir`, `runtime`, or `std`.
- Example: `fix(codegen): skip library packages before link validation`.
