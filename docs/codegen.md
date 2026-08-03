# Code Generation and Build Artifacts

Taro lowers typed source through HIR, THIR, and MIR before generating LLVM IR.
This document describes the user-visible build modes and artifact boundaries.

## Profiles and Optimization

Build profile and LLVM optimization level are independent:

- Debug builds use the fast baseline pipeline and retain overflow checks.
- Release builds use O2 and disable overflow checks by default.
- `-O0`, `-O1`, `-O2`, `-O3`, `-Os`, and `-Oz` override only LLVM's
  optimization pipeline.
- `--overflow-checks` and `--no-overflow-checks` override the language profile
  default.

LLVM owns instruction selection. On supported AArch64 targets, Taro permits
GlobalISel at O0 with per-function SelectionDAG fallback; optimized builds use
LLVM's maintained target defaults.

## Output Modes

`taro build` normally produces a linked executable. Use `--emit llvm-bc` to
stop after verified, post-optimization LLVM bitcode:

```bash
taro build examples/arithmetic.tr --release
taro build examples/arithmetic.tr --release --emit llvm-bc -o arithmetic.bc
```

Bitcode output does not require the runtime archive, a linker, or a sysroot. It
is a terminal package-scoped artifact and cannot be combined with LTO.

## Link-Time Optimization

LTO is opt-in and applies to participating Taro packages:

| Mode | Behavior |
| --- | --- |
| `--lto off` | Compile packages independently and link native objects |
| `--lto full` | Merge user-package bitcode and emit one optimized native object |
| `--lto thin` | Import across package boundaries and run parallel cached backends |

```bash
taro build my-package --release --lto full
taro build my-package --release --lto thin
```

Attached std, the Rust runtime, and other native objects remain optimization
boundaries. Taro performs LTO inside the compiler, so the platform linker does
not need an LLVM plugin matching Taro's LLVM version.

Full LTO reuses package bitcode but regenerates the whole-program native object.
ThinLTO also maintains a profile-scoped backend cache under
`target/<profile>/objects/thinlto-cache/`. `--no-incremental` bypasses package
reuse and ThinLTO cache reads without deleting existing entries.

## Incremental Compilation

Incremental reuse is enabled for `build`, `run`, `test`, and `check`. Artifacts
are profile-, target-, compiler-, option-, and source-fingerprinted.

| Path | Contents |
| --- | --- |
| `target/<profile>/metadata/` | Internal semantic metadata |
| `target/<profile>/objects/*.o` | Native package objects |
| `target/<profile>/objects/*.bc` | Package bitcode for bitcode/LTO modes |
| `target/<profile>/objects/*.lto.o` | Full-LTO output |
| `target/<profile>/objects/thinlto-*` | ThinLTO objects and cache |

Object and bitcode entries cannot satisfy one another's cache requirements.
`check` requires semantic metadata only. Final executables are relinked so the
current output path and native inputs are always honored.

Use `--no-incremental` for a cold build. `.taro_meta` is a binary internal
format, not a stable interchange format.

## Attached Standard Library

Std is an attached toolchain artifact. The compiler expects target-specific
metadata and native code under:

```text
$TARO_HOME/lib/taro/std/<target-triple>/std.taro_meta
$TARO_HOME/lib/taro/std/<target-triple>/std.o
```

It does not silently rebuild missing or incompatible std artifacts. Rebuild the
local distribution, or request an explicit source rebuild:

```bash
TARO_HOME="$PWD/dist" \
  dist/bin/taro check examples/hello.tr --std-path std --build-std
```

Attached std uses one canonical release-like configuration per target and is
shared by debug and release user builds.

## Cross-Compilation

`--target` controls LLVM output, attached std selection, runtime selection, and
linking. Runtime archives and their manifests live at:

```text
$TARO_HOME/lib/taro/runtime/libtaro_runtime.a
$TARO_HOME/lib/taro/runtime/<target-triple>/libtaro_runtime.a
```

Each archive has an adjacent `.manifest.toml` containing the runtime ABI,
target, architecture, and checksum contract. This validation also applies to
`--runtime-path` and `TARO_RUNTIME_LIB`.

Build a target-ready local distribution with:

```bash
python3 development/scripts/build_dist.py --target x86_64-apple-darwin
```

Same-OS Darwin cross-architecture links use the host SDK automatically. Linux
cross-architecture builds require a compatible `--linker` or `--sysroot`;
cross-OS Darwin/Linux builds require both.
