# Releasing

Taro ships as a self-contained SDK archive per platform:

| Archive | Runs on |
| --- | --- |
| `taro-<version>-macos-arm64.tar.gz` | Apple Silicon Macs, macOS 14 or newer |
| `taro-<version>-linux-x86_64.tar.gz` | x86-64 Linux with glibc 2.28 or newer |
| `taro-<version>-linux-arm64.tar.gz` | ARM64 Linux with glibc 2.28 or newer |

Each contains `bin/taro` (with LLVM embedded statically), `bin/taro-lsp`, the
runtime, the precompiled standard library and its sources, `LICENSE-MIT`,
`LICENSE-APACHE` and `THIRD_PARTY_NOTICES`. Users need only the system linker:
Apple's command line tools, or a C compiler (`cc`) on Linux.

## What makes an SDK portable

- **Embedded LLVM.** `build_llvm.py` builds LLVM 22.1.8 from source as static
  libraries for the AArch64 and X86 backends, without zlib, zstd, libxml2 or
  terminal dependencies. On macOS it targets the deployment floor; on Linux it
  is built inside `manylinux_2_28`, so it needs only glibc 2.28. Homebrew or
  distribution LLVM packages carry their build machine's OS floor and are not
  accepted for SDK builds.
- **Fixed targets.** The compiler targets `arm64-apple-macosx14.0` on every Mac
  and a baseline CPU per architecture, never the build machine's (see
  [Native Targets](codegen.md#native-targets)).
- **Audits.** `build_dist.py --sdk` rejects executables that load non-system
  libraries, contain library search paths, need a newer macOS than 14.0, or need
  glibc newer than 2.28 or libstdc++ newer than GCC 8's.
- **Writable state lives outside the SDK.** Package downloads go to the
  per-user cache (see [Packages](packages.md#resolution-and-locking)) and the
  language server's cache to its own, so the SDK can be installed read-only.

## Continuous integration

`.github/workflows/sdk.yml` runs on pushes to `main`, on related pull requests,
and on `v*` tags:

1. **Build** each platform: macOS on a macOS 14 runner, Linux in
   `manylinux_2_28` containers on x86-64 and ARM64 runners. LLVM is cached per
   platform until `build_llvm.py` changes; the first build takes about an hour.
2. **Test** each archive on clean machines that have only a C compiler:
   macOS 14 and 15, AlmaLinux 8 (the glibc floor), Ubuntu 22.04 and 24.04,
   Debian 12 and Fedora 42. `smoke_sdk.py` verifies the checksum, unpacks the
   archive to a path with spaces, makes it read-only, and then runs, builds,
   creates a package with `taro new`, runs its tests, checks a diagnostic that
   quotes std source, and navigates into std through `taro-lsp`.
3. **Draft a release** for a `v*` tag, attaching every archive, its `.sha256`,
   `SHA256SUMS` and `install.sh`.

## Publishing a release

1. Set the version in `compiler-cli/Cargo.toml` (it is what `taro --version`
   prints and what names the archives) and commit.
2. Push a matching tag, e.g. `git tag v0.2.0 && git push origin v0.2.0`.
3. When the workflow finishes, review the draft release on GitHub and publish
   it. The installer picks the newest release, previews included.

## Build and test an SDK locally

```sh
python3 -B development/scripts/build_llvm.py --prefix "$PWD/target/sdk-llvm/macos-arm64"
python3 -B development/scripts/build_dist.py --sdk \
  --llvm-prefix "$PWD/target/sdk-llvm/macos-arm64" --dist-dir "$PWD/target/sdk-dist/taro"
python3 -B development/scripts/package_sdk.py target/sdk-dist/taro --output-dir target/sdk-out
python3 -B development/scripts/smoke_sdk.py target/sdk-out/taro-*-macos-arm64.tar.gz
```

The LLVM build needs CMake and Ninja and takes 20–30 minutes on a recent Mac;
its build tree is removed afterwards, leaving about 1 GiB. SDK builds use
`target/sdk/` for Cargo so they do not disturb development builds. Pass
`--developer-dir /Library/Developer/CommandLineTools` to `smoke_sdk.py` to test
the Command Line Tools on a host that also has Xcode.

## Not yet covered

- macOS archives are not signed or notarized. `curl` downloads (including the
  installer) are not quarantined, but a browser download is: users must remove
  the quarantine attribute or approve it in System Settings.
- Intel Macs and Windows are not supported.
