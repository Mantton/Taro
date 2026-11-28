#!/usr/bin/env python3
import argparse
import os
import re
import subprocess
import shutil
import sys
import tempfile
from pathlib import Path

import disk_guard
import third_party_notices

"""
build_dist.py

This script compiles the compiler (taro-bin) and the runtime library (taro-runtime),
and constructs a distribution directory with a sysroot-like structure.

Output Structure:
  dist/
    bin/
      taro                 (Compiler executable)
    lib/
      taro/
        runtime/
          libtaro_runtime.a (Host static runtime library)
          libtaro_runtime.a.manifest.toml
          <target-triple>/libtaro_runtime.a (Cross-target runtime library)
          <target-triple>/libtaro_runtime.a.manifest.toml
    std/                   (Standard library sources)

With --sdk, the result is a relocatable release SDK for macOS or Linux: it
also contains taro-lsp, physical std sources, license files and third-party
notices, and embeds the portable LLVM built by build_llvm.py.
"""

# Must match `MACOS_DEPLOYMENT_TARGET` in compiler/src/codegen/target.rs.
MACOS_DEPLOYMENT_TARGET = "14.0"
# Release SDKs are built in a container with this glibc (see
# .github/workflows/sdk.yml); newer symbol versions would exclude older distros.
GLIBC_FLOOR = (2, 28)
# libstdc++ of GCC 8, the system C++ runtime of the oldest supported distros.
GLIBCXX_FLOOR = (3, 4, 25)
LINUX_SYSTEM_LIBRARIES = {
    "libc.so.6", "libm.so.6", "libpthread.so.0", "libdl.so.2", "librt.so.1",
    "libgcc_s.so.1", "libstdc++.so.6", "ld-linux-x86-64.so.2", "ld-linux-aarch64.so.1",
}
LLVM_STAMP = "taro-llvm.json"


def parse_args(repo_root: Path) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build a local Taro distribution layout.")
    parser.add_argument(
        "--profile",
        choices=["debug", "release"],
        default="release",
        help="Compiler/runtime build profile (default: release).",
    )
    parser.add_argument(
        "--dist-dir",
        type=Path,
        default=repo_root / "dist",
        help="Output distribution directory (default: <repo>/dist).",
    )
    parser.add_argument(
        "--std-path",
        type=Path,
        default=repo_root / "std",
        help="Path to std sources used for dist symlink and attached-std bootstrap.",
    )
    parser.add_argument(
        "--target",
        help="Build runtime and attached std artifacts for this target triple.",
    )
    parser.add_argument(
        "--sdk",
        action="store_true",
        help="Build a relocatable native macOS or Linux release SDK including taro-lsp.",
    )
    parser.add_argument(
        "--llvm-prefix",
        type=Path,
        help="Portable LLVM installed by build_llvm.py (required with --sdk).",
    )
    return parser.parse_args()


def run_command(command: list[str], cwd: Path | None = None, env: dict[str, str] | None = None):
    print(f"Running: {' '.join(command)}")
    subprocess.run(command, cwd=cwd, env=env, check=True)


def apple_build_env(target: str | None) -> dict[str, str] | None:
    """Build Rust and C objects for the macOS floor that Taro links against.

    Without MACOSX_DEPLOYMENT_TARGET, cc-built objects (the unwind probe,
    ring) default to the SDK version, which can be newer than the minimum
    the link step passes, and every link then warns once per object.
    """
    if target is None:
        if sys.platform != "darwin":
            return None
    elif "apple-darwin" not in target and "apple-macos" not in target:
        return None
    return {**os.environ, "MACOSX_DEPLOYMENT_TARGET": MACOS_DEPLOYMENT_TARGET}


def release_flag(profile: str) -> list[str]:
    return ["--release"] if profile == "release" else []


def sdk_build_env(
    build_env: dict[str, str] | None, llvm_prefix: Path, cargo_target: Path
) -> dict[str, str]:
    env = (build_env if build_env is not None else os.environ).copy()
    env["LLVM_SYS_221_PREFIX"] = str(llvm_prefix)
    # A different LLVM must not overwrite the development build's artifacts.
    env["CARGO_TARGET_DIR"] = str(cargo_target)
    for variable in (
        "OPENSSL_NO_VENDOR",
        "AARCH64_APPLE_DARWIN_OPENSSL_NO_VENDOR",
        "X86_64_APPLE_DARWIN_OPENSSL_NO_VENDOR",
        "LIBGIT2_NO_VENDOR",
        "LIBSSH2_SYS_USE_PKG_CONFIG",
    ):
        env.pop(variable, None)
    # zlib is not part of every Linux system; build the bundled copy, whose
    # license THIRD_PARTY_NOTICES already carries.
    env["LIBZ_SYS_STATIC"] = "1"
    return env


def verify_portable_llvm(prefix: Path) -> None:
    if not (prefix / LLVM_STAMP).is_file() or not (prefix / "bin" / "llvm-config").is_file():
        raise ValueError(f"{prefix} is not an LLVM installation from build_llvm.py")


def verify_sdk_binary(binary: Path) -> None:
    if sys.platform == "darwin":
        verify_macos_linkage(binary)
        verify_macos_floor(binary)
    else:
        verify_linux_linkage(binary)


def verify_macos_floor(binary: Path) -> None:
    """The executable must load on the oldest supported macOS release."""
    commands = subprocess.check_output(["otool", "-l", str(binary)], text=True).split()
    versions = [commands[index + 1] for index, word in enumerate(commands[:-1]) if word == "minos"]
    if versions != [MACOS_DEPLOYMENT_TARGET]:
        raise ValueError(
            f"{binary.name} requires macOS {versions or 'unknown'}; expected {MACOS_DEPLOYMENT_TARGET}"
        )


def verify_linux_linkage(binary: Path, floors: bool = True) -> None:
    """An SDK executable may load only core system libraries of old glibc distros.

    `floors=False` checks only the libraries, for programs built on the host.
    """
    dynamic = subprocess.check_output(["readelf", "--dynamic", "--wide", str(binary)], text=True)
    for line in dynamic.splitlines():
        if "(RPATH)" in line or "(RUNPATH)" in line:
            raise ValueError(f"{binary.name} contains an unexpected library search path")
        if "(NEEDED)" in line:
            library = line.partition("[")[2].partition("]")[0]
            if library not in LINUX_SYSTEM_LIBRARIES:
                raise ValueError(f"{binary.name} depends on a non-system library: {library}")
    if not floors:
        return
    versions = subprocess.check_output(["readelf", "--version-info", "--wide", str(binary)], text=True)
    for family, floor in (("GLIBC", GLIBC_FLOOR), ("GLIBCXX", GLIBCXX_FLOOR)):
        for match in re.finditer(rf"Name: {family}_([0-9.]+)", versions):
            version = tuple(int(part) for part in match.group(1).split("."))
            if version > floor:
                raise ValueError(
                    f"{binary.name} requires {family}_{match.group(1)}; "
                    f"the SDK floor is {family}_{'.'.join(map(str, floor))}"
                )


def verify_macos_linkage(binary: Path) -> None:
    """An SDK executable may load only macOS-provided libraries."""
    dependencies = subprocess.check_output(["otool", "-L", str(binary)], text=True)
    for line in dependencies.splitlines()[1:]:
        dependency = line.strip().partition(" (")[0]
        if dependency and not dependency.startswith(("/usr/lib/", "/System/Library/")):
            raise ValueError(f"{binary.name} depends on a non-system library: {dependency}")
    commands = subprocess.check_output(["otool", "-l", str(binary)], text=True)
    if any(line.strip() == "cmd LC_RPATH" for line in commands.splitlines()):
        raise ValueError(f"{binary.name} contains an unexpected library search path")


def host_rust_target() -> str:
    output = subprocess.check_output(["rustc", "-vV"], text=True)
    return next(line.split(": ", 1)[1] for line in output.splitlines() if line.startswith("host: "))


def copy_std_sources(source: Path, destination: Path) -> None:
    if (source / "src").is_symlink():
        raise ValueError("SDK standard-library sources must contain regular files")
    destination.mkdir()
    shutil.copytree(source / "src", destination / "src", symlinks=True)
    shutil.copy2(source / "package.toml", destination / "package.toml", follow_symlinks=False)
    lockfile = source / "package.lock"
    if lockfile.exists() or lockfile.is_symlink():
        shutil.copy2(lockfile, destination / "package.lock", follow_symlinks=False)
    if any(path.is_symlink() for path in destination.rglob("*")):
        raise ValueError("SDK standard-library sources must contain regular files")


def validate_dist_dir(repo_root: Path, dist_dir: Path):
    if not dist_dir.is_absolute():
        raise ValueError(f"dist dir must be absolute: {dist_dir}")

    if dist_dir.is_symlink():
        raise ValueError(f"refusing to replace symlink dist directory: {dist_dir}")
    if dist_dir.exists() and not dist_dir.is_dir():
        raise ValueError(f"dist destination is not a directory: {dist_dir}")
    dist_dir = dist_dir.resolve()

    forbidden = {
        Path("/"),
        Path.home(),
        repo_root.resolve(),
        repo_root.resolve().parent,
    }
    if dist_dir in forbidden:
        raise ValueError(f"refusing to use unsafe dist dir: {dist_dir}")

    # Guard against accidental broad deletes like /tmp or /Users.
    if len(dist_dir.parts) <= 2:
        raise ValueError(f"dist dir path is too shallow and unsafe: {dist_dir}")


def main():
    # Determine repo root (assuming script is in development/scripts)
    script_dir = Path(__file__).resolve().parent
    repo_root = script_dir.parent.parent
    args = parse_args(repo_root)
    disk_guard.enforce()

    profile = args.profile
    dist_dir = args.dist_dir.absolute()
    std_src = args.std_path.resolve()
    target = args.target
    sdk = args.sdk
    if sdk and (sys.platform not in ("darwin", "linux") or profile != "release" or target):
        raise ValueError("--sdk requires a native macOS or Linux release build")
    llvm_prefix = args.llvm_prefix
    if sdk:
        if llvm_prefix is None:
            raise ValueError("--sdk requires --llvm-prefix from build_llvm.py")
        llvm_prefix = llvm_prefix.resolve()
        verify_portable_llvm(llvm_prefix)
    elif llvm_prefix is not None:
        raise ValueError("--llvm-prefix requires --sdk")
    cargo_target = repo_root / os.environ.get("CARGO_TARGET_DIR", "target/sdk" if sdk else "target")
    validate_dist_dir(repo_root, dist_dir)
    dist_dir = dist_dir.resolve()

    if std_src.is_relative_to(dist_dir):
        raise ValueError("std sources must be outside the distribution being replaced")
    if not std_src.is_dir():
        raise FileNotFoundError(f"std path does not exist: {std_src}")

    print(f"Repository Root: {repo_root}")
    print(f"Distribution Dir: {dist_dir}")
    print(f"Profile: {profile}")
    print(f"Std Path: {std_src}")
    print(f"Target: {target or 'host'}")

    # 1. Build Runtime
    print("\n--- Building Runtime ---")
    runtime_command = [
        "cargo",
        "build",
        "-p",
        "taro-runtime",
        *release_flag(profile),
    ]
    if target:
        runtime_command.extend(["--target", target])
    # Both builds share dependencies; one environment avoids rebuilding them.
    build_env = apple_build_env(target)
    if sdk:
        build_env = sdk_build_env(build_env, llvm_prefix, cargo_target)
        runtime_command.append("--locked")
    run_command(runtime_command, cwd=repo_root, env=build_env)

    # Assemble every artifact before replacing the previous distribution.
    # Keep staging and backup on the destination filesystem so publication is a rename.
    dist_dir.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=f".{dist_dir.name}-", dir=dist_dir.parent))
    previous = temporary / "previous"
    try:
        print("\n--- Building Compiler CLI ---")
        if sdk:
            run_command(
                [
                    "cargo", "build", "--release", "--locked", "-p", "taro-bin",
                    "--features", "release-sdk",
                ],
                cwd=repo_root,
                env=build_env,
            )
            print("\n--- Building Language Server ---")
            run_command(
                [
                    "cargo", "build", "--release", "--locked", "--bin", "taro-lsp",
                    "--manifest-path", str(repo_root / "taro-lsp" / "Cargo.toml"),
                ],
                cwd=repo_root,
                env=build_env,
            )
        else:
            run_command(
                ["cargo", "build", "-p", "taro-bin", *release_flag(profile)],
                cwd=repo_root,
                env=build_env,
            )
        staged_dist = temporary / "dist"
        staged_dist.mkdir()
        # 3. Create Distribution Structure
        print("\n--- These files go to dist ---")

        # bin/taro
        bin_dir = staged_dist / "bin"
        bin_dir.mkdir(exist_ok=True)

        src_bin = cargo_target / profile / "taro-bin"
        dst_bin = bin_dir / "taro"

        print(f"Copying {src_bin} -> {dst_bin}")
        shutil.copy2(src_bin, dst_bin)
        if sdk:
            lsp = bin_dir / "taro-lsp"
            shutil.copy2(cargo_target / profile / "taro-lsp", lsp)
            verify_sdk_binary(dst_bin)
            verify_sdk_binary(lsp)
            for license_file in ("LICENSE-MIT", "LICENSE-APACHE"):
                shutil.copy2(repo_root / license_file, staged_dist / license_file)
            notices = third_party_notices.render(
                repo_root, host_rust_target(), llvm_prefix / "LICENSE.TXT"
            )
            (staged_dist / "THIRD_PARTY_NOTICES").write_text(notices)

        # lib/taro/runtime[/<target-triple>]/libtaro_runtime.a
        lib_dir = staged_dist / "lib" / "taro" / "runtime"
        if target:
            lib_dir = lib_dir / target
        lib_dir.mkdir(parents=True, exist_ok=True)

        # Use the same target machine as the compiler to describe the layout.
        # The standalone frontend can read the result without loading LLVM.
        facts_command = [str(dst_bin), "target-facts", str(lib_dir / "target-facts.toml")]
        if target:
            facts_command.extend(["--target", target])
        run_command(facts_command, cwd=repo_root)

        src_lib = cargo_target
        if target:
            src_lib = src_lib / target
        src_lib = src_lib / profile / "libtaro_runtime.a"
        dst_lib = lib_dir / "libtaro_runtime.a"

        print(f"Copying {src_lib} -> {dst_lib}")
        shutil.copy2(src_lib, dst_lib)
        shutil.copy2(repo_root / "runtime" / "GO-LICENSE", lib_dir / "GO-LICENSE")

        manifest_command = [str(dst_bin), "runtime-manifest", str(dst_lib)]
        if target:
            manifest_command.extend(["--target", target])
        run_command(manifest_command, cwd=repo_root)

        std_dst = staged_dist / "std"
        if sdk:
            print(f"Copying {std_src} -> {std_dst}")
            copy_std_sources(std_src, std_dst)
        else:
            print(f"Symlinking {std_src} -> {std_dst}")
            std_dst.symlink_to(std_src, target_is_directory=True)

        # 4. Build attached std artifacts into TARO_HOME (dist)
        print("\n--- Building Attached Std Artifacts ---")
        env = os.environ.copy()
        env["TARO_HOME"] = str(staged_dist)
        bootstrap_src = staged_dist / ".std_bootstrap.tr"
        bootstrap_src.write_text(
            "func main() {\n    // std bootstrap source for attached artifact build\n}\n",
            encoding="utf-8",
        )
        bootstrap_command = [
            str(dst_bin),
            "check",
            str(bootstrap_src),
            "--std-path",
            str(std_dst if sdk else std_src),
            "--build-std",
        ]
        if target:
            bootstrap_command.extend(["--target", target])
        run_command(
            bootstrap_command,
            cwd=repo_root,
            env=env,
        )
        bootstrap_src.unlink()

        if dist_dir.exists():
            dist_dir.rename(previous)
        try:
            staged_dist.rename(dist_dir)
        except BaseException:
            if previous.exists():
                previous.rename(dist_dir)
            raise
        if previous.exists():
            shutil.rmtree(previous)
    finally:
        # A failed rollback must leave the previous distribution recoverable.
        if previous.exists():
            print(f"Previous distribution retained at {previous}", file=sys.stderr)
        else:
            shutil.rmtree(temporary)

    print("\n--- Build Complete ---")
    print(f"Distribution is ready at {dist_dir}")

if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as e:
        import traceback
        traceback.print_exc()
        print(f"\nError: Command failed with exit code {e.returncode}")
        sys.exit(1)
    except Exception as e:
        import traceback
        traceback.print_exc()
        print(f"\nError: {e}")
        sys.exit(1)
