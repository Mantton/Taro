#!/usr/bin/env python3
import argparse
import os
import subprocess
import shutil
import sys
import tempfile
from pathlib import Path

import disk_guard

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
"""


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
        "--macos-sdk",
        action="store_true",
        help="Build a relocatable native macOS release SDK including taro-lsp.",
    )
    parser.add_argument(
        "--static-zstd",
        type=Path,
        help="Path to libzstd.a when the release LLVM build uses zstd.",
    )
    return parser.parse_args()


def run_command(command: list[str], cwd: Path | None = None, env: dict[str, str] | None = None):
    print(f"Running: {' '.join(command)}")
    subprocess.run(command, cwd=cwd, env=env, check=True)


def apple_build_env(target: str | None) -> dict[str, str] | None:
    """Give C objects in the runtime archive the deployment target rustc uses.

    Without MACOSX_DEPLOYMENT_TARGET, cc-built objects (the unwind probe,
    ring) default to the SDK version, which can be newer than the minimum
    the link step passes, and every link then warns once per object.
    """
    if os.environ.get("MACOSX_DEPLOYMENT_TARGET"):
        return None
    if target is None:
        if sys.platform != "darwin":
            return None
    elif "apple-darwin" not in target and "apple-macos" not in target:
        return None
    command = ["rustc", "--print", "deployment-target"]
    if target:
        command.extend(["--target", target])
    output = subprocess.run(command, check=True, capture_output=True, text=True).stdout
    key, _, value = output.strip().partition("=")
    if key != "MACOSX_DEPLOYMENT_TARGET" or not value:
        raise RuntimeError(f"unexpected `rustc --print deployment-target` output: {output!r}")
    return {**os.environ, "MACOSX_DEPLOYMENT_TARGET": value}


def release_flag(profile: str) -> list[str]:
    return ["--release"] if profile == "release" else []


def sdk_build_env(build_env: dict[str, str] | None) -> dict[str, str]:
    env = (build_env if build_env is not None else os.environ).copy()
    for variable in (
        "OPENSSL_NO_VENDOR",
        "AARCH64_APPLE_DARWIN_OPENSSL_NO_VENDOR",
        "X86_64_APPLE_DARWIN_OPENSSL_NO_VENDOR",
        "LIBGIT2_NO_VENDOR",
        "LIBSSH2_SYS_USE_PKG_CONFIG",
    ):
        env.pop(variable, None)
    return env


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
    macos_sdk = args.macos_sdk
    if macos_sdk and (sys.platform != "darwin" or profile != "release" or target):
        raise ValueError("--macos-sdk requires a native macOS release build")
    zstd_archive = args.static_zstd
    if zstd_archive:
        if not macos_sdk or zstd_archive.name != "libzstd.a" or not zstd_archive.is_file():
            raise ValueError("--static-zstd requires --macos-sdk and a libzstd.a file")
        zstd_archive = zstd_archive.resolve()
    cargo_target = repo_root / os.environ.get("CARGO_TARGET_DIR", "target")
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
    if macos_sdk:
        build_env = sdk_build_env(build_env)
        runtime_command.append("--locked")
    run_command(runtime_command, cwd=repo_root, env=build_env)

    # Assemble every artifact before replacing the previous distribution.
    # Keep staging and backup on the destination filesystem so publication is a rename.
    dist_dir.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=f".{dist_dir.name}-", dir=dist_dir.parent))
    previous = temporary / "previous"
    try:
        print("\n--- Building Compiler CLI ---")
        if macos_sdk:
            command = [
                "cargo", "rustc", "--release", "--locked", "-p", "taro-bin",
                "--features", "release-sdk",
            ]
            if zstd_archive:
                # Apple's linker searches each directory for both archive and
                # dylib. Put just the archive ahead of LLVM's other search paths.
                static_libs = temporary / "static"
                static_libs.mkdir()
                shutil.copy2(zstd_archive, static_libs / "libzstd.a")
                command.extend(["--", "-L", f"native={static_libs}"])
            run_command(command, cwd=repo_root, env=build_env)
            print("\n--- Building Language Server ---")
            run_command(
                [
                    "cargo", "build", "--release", "--locked", "--bin", "taro-lsp",
                    "--manifest-path", str(repo_root / "taro-lsp" / "Cargo.toml"),
                ],
                cwd=repo_root,
                env={**build_env, "CARGO_TARGET_DIR": str(cargo_target)},
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
        if macos_sdk:
            lsp = bin_dir / "taro-lsp"
            shutil.copy2(cargo_target / profile / "taro-lsp", lsp)
            verify_macos_linkage(dst_bin)
            verify_macos_linkage(lsp)

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
        if macos_sdk:
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
            str(std_dst if macos_sdk else std_src),
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
