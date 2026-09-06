#!/usr/bin/env python3
import argparse
import os
import subprocess
import shutil
import sys
import tempfile
from pathlib import Path

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
    return parser.parse_args()


def run_command(command: list[str], cwd: Path | None = None, env: dict[str, str] | None = None):
    print(f"Running: {' '.join(command)}")
    subprocess.run(command, cwd=cwd, env=env, check=True)


def release_flag(profile: str) -> list[str]:
    return ["--release"] if profile == "release" else []


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

    profile = args.profile
    dist_dir = args.dist_dir.absolute()
    std_src = args.std_path.resolve()
    target = args.target
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
    run_command(runtime_command, cwd=repo_root)

    # 2. Build Compiler CLI
    print("\n--- Building Compiler CLI ---")
    run_command(
        [
            "cargo",
            "build",
            "-p",
            "taro-bin",
            *release_flag(profile),
        ],
        cwd=repo_root,
    )

    # Assemble every artifact before replacing the previous distribution.
    # Keep staging and backup on the destination filesystem so publication is a rename.
    dist_dir.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=f".{dist_dir.name}-", dir=dist_dir.parent))
    previous = temporary / "previous"
    try:
        staged_dist = temporary / "dist"
        staged_dist.mkdir()
        # 3. Create Distribution Structure
        print("\n--- These files go to dist ---")

        # bin/taro
        bin_dir = staged_dist / "bin"
        bin_dir.mkdir(exist_ok=True)

        src_bin = repo_root / "target" / profile / "taro-bin"
        dst_bin = bin_dir / "taro"

        print(f"Copying {src_bin} -> {dst_bin}")
        shutil.copy2(src_bin, dst_bin)

        # lib/taro/runtime[/<target-triple>]/libtaro_runtime.a
        lib_dir = staged_dist / "lib" / "taro" / "runtime"
        if target:
            lib_dir = lib_dir / target
        lib_dir.mkdir(parents=True, exist_ok=True)

        src_lib = repo_root / "target"
        if target:
            src_lib = src_lib / target
        src_lib = src_lib / profile / "libtaro_runtime.a"
        dst_lib = lib_dir / "libtaro_runtime.a"

        print(f"Copying {src_lib} -> {dst_lib}")
        shutil.copy2(src_lib, dst_lib)

        manifest_command = [str(dst_bin), "runtime-manifest", str(dst_lib)]
        if target:
            manifest_command.extend(["--target", target])
        run_command(manifest_command, cwd=repo_root)

        # std - symlink instead of copy for development
        std_dst = staged_dist / "std"
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
            str(std_src),
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
