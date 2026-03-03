#!/usr/bin/env python3
import argparse
import os
import subprocess
import shutil
import sys
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
          libtaro_runtime.a (Static runtime library)
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
    return parser.parse_args()


def run_command(command: list[str], cwd: Path | None = None, env: dict[str, str] | None = None):
    print(f"Running: {' '.join(command)}")
    result = subprocess.run(command, cwd=cwd, env=env, check=True)
    return result


def release_flag(profile: str) -> list[str]:
    return ["--release"] if profile == "release" else []


def validate_dist_dir(repo_root: Path, dist_dir: Path):
    if not dist_dir.is_absolute():
        raise ValueError(f"dist dir must be absolute: {dist_dir}")

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
    dist_dir = args.dist_dir.resolve()
    std_src = args.std_path.resolve()
    validate_dist_dir(repo_root, dist_dir)

    if not std_src.exists():
        raise FileNotFoundError(f"std path does not exist: {std_src}")

    print(f"Repository Root: {repo_root}")
    print(f"Distribution Dir: {dist_dir}")
    print(f"Profile: {profile}")
    print(f"Std Path: {std_src}")

    # Clean dist dir
    if dist_dir.exists():
        if dist_dir.is_symlink():
            raise RuntimeError(
                f"refusing to remove symlink dist directory: {dist_dir}"
            )
        shutil.rmtree(dist_dir)
    dist_dir.mkdir(parents=True)

    # 1. Build Runtime
    print("\n--- Building Runtime ---")
    run_command([
        "cargo", "build", 
        "-p", "taro-runtime", 
        *release_flag(profile),
    ], cwd=repo_root)

    # 2. Build Compiler CLI
    print("\n--- Building Compiler CLI ---")
    run_command([
        "cargo", "build", 
        "-p", "taro-bin", 
        *release_flag(profile),
    ], cwd=repo_root)

    # 3. Create Distribution Structure
    print("\n--- These files go to dist ---")
    
    # bin/taro
    bin_dir = dist_dir / "bin"
    bin_dir.mkdir()
    
    src_bin = repo_root / "target" / profile / "taro-bin"
    dst_bin = bin_dir / "taro"
    
    print(f"Copying {src_bin} -> {dst_bin}")
    shutil.copy2(src_bin, dst_bin)

    # lib/taro/runtime/libtaro_runtime.a
    lib_dir = dist_dir / "lib" / "taro" / "runtime"
    lib_dir.mkdir(parents=True)
    
    src_lib = repo_root / "target" / profile / "libtaro_runtime.a"
    dst_lib = lib_dir / "libtaro_runtime.a"
    
    print(f"Copying {src_lib} -> {dst_lib}")
    shutil.copy2(src_lib, dst_lib)
    
    # std - symlink instead of copy for development
    std_dst = dist_dir / "std"
    print(f"Symlinking {std_src} -> {std_dst}")
    if std_dst.exists():
        std_dst.unlink() if std_dst.is_symlink() else shutil.rmtree(std_dst)
    std_dst.symlink_to(std_src, target_is_directory=True)

    # 4. Build attached std artifacts into TARO_HOME (dist)
    print("\n--- Building Attached Std Artifacts ---")
    env = os.environ.copy()
    env["TARO_HOME"] = str(dist_dir)
    bootstrap_src = dist_dir / ".std_bootstrap.tr"
    bootstrap_src.write_text(
        "func main() {\n    // std bootstrap source for attached artifact build\n}\n",
        encoding="utf-8",
    )
    try:
        run_command(
            [
                str(dst_bin),
                "check",
                str(bootstrap_src),
                "--std-path",
                str(std_src),
                "--build-std",
            ],
            cwd=repo_root,
            env=env,
        )
    finally:
        bootstrap_src.unlink(missing_ok=True)

    print("\n--- Build Complete ---")
    print(f"Distribution is ready at {dist_dir}")

if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as e:
        print(f"\nError: Command failed with exit code {e.returncode}")
        sys.exit(1)
    except Exception as e:
        print(f"\nError: {e}")
        sys.exit(1)
