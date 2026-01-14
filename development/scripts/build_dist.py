#!/usr/bin/env python3
import os
import subprocess
import shutil
import sys
from pathlib import Path

"""
build_dist.py

This script compiles the compiler (taro-bin) and the runtime library (taro-runtime),
and constructs a distribution directory `dist/` in the repository root.

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

def run_command(command, cwd=None):
    print(f"Running: {' '.join(command)}")
    result = subprocess.run(command, cwd=cwd, check=True)
    return result

def main():
    # Determine repo root (assuming script is in development/scripts)
    script_dir = Path(__file__).resolve().parent
    repo_root = script_dir.parent.parent
    
    dist_dir = repo_root / "dist"
    
    print(f"Repository Root: {repo_root}")
    print(f"Distribution Dir: {dist_dir}")

    # Clean dist dir
    if dist_dir.exists():
        shutil.rmtree(dist_dir)
    dist_dir.mkdir(parents=True)

    # 1. Build Runtime
    print("\n--- Building Runtime ---")
    run_command([
        "cargo", "build", 
        "-p", "taro-runtime", 
        "--release"
    ], cwd=repo_root)

    # 2. Build Compiler CLI
    print("\n--- Building Compiler CLI ---")
    run_command([
        "cargo", "build", 
        "-p", "taro-bin", 
        "--release"
    ], cwd=repo_root)

    # 3. Create Distribution Structure
    print("\n--- These files go to dist ---")
    
    # bin/taro
    bin_dir = dist_dir / "bin"
    bin_dir.mkdir()
    
    src_bin = repo_root / "target" / "release" / "taro-bin"
    dst_bin = bin_dir / "taro"
    
    print(f"Copying {src_bin} -> {dst_bin}")
    shutil.copy2(src_bin, dst_bin)

    # lib/taro/runtime/libtaro_runtime.a
    lib_dir = dist_dir / "lib" / "taro" / "runtime"
    lib_dir.mkdir(parents=True)
    
    src_lib = repo_root / "target" / "release" / "libtaro_runtime.a"
    dst_lib = lib_dir / "libtaro_runtime.a"
    
    print(f"Copying {src_lib} -> {dst_lib}")
    shutil.copy2(src_lib, dst_lib)
    
    # std
    std_src = repo_root / "std"
    std_dst = dist_dir / "std"
    print(f"Copying {std_src} -> {std_dst}")
    if std_dst.exists():
        shutil.rmtree(std_dst)
    shutil.copytree(std_src, std_dst)
    
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
