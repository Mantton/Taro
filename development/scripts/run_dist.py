#!/usr/bin/env python3
import os
import subprocess
import sys
from pathlib import Path

"""
run_dist.py

A convenience script for development.
It rebuilds the compiler distribution (using build_dist.py) and then runs
or tests the `taro` executable from that distribution with the provided arguments.

Usage:
    python3 development/scripts/run_dist.py <file_or_package> [args...]
    python3 development/scripts/run_dist.py --test <file_or_package> [args...]

Flags:
    --test   Run `taro test` instead of `taro run`.
"""


def main():
    # Determine paths
    script_dir = Path(__file__).resolve().parent
    repo_root = script_dir.parent.parent
    build_script = script_dir / "build_dist.py"
    dist_dir = repo_root / "dist"
    taro_bin = dist_dir / "bin" / "taro"

    # 1. Build Distribution
    print(">>> Building Distribution...")
    try:
        subprocess.run([sys.executable, str(build_script)], check=True)
    except subprocess.CalledProcessError:
        print("Error: Build failed.")
        sys.exit(1)

    # 2. Parse arguments — strip our own --test flag before forwarding the rest
    raw_args = sys.argv[1:]

    use_test = False
    if "--test" in raw_args:
        use_test = True
        raw_args = [a for a in raw_args if a != "--test"]

    if not raw_args:
        print("Usage: python3 run_dist.py [--test] <file_or_package> [args...]")
        sys.exit(1)

    # 3. Construct taro command
    taro_subcommand = "test" if use_test else "run"
    cmd = [str(taro_bin), taro_subcommand] + raw_args

    # 4. Environment setup
    env = os.environ.copy()
    env["TARO_HOME"] = str(dist_dir)

    print(f">>> Running: {' '.join(cmd)}")
    print("-" * 40)

    try:
        subprocess.run(cmd, env=env, check=True)
    except subprocess.CalledProcessError as e:
        sys.exit(e.returncode)
    except KeyboardInterrupt:
        sys.exit(130)


if __name__ == "__main__":
    main()
