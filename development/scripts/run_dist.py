#!/usr/bin/env python3
import argparse
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
    python3 development/scripts/run_dist.py --test <file_or_package>

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

    parser = argparse.ArgumentParser(description="Build the local distribution and run a Taro input.")
    parser.add_argument("--test", action="store_true", help="Run package tests instead of the program.")
    parser.add_argument("input", help="Taro source file or package")
    parser.add_argument("args", nargs=argparse.REMAINDER, help="Arguments forwarded to the program")
    args = parser.parse_args()
    program_args = args.args
    if program_args and program_args[0] == "--":
        program_args = program_args[1:]
    if args.test and program_args:
        parser.error("forwarding program arguments is only supported for run, not --test")

    print(">>> Building Distribution...")
    try:
        subprocess.run([sys.executable, str(build_script)], check=True)
    except subprocess.CalledProcessError:
        print("Error: Build failed.")
        sys.exit(1)

    cmd = [str(taro_bin), "test" if args.test else "run", args.input]
    if program_args:
        cmd.append("--")
        cmd.extend(program_args)

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
