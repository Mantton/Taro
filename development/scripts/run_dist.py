#!/usr/bin/env python3
import os
import subprocess
import sys
from pathlib import Path

"""
run_dist.py

A convenience script for development.
It rebuilds the compiler distribution (using build_dist.py) and then runs
the `taro` executable from that distribution with the provided arguments.

Usage:
    python3 development/scripts/run_dist.py <file_or_package> [args...]
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

    # 2. Prepare Command
    if len(sys.argv) < 2:
        print("Usage: python3 run_dist.py <file_or_package> [args...]")
        sys.exit(1)

    # Arguments to pass to taro run
    # The first arg to this script is the script name, so user args start at 1
    user_args = sys.argv[1:]
    
    # Construct taro command: taro run <user_args>
    # Note: user might provide 'run' themselves or just the file? 
    # The request says "run provided code". Usually that implies `taro run`.
    # Let's assume we invoke `taro run` + args.
    
    cmd = [str(taro_bin), "run"] + user_args

    # 3. environment setup
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
