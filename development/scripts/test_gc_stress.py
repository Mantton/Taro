#!/usr/bin/env python3
"""Periodic focused GC gate against an already built, matching SDK.

Run after changing a root protocol or an optimization family, rather than per
story. The SDK supplies std/runtime; generated fixtures and Monkey run at O0
and O3 under forced collection. Temporary harnesses are always removed.
"""
import argparse
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dist", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, help="Override the GC fixture selection")
    parser.add_argument("--opt-level", action="append", choices=("0", "3"), help="Run only selected optimization levels (default: both)")
    parser.add_argument("--list", action="store_true", help="Print selected fixtures without running")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    fixtures = root / "language_tests/source_files"
    selected = sorted(path.relative_to(fixtures).as_posix() for path in fixtures.glob("valid/*.tr")
                      if path.name.startswith("gc_") or "// TAG: gc" in path.read_text())
    if args.manifest:
        selected = [line.strip() for line in args.manifest.read_text().splitlines()
                    if line.strip() and not line.lstrip().startswith("#")]
    if not selected:
        parser.error("no GC fixtures selected")
    if args.list:
        print("\n".join(selected))
        return
    dist = args.dist.resolve()
    env = dict(os.environ, TARO_HOME=str(dist), TARO_GC_STRESS="1")
    env.setdefault("TARO_WORKERS", "4")
    with tempfile.TemporaryDirectory(prefix="monkey-gc-gate-") as temporary:
        temp = Path(temporary)
        manifest = temp / "fixtures.txt"
        manifest.write_text("\n".join(selected) + "\n")
        for level in (args.opt_level or ("0", "3")):
            subprocess.run([sys.executable, str(root / "development/scripts/language_tests.py"),
                "--dist", str(dist), "--manifest", str(manifest), "--jobs", "1",
                "--codegen-profile", "release", "--opt-level", level, "--gc-stress"],
                cwd=root, env=env, check=True)
            for family in ("sync_tests", "atomic_tests"):
                subprocess.run([str(dist / "bin/taro"), "test",
                    str(root / ("std/src/tests/sync/" + family + ".tr")),
                    "--release", "-O", level, "-o", str(temp / (family + "-O" + level))],
                    cwd=root, env=env, check=True)
            # Deep parser/recursion tests are intentionally excluded here:
            # collecting at every poll makes them an unrelated endurance test.
            subprocess.run([str(dist / "bin/taro"), "test", str(root / "showcase/monkey"),
                "--release", "-O", level, "--filter", "gcReferencesRetainEscapingValues",
                "-o", str(temp / ("monkey-gc-O" + level))],
                cwd=root, env=env, check=True)


if __name__ == "__main__":
    main()
