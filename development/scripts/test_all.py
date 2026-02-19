#!/usr/bin/env python3
import argparse
import os
import shlex
import subprocess
import sys
from pathlib import Path


def positive_int(value: str) -> int:
    try:
        parsed = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"invalid int value: {value}") from error
    if parsed < 1:
        raise argparse.ArgumentTypeError("--jobs must be >= 1")
    return parsed


def format_command(command: list[str]) -> str:
    return " ".join(shlex.quote(part) for part in command)


def run_command(command: list[str], cwd: Path, env: dict[str, str] | None = None) -> None:
    print(f"Running: {format_command(command)}")
    subprocess.run(command, cwd=str(cwd), env=env, check=True)


def print_stage(index: int, total: int, name: str) -> None:
    print()
    print(f"[{index}/{total}] {name}")


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(line_buffering=True)
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(line_buffering=True)

    parser = argparse.ArgumentParser(description="Run all Taro development checks.")
    parser.add_argument("--jobs", type=positive_int, help="Forwarded to language_tests.py")
    parser.add_argument("--skip-cargo-tests", action="store_true")
    parser.add_argument("--skip-build-dist", action="store_true")
    parser.add_argument("--skip-compile-std", action="store_true")
    parser.add_argument("--skip-std-package-tests", action="store_true")
    parser.add_argument("--skip-language-tests", action="store_true")
    args = parser.parse_args()

    script_dir = Path(__file__).resolve().parent
    repo_root = script_dir.parent.parent
    build_script = repo_root / "development" / "scripts" / "build_dist.py"
    language_tests_script = repo_root / "development" / "scripts" / "language_tests.py"
    dist_dir = repo_root / "dist"
    taro_bin = dist_dir / "bin" / "taro"
    std_path = repo_root / "std"
    hello_example = repo_root / "examples" / "hello.tr"
    std_tests_root = repo_root / "std" / "src" / "tests"

    stage_count = 5
    current_stage = "startup"

    try:
        current_stage = "cargo tests"
        print_stage(1, stage_count, "Cargo tests")
        if args.skip_cargo_tests:
            print("SKIPPED: disabled via --skip-cargo-tests")
        else:
            run_command(["cargo", "test", "--workspace"], cwd=repo_root)

        current_stage = "build dist"
        print_stage(2, stage_count, "Build dist")
        if args.skip_build_dist:
            print("SKIPPED: disabled via --skip-build-dist")
        else:
            run_command(["python3", str(build_script)], cwd=repo_root)

        current_stage = "compile std smoke"
        print_stage(3, stage_count, "Compile std smoke")
        if args.skip_compile_std:
            print("SKIPPED: disabled via --skip-compile-std")
        else:
            if not taro_bin.exists():
                print(
                    f"error: compiler binary not found at {taro_bin}; run without --skip-build-dist first"
                )
                return 1

            env = os.environ.copy()
            env["TARO_HOME"] = str(dist_dir)
            run_command(
                [
                    str(taro_bin),
                    "check",
                    str(hello_example),
                    "--std-path",
                    str(std_path),
                ],
                cwd=repo_root,
                env=env,
            )

        current_stage = "std package tests"
        print_stage(4, stage_count, "Std package tests")
        if args.skip_std_package_tests:
            print("SKIPPED: disabled via --skip-std-package-tests")
        else:
            if not taro_bin.exists():
                print(
                    f"error: compiler binary not found at {taro_bin}; run without --skip-build-dist first"
                )
                return 1

            if not std_tests_root.exists():
                print(
                    f"SKIPPED: std package tests directory not found at {std_tests_root}"
                )
            else:
                test_files = sorted(
                    path for path in std_tests_root.rglob("*.tr") if path.is_file()
                )
                if not test_files:
                    print(
                        f"SKIPPED: no std package test files found under {std_tests_root}"
                    )
                else:
                    env = os.environ.copy()
                    env["TARO_HOME"] = str(dist_dir)
                    print(f"Discovered {len(test_files)} std package test file(s)")
                    for test_file in test_files:
                        run_command(
                            [
                                str(taro_bin),
                                "test",
                                str(test_file),
                                "--std-path",
                                str(std_path),
                            ],
                            cwd=repo_root,
                            env=env,
                        )

        current_stage = "language tests"
        print_stage(5, stage_count, "Language tests")
        if args.skip_language_tests:
            print("SKIPPED: disabled via --skip-language-tests")
        else:
            command = ["python3", str(language_tests_script)]
            if args.jobs is not None:
                command.extend(["--jobs", str(args.jobs)])
            run_command(command, cwd=repo_root)

    except subprocess.CalledProcessError as error:
        print()
        print(
            f"error: stage '{current_stage}' failed with exit code {error.returncode}"
        )
        return error.returncode or 1
    except KeyboardInterrupt:
        print()
        print("Interrupted")
        return 130

    print()
    print("All enabled stages passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
