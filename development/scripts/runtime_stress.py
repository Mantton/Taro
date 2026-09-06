#!/usr/bin/env python3
import argparse
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def format_command(command: list[str]) -> str:
    return " ".join(shlex.quote(part) for part in command)


def run_command(command: list[str], cwd: Path, env: dict[str, str] | None = None) -> None:
    rendered = format_command(command)
    workers = None if env is None else env.get("TARO_WORKERS")
    suffix = "" if workers is None else f" TARO_WORKERS={workers}"
    print(f"Running: {rendered}{suffix}")
    subprocess.run(command, cwd=str(cwd), env=env, check=True)


def parse_workers(raw: str) -> list[str | None]:
    workers: list[str | None] = []
    for part in raw.split(","):
        value = part.strip()
        if not value:
            continue
        if value.lower() in {"default", "none"}:
            workers.append(None)
            continue
        parsed = int(value)
        if parsed < 1:
            raise argparse.ArgumentTypeError("--workers values must be >= 1")
        workers.append(str(parsed))
    if not workers:
        raise argparse.ArgumentTypeError("--workers must include at least one value")
    return workers


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(line_buffering=True)
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(line_buffering=True)

    parser = argparse.ArgumentParser(
        description="Run runtime-tagged std stress tests across executor worker counts."
    )
    profile = parser.add_mutually_exclusive_group()
    profile.add_argument(
        "--release",
        dest="release",
        action="store_true",
        default=True,
        help="Build and run with release binaries (default).",
    )
    profile.add_argument(
        "--debug",
        dest="release",
        action="store_false",
        help="Build and run with debug binaries.",
    )
    parser.add_argument(
        "--workers",
        type=parse_workers,
        default="1,2,4,default",
        help="Comma-separated TARO_WORKERS values. Use 'default' for no override.",
    )
    parser.add_argument(
        "--keep-temp",
        action="store_true",
        help="Keep the temporary dist directory after the run.",
    )
    args = parser.parse_args()

    script_dir = Path(__file__).resolve().parent
    repo_root = script_dir.parent.parent
    build_script = script_dir / "build_dist.py"
    temp_dir = Path(tempfile.mkdtemp(prefix="taro_runtime_stress_"))
    dist_dir = temp_dir / "dist"
    profile_name = "release" if args.release else "debug"

    try:
        run_command(
            [
                sys.executable,
                str(build_script),
                "--profile",
                profile_name,
                "--dist-dir",
                str(dist_dir),
                "--std-path",
                str(repo_root / "std"),
            ],
            cwd=repo_root,
        )

        taro = dist_dir / "bin" / "taro"
        std_path = dist_dir / "std"
        if not taro.exists():
            print(f"error: compiler binary not found at {taro}")
            return 1

        regression_root = repo_root / "language_tests/source_files/valid"
        cases = [
            (Path("std"), "test", ["--tag", "runtime"], False),
            (regression_root / "gc_stack_map_stress.tr", "run", [], True),
            (regression_root / "gc_precise_liveness.tr", "run", [], True),
        ]
        binary_dir = temp_dir / "bin"
        binary_dir.mkdir()
        for worker_index, worker_count in enumerate(args.workers):
            worker_env = os.environ.copy()
            worker_env["TARO_HOME"] = str(dist_dir)
            if worker_count is None:
                worker_env.pop("TARO_WORKERS", None)
            else:
                worker_env["TARO_WORKERS"] = worker_count

            for source, subcommand, selection, gc_stress in cases:
                binary = binary_dir / source.stem
                env = worker_env.copy()
                if gc_stress:
                    env["TARO_GC_STRESS"] = "1"
                # `taro test` always executes after compilation; its selected
                # cases are baked into the harness. Compile and run each case
                # for the first worker, then reuse that executable unchanged.
                command = [str(binary)]
                if worker_index == 0:
                    command = [
                        str(taro), subcommand, str(source),
                        "--std-path", str(std_path), "-o", str(binary),
                        *selection, *(["--release"] if args.release else []),
                    ]
                run_command(command, cwd=repo_root, env=env)
                if not binary.is_file():
                    raise RuntimeError(f"compiler did not produce executable: {binary}")
    except subprocess.CalledProcessError as error:
        return error.returncode or 1
    except RuntimeError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    finally:
        if args.keep_temp:
            print(f"Kept temp directory: {temp_dir}")
        else:
            shutil.rmtree(temp_dir, ignore_errors=True)

    print("Runtime stress tests passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
