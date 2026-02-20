#!/usr/bin/env python3
import argparse
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
STD_PATH_DEFAULT = PROJECT_ROOT / "std"
TARO_BIN_NAME = "taro-bin"

HEADER_RE = re.compile(r"^Timings – (?P<package>.+) \((?P<mode>.+)\)$")
ROW_RE = re.compile(r"^\s{2}(?P<phase>.+?)\s+(?P<ms>\d+\.\d+)\s+ms$")


@dataclass(frozen=True)
class ProfileEnvironment:
    profile: str
    compiler: Path
    taro_home: Path


def parse_args() -> tuple[argparse.Namespace, list[str]]:
    parser = argparse.ArgumentParser(
        description=(
            "Benchmark compiler timings for an input file/package using debug and release profiles."
        )
    )
    parser.add_argument("input", help="Input file or package path to compile")
    parser.add_argument(
        "--command",
        choices=["run", "check", "build", "test"],
        default="check",
        help="Compiler command to benchmark (default: check)",
    )
    parser.add_argument(
        "--runs",
        type=int,
        default=5,
        help="Number of runs per profile (default: 5)",
    )
    parser.add_argument(
        "--std-path",
        default=str(STD_PATH_DEFAULT),
        help=f"Path to std package (default: {STD_PATH_DEFAULT})",
    )
    parser.add_argument(
        "--package",
        action="append",
        default=[],
        help=(
            "Optional package filter for detailed table. Can be passed multiple times. "
            "Defaults to std if present."
        ),
    )
    args, extra = parser.parse_known_args()
    if extra and extra[0] == "--":
        extra = extra[1:]
    if args.runs <= 0:
        parser.error("--runs must be >= 1")
    return args, extra


def build_profile(profile: str):
    print(f"Building compiler/runtime ({profile})...")
    cmd = ["cargo", "build", "-p", "taro-bin", "-p", "taro-runtime"]
    if profile == "release":
        cmd.append("--release")
    result = subprocess.run(
        cmd,
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(result.stdout)
        print(result.stderr, file=sys.stderr)
        raise RuntimeError(f"build failed for profile={profile}")


def setup_profile_env(profile: str, temp_root: Path) -> ProfileEnvironment:
    compiler = PROJECT_ROOT / "target" / profile / TARO_BIN_NAME
    runtime_src = PROJECT_ROOT / "target" / profile / "libtaro_runtime.a"
    taro_home = temp_root / profile / "taro_home"
    taro_home_lib = taro_home / "lib"
    taro_home_lib.mkdir(parents=True, exist_ok=True)
    shutil.copy2(runtime_src, taro_home_lib / "libtaro_runtime.a")
    return ProfileEnvironment(profile=profile, compiler=compiler, taro_home=taro_home)


def parse_timings(output: str) -> dict[tuple[str, str, str], float]:
    parsed: dict[tuple[str, str, str], float] = {}
    current_package: str | None = None
    current_mode: str | None = None

    for raw_line in output.splitlines():
        line = raw_line.rstrip()
        header_match = HEADER_RE.match(line)
        if header_match:
            current_package = header_match.group("package").strip()
            current_mode = header_match.group("mode").strip()
            continue

        if current_package is None or current_mode is None:
            continue

        row_match = ROW_RE.match(line)
        if not row_match:
            continue

        phase = row_match.group("phase").strip()
        ms = float(row_match.group("ms"))
        parsed[(current_package, current_mode, phase)] = ms

    return parsed


def run_once(
    env: ProfileEnvironment,
    input_path: Path,
    std_path: Path,
    command: str,
    extra_args: list[str],
) -> dict[tuple[str, str, str], float]:
    cmd = [
        str(env.compiler),
        command,
        str(input_path),
        "--std-path",
        str(std_path),
        "--timings",
    ]
    cmd.extend(extra_args)

    process_env = os.environ.copy()
    process_env["TARO_HOME"] = str(env.taro_home)

    result = subprocess.run(
        cmd,
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        env=process_env,
    )
    if result.returncode != 0:
        print("Command failed:", " ".join(cmd), file=sys.stderr)
        if result.stdout:
            print(result.stdout, file=sys.stderr)
        if result.stderr:
            print(result.stderr, file=sys.stderr)
        raise RuntimeError(f"benchmark command failed for profile={env.profile}")

    parsed = parse_timings(result.stdout + "\n" + result.stderr)
    if not parsed:
        raise RuntimeError(
            f"no timings were parsed for profile={env.profile}; ensure --timings output format is unchanged"
        )
    return parsed


def aggregate_samples(
    samples: list[dict[tuple[str, str, str], float]],
) -> dict[tuple[str, str, str], list[float]]:
    acc: dict[tuple[str, str, str], list[float]] = defaultdict(list)
    for sample in samples:
        for key, value in sample.items():
            acc[key].append(value)
    return acc


def mean(values: list[float]) -> float:
    return statistics.fmean(values) if values else 0.0


def median(values: list[float]) -> float:
    return statistics.median(values) if values else 0.0


def speedup(debug: float, release: float) -> str:
    if release <= 0.0:
        if debug <= 0.0:
            return "N/A"
        return "inf"
    return f"{debug / release:.2f}x"


def format_table(headers: list[str], rows: list[list[str]]) -> str:
    widths = [len(h) for h in headers]
    for row in rows:
        for index, cell in enumerate(row):
            widths[index] = max(widths[index], len(cell))

    def format_row(row: list[str]) -> str:
        return " | ".join(cell.ljust(widths[index]) for index, cell in enumerate(row))

    separator = "-+-".join("-" * width for width in widths)
    lines = [format_row(headers), separator]
    lines.extend(format_row(row) for row in rows)
    return "\n".join(lines)


def default_detail_packages(
    keys: set[tuple[str, str, str]],
    requested: list[str],
) -> list[str]:
    if requested:
        return requested
    package_names = sorted({package for package, _mode, _phase in keys})
    if "std" in package_names:
        return ["std"]
    if package_names:
        return [package_names[0]]
    return []


def main():
    args, extra_args = parse_args()
    input_path = Path(args.input).resolve()
    std_path = Path(args.std_path).resolve()

    if not input_path.exists():
        print(f"input does not exist: {input_path}", file=sys.stderr)
        sys.exit(1)
    if not std_path.exists():
        print(f"std path does not exist: {std_path}", file=sys.stderr)
        sys.exit(1)

    for profile in ("debug", "release"):
        build_profile(profile)

    samples_by_profile: dict[str, list[dict[tuple[str, str, str], float]]] = {
        "debug": [],
        "release": [],
    }

    with tempfile.TemporaryDirectory(prefix="taro_bench_timings_") as temp_dir:
        temp_root = Path(temp_dir)
        envs = {
            "debug": setup_profile_env("debug", temp_root),
            "release": setup_profile_env("release", temp_root),
        }

        for profile in ("debug", "release"):
            print(f"Running {args.runs} timing samples ({profile})...")
            env = envs[profile]
            for run_index in range(args.runs):
                sample = run_once(
                    env=env,
                    input_path=input_path,
                    std_path=std_path,
                    command=args.command,
                    extra_args=extra_args,
                )
                samples_by_profile[profile].append(sample)
                print(f"  {profile} sample {run_index + 1}/{args.runs} complete")

    aggregate_debug = aggregate_samples(samples_by_profile["debug"])
    aggregate_release = aggregate_samples(samples_by_profile["release"])

    all_keys = set(aggregate_debug.keys()) | set(aggregate_release.keys())
    if not all_keys:
        print("No timing data collected.", file=sys.stderr)
        sys.exit(1)

    print()
    print(f"Benchmark input: {input_path}")
    print(f"Command: {args.command}")
    if extra_args:
        print(f"Forwarded args: {' '.join(extra_args)}")
    print(f"Runs/profile: {args.runs}")
    print()

    total_rows: list[list[str]] = []
    total_keys = sorted(k for k in all_keys if k[2] == "total")
    for package, mode, phase in total_keys:
        d_values = aggregate_debug.get((package, mode, phase), [])
        r_values = aggregate_release.get((package, mode, phase), [])
        d_avg = mean(d_values)
        r_avg = mean(r_values)
        total_rows.append(
            [
                package,
                f"{d_avg:.3f}",
                f"{median(d_values):.3f}",
                f"{r_avg:.3f}",
                f"{median(r_values):.3f}",
                speedup(d_avg, r_avg),
            ]
        )

    print("Totals (ms)")
    print(
        format_table(
            ["Package", "Debug avg", "Debug med", "Release avg", "Release med", "Release Speedup"],
            total_rows,
        )
    )

    detail_packages = default_detail_packages(all_keys, args.package)
    for package_name in detail_packages:
        phase_rows: list[list[str]] = []
        phase_keys = [
            key
            for key in all_keys
            if key[0] == package_name and key[2] != "total"
        ]
        phase_keys.sort(
            key=lambda key: mean(aggregate_debug.get(key, [])),
            reverse=True,
        )

        if not phase_keys:
            continue

        for package, mode, phase in phase_keys:
            d_values = aggregate_debug.get((package, mode, phase), [])
            r_values = aggregate_release.get((package, mode, phase), [])
            d_avg = mean(d_values)
            r_avg = mean(r_values)
            phase_rows.append(
                [
                    phase,
                    f"{d_avg:.3f}",
                    f"{r_avg:.3f}",
                    speedup(d_avg, r_avg),
                ]
            )

        print()
        print(f"Detailed phases for package '{package_name}' (ms)")
        print(
            format_table(
                ["Phase", "Debug avg", "Release avg", "Release Speedup"],
                phase_rows,
            )
        )


if __name__ == "__main__":
    main()
