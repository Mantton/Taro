#!/usr/bin/env python3
"""Compare Taro's retained release baseline with LLVM's O2 pipeline."""

from __future__ import annotations

import argparse
import os
import statistics
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
BUILD_DIST_SCRIPT = PROJECT_ROOT / "development" / "scripts" / "build_dist.py"
DEFAULT_INPUT = PROJECT_ROOT / "development" / "benchmarks" / "codegen" / "optimizer_workload.tr"
DEFAULT_STD_PATH = PROJECT_ROOT / "std"


@dataclass(frozen=True)
class Variant:
    name: str
    optimization_argument: str


@dataclass(frozen=True)
class BenchmarkResult:
    variant: Variant
    compile_ms: tuple[float, ...]
    runtime_ms: tuple[float, ...]
    executable_bytes: int
    stdout: str


VARIANTS = (
    Variant(name="baseline", optimization_argument="-Obaseline"),
    Variant(name="O2", optimization_argument="-O2"),
)


def positive_int(value: str) -> int:
    try:
        parsed = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"invalid int value: {value}") from error
    if parsed < 1:
        raise argparse.ArgumentTypeError("value must be >= 1")
    return parsed


def non_negative_int(value: str) -> int:
    try:
        parsed = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"invalid int value: {value}") from error
    if parsed < 0:
        raise argparse.ArgumentTypeError("value must be >= 0")
    return parsed


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Benchmark cold compile time, warmed runtime, and executable size for "
            "Taro's retained release baseline and LLVM O2."
        )
    )
    parser.add_argument(
        "input",
        nargs="?",
        type=Path,
        default=DEFAULT_INPUT,
        help=f"Taro source file to benchmark (default: {DEFAULT_INPUT})",
    )
    parser.add_argument(
        "--runs",
        type=positive_int,
        default=5,
        help="Measured compile and runtime samples per variant (default: 5)",
    )
    parser.add_argument(
        "--warmups",
        type=non_negative_int,
        default=1,
        help="Unmeasured executable runs per variant (default: 1)",
    )
    parser.add_argument(
        "--std-path",
        type=Path,
        default=DEFAULT_STD_PATH,
        help=f"Standard-library source path (default: {DEFAULT_STD_PATH})",
    )
    return parser.parse_args()


def compile_command(
    compiler: Path,
    source: Path,
    std_path: Path,
    output: Path,
    variant: Variant,
) -> list[str]:
    return [
        str(compiler),
        "build",
        str(source),
        "--std-path",
        str(std_path),
        "--release",
        "--no-incremental",
        variant.optimization_argument,
        "-o",
        str(output),
    ]


def run_checked(
    command: list[str],
    *,
    env: dict[str, str],
) -> tuple[float, subprocess.CompletedProcess[str]]:
    started_at = time.perf_counter_ns()
    completed = subprocess.run(
        command,
        cwd=PROJECT_ROOT,
        env=env,
        capture_output=True,
        text=True,
    )
    elapsed_ms = (time.perf_counter_ns() - started_at) / 1_000_000.0
    if completed.returncode != 0:
        rendered = " ".join(command)
        raise RuntimeError(
            f"command failed ({completed.returncode}): {rendered}\n"
            f"stdout:\n{completed.stdout}\n"
            f"stderr:\n{completed.stderr}"
        )
    return elapsed_ms, completed


def bootstrap_distribution(dist_dir: Path, std_path: Path) -> Path:
    command = [
        sys.executable,
        str(BUILD_DIST_SCRIPT),
        "--profile",
        "release",
        "--dist-dir",
        str(dist_dir),
        "--std-path",
        str(std_path),
    ]
    completed = subprocess.run(command, cwd=PROJECT_ROOT)
    if completed.returncode != 0:
        raise RuntimeError("release distribution bootstrap failed")
    compiler = dist_dir / "bin" / "taro"
    if not compiler.is_file():
        raise RuntimeError(f"compiler missing after bootstrap: {compiler}")
    return compiler


def alternating_order(
    variants: tuple[Variant, ...], sample_index: int
) -> tuple[Variant, ...]:
    if sample_index % 2 == 0:
        return variants
    return tuple(reversed(variants))


def benchmark_variants(
    compiler: Path,
    taro_home: Path,
    source: Path,
    std_path: Path,
    output_dir: Path,
    variants: tuple[Variant, ...],
    runs: int,
    warmups: int,
) -> tuple[BenchmarkResult, ...]:
    env = os.environ.copy()
    env["TARO_HOME"] = str(taro_home)
    binaries = {
        variant: output_dir / variant.name.lower() / source.stem
        for variant in variants
    }
    for binary in binaries.values():
        binary.parent.mkdir(parents=True, exist_ok=True)

    compile_samples: dict[Variant, list[float]] = {
        variant: [] for variant in variants
    }
    for sample_index in range(runs):
        for variant in alternating_order(variants, sample_index):
            command = compile_command(
                compiler, source, std_path, binaries[variant], variant
            )
            elapsed_ms, _ = run_checked(command, env=env)
            compile_samples[variant].append(elapsed_ms)

    for binary in binaries.values():
        if not binary.is_file():
            raise RuntimeError(f"compiler did not produce executable: {binary}")

    for sample_index in range(warmups):
        for variant in alternating_order(variants, sample_index):
            run_checked([str(binaries[variant])], env=env)

    runtime_samples: dict[Variant, list[float]] = {
        variant: [] for variant in variants
    }
    outputs: dict[Variant, list[str]] = {variant: [] for variant in variants}
    for sample_index in range(runs):
        for variant in alternating_order(variants, sample_index):
            elapsed_ms, completed = run_checked(
                [str(binaries[variant])], env=env
            )
            runtime_samples[variant].append(elapsed_ms)
            outputs[variant].append(completed.stdout)

    results: list[BenchmarkResult] = []
    for variant in variants:
        expected = outputs[variant][0]
        if any(output != expected for output in outputs[variant][1:]):
            raise RuntimeError(f"{variant.name} produced unstable output across runs")
        results.append(
            BenchmarkResult(
                variant=variant,
                compile_ms=tuple(compile_samples[variant]),
                runtime_ms=tuple(runtime_samples[variant]),
                executable_bytes=binaries[variant].stat().st_size,
                stdout=expected,
            )
        )

    return tuple(results)


def validate_equivalent_outputs(results: tuple[BenchmarkResult, ...]) -> None:
    if not results:
        raise ValueError("at least one benchmark result is required")
    expected = results[0].stdout
    for result in results[1:]:
        if result.stdout != expected:
            raise RuntimeError(
                f"output mismatch: {results[0].variant.name} produced {expected!r}, "
                f"but {result.variant.name} produced {result.stdout!r}"
            )


def median(values: tuple[float, ...]) -> float:
    return statistics.median(values)


def ratio(numerator: float, denominator: float) -> float:
    if denominator == 0.0:
        return float("inf")
    return numerator / denominator


def print_results(source: Path, runs: int, warmups: int, results: tuple[BenchmarkResult, ...]) -> None:
    print()
    print(f"Codegen benchmark: {source}")
    print(f"Samples/variant: {runs} measured, {warmups} runtime warmup(s)")
    print("Incremental reuse: disabled for compile samples")
    print()
    print("Variant  Compile median (ms)  Runtime median (ms)  Executable (bytes)")
    print("-------  -------------------  -------------------  ------------------")
    for result in results:
        print(
            f"{result.variant.name:<8} "
            f"{median(result.compile_ms):>19.3f}  "
            f"{median(result.runtime_ms):>19.3f}  "
            f"{result.executable_bytes:>18}"
        )

    baseline, optimized = results
    print()
    print(
        "O2 runtime speedup: "
        f"{ratio(median(baseline.runtime_ms), median(optimized.runtime_ms)):.2f}x"
    )
    print(
        "O2 compile-time ratio: "
        f"{ratio(median(optimized.compile_ms), median(baseline.compile_ms)):.2f}x"
    )
    print(
        "O2 executable-size ratio: "
        f"{ratio(float(optimized.executable_bytes), float(baseline.executable_bytes)):.3f}x"
    )
    print(f"Program output: {optimized.stdout.strip()}")


def main() -> int:
    args = parse_args()
    source = args.input.resolve()
    std_path = args.std_path.resolve()
    if not source.is_file():
        print(f"error: benchmark input is not a file: {source}", file=sys.stderr)
        return 2
    if not std_path.is_dir():
        print(f"error: std path is not a directory: {std_path}", file=sys.stderr)
        return 2

    try:
        with tempfile.TemporaryDirectory(prefix="taro_codegen_benchmark_") as temp:
            temp_root = Path(temp)
            dist_dir = temp_root / "dist"
            compiler = bootstrap_distribution(dist_dir, std_path)
            results = benchmark_variants(
                compiler=compiler,
                taro_home=dist_dir,
                source=source,
                std_path=std_path,
                output_dir=temp_root / "outputs",
                variants=VARIANTS,
                runs=args.runs,
                warmups=args.warmups,
            )
            validate_equivalent_outputs(results)
            print_results(source, args.runs, args.warmups, results)
    except RuntimeError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
