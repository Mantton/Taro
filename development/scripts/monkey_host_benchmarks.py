#!/usr/bin/env python3
"""Compare matched Taro/Go workloads from the Monkey tree-walker hot path."""

from __future__ import annotations

import argparse
import os
import re
import statistics
import subprocess
import sys
import tempfile
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
BUILD_DIST_SCRIPT = PROJECT_ROOT / "development" / "scripts" / "build_dist.py"
FIXTURE_DIR = PROJECT_ROOT / "development" / "benchmarks" / "monkey_host_gap"
TARO_SOURCE = FIXTURE_DIR / "host_gap.tr"
DEFAULT_STD_PATH = PROJECT_ROOT / "std"


@dataclass(frozen=True)
class Workload:
    name: str
    iterations: int
    quick_iterations: int


WORKLOADS = (
    Workload("dictionary_lookup", 5_000_000, 25_000),
    Workload("environment_lookup", 5_000_000, 25_000),
    Workload("environment_churn", 250_000, 2_500),
    Workload("argument_list", 1_000_000, 10_000),
    Workload("result_success", 10_000_000, 100_000),
    Workload("small_allocation", 2_000_000, 20_000),
)
WORKLOAD_BY_NAME = {workload.name: workload for workload in WORKLOADS}
LANGUAGES = ("taro", "go")

BENCHMARK_RE = re.compile(
    r"^benchmark case=(?P<case>[a-z_]+) "
    r"iterations=(?P<iterations>\d+) "
    r"elapsed_ns=(?P<elapsed_ns>\d+) "
    r"checksum=(?P<checksum>-?\d+)$",
    re.MULTILINE,
)
TARO_GC_RE = re.compile(
    r"^\s*gc collections=(?P<collections>\d+) "
    r"allocations=(?P<allocations>\d+) "
    r"frees=\d+ allocated_bytes=(?P<allocated_bytes>\d+)\b",
    re.MULTILINE,
)
TARO_PAUSE_RE = re.compile(
    r"^\s*gc_pause_ns count=(?P<count>\d+) "
    r"p50=(?P<p50>\d+) p95=(?P<p95>\d+) "
    r"p99=(?P<p99>\d+) max=(?P<max>\d+)$",
    re.MULTILINE,
)
GO_STATS_RE = re.compile(
    r"^go stats: collections=(?P<collections>\d+) "
    r"allocations=(?P<allocations>\d+) "
    r"allocated_bytes=(?P<allocated_bytes>\d+)$",
    re.MULTILINE,
)


@dataclass(frozen=True)
class RuntimeMetrics:
    collections: int
    allocations: int
    allocated_bytes: int
    pause_count: int = 0
    pause_p50_ns: int = 0
    pause_p95_ns: int = 0
    pause_p99_ns: int = 0
    pause_max_ns: int = 0


@dataclass(frozen=True)
class Sample:
    language: str
    case: str
    iterations: int
    elapsed_ns: int
    checksum: int
    metrics: RuntimeMetrics


@dataclass(frozen=True)
class CaseSummary:
    case: str
    iterations: int
    checksum: int
    taro_elapsed_ns: float
    go_elapsed_ns: float
    taro_allocations: float
    go_allocations: float
    taro_allocated_bytes: float
    go_allocated_bytes: float
    taro_collections: float
    go_collections: float
    taro_pause_p50_ns: float
    taro_pause_p95_ns: float
    taro_pause_max_ns: float

    @property
    def elapsed_ratio(self) -> float:
        return ratio(self.taro_elapsed_ns, self.go_elapsed_ns)


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


def iteration_override(value: str) -> tuple[str, int]:
    name, separator, raw_count = value.partition("=")
    if not separator or name not in WORKLOAD_BY_NAME:
        choices = ", ".join(WORKLOAD_BY_NAME)
        raise argparse.ArgumentTypeError(
            f"expected CASE=COUNT with CASE one of: {choices}"
        )
    try:
        count = positive_int(raw_count)
    except argparse.ArgumentTypeError as error:
        raise argparse.ArgumentTypeError(f"invalid iteration override: {value}") from error
    return name, count


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Compare matched Taro and Go workloads that isolate hot operations "
            "in the Monkey tree-walking evaluator."
        )
    )
    parser.add_argument(
        "--case",
        action="append",
        choices=tuple(WORKLOAD_BY_NAME),
        default=[],
        help="Run only this case; repeat to select multiple cases.",
    )
    parser.add_argument(
        "--runs",
        type=positive_int,
        default=5,
        help="Measured fresh-process samples per language and case (default: 5).",
    )
    parser.add_argument(
        "--warmups",
        type=non_negative_int,
        default=1,
        help="Unmeasured fresh-process samples per language and case (default: 1).",
    )
    parser.add_argument(
        "--quick",
        action="store_true",
        help="Use smoke-test iteration counts instead of benchmark counts.",
    )
    parser.add_argument(
        "--iterations",
        action="append",
        type=iteration_override,
        default=[],
        metavar="CASE=COUNT",
        help="Override the iteration count for one case; repeat as needed.",
    )
    parser.add_argument(
        "--compiler",
        type=Path,
        help="Use this Taro compiler instead of bootstrapping a temporary release dist.",
    )
    parser.add_argument(
        "--taro-home",
        type=Path,
        help="TARO_HOME for --compiler; defaults to the compiler's dist root.",
    )
    parser.add_argument(
        "--std-path",
        type=Path,
        default=DEFAULT_STD_PATH,
        help=f"Standard-library source path (default: {DEFAULT_STD_PATH}).",
    )
    parser.add_argument(
        "--json-output",
        type=Path,
        help="Also write measured samples and summaries as JSON to this path.",
    )
    return parser.parse_args()


def selected_workloads(
    names: Sequence[str], quick: bool, overrides: Iterable[tuple[str, int]]
) -> tuple[Workload, ...]:
    selected_names = set(names) if names else set(WORKLOAD_BY_NAME)
    override_map = dict(overrides)
    selected: list[Workload] = []
    for workload in WORKLOADS:
        if workload.name not in selected_names:
            continue
        default = workload.quick_iterations if quick else workload.iterations
        count = override_map.get(workload.name, default)
        selected.append(Workload(workload.name, count, count))
    return tuple(selected)


def alternating_order(sample_index: int) -> tuple[str, ...]:
    if sample_index % 2 == 0:
        return LANGUAGES
    return tuple(reversed(LANGUAGES))


def taro_compile_command(
    compiler: Path, source: Path, std_path: Path, output: Path
) -> list[str]:
    return [
        str(compiler),
        "build",
        str(source),
        "--std-path",
        str(std_path),
        "--release",
        "--no-incremental",
        "-O2",
        "-o",
        str(output),
    ]


def go_compile_command(output: Path) -> list[str]:
    return ["go", "build", "-trimpath", "-o", str(output), "."]


def program_command(binary: Path, workload: Workload) -> list[str]:
    return [str(binary), workload.name, str(workload.iterations)]


def run_checked(
    command: Sequence[str], *, cwd: Path, env: dict[str, str]
) -> subprocess.CompletedProcess[str]:
    try:
        completed = subprocess.run(
            list(command),
            cwd=cwd,
            env=env,
            capture_output=True,
            text=True,
        )
    except FileNotFoundError as error:
        raise RuntimeError(f"required executable not found: {command[0]}") from error
    if completed.returncode != 0:
        rendered = " ".join(str(part) for part in command)
        raise RuntimeError(
            f"command failed ({completed.returncode}): {rendered}\n"
            f"stdout:\n{completed.stdout}\n"
            f"stderr:\n{completed.stderr}"
        )
    return completed


def only_match(pattern: re.Pattern[str], text: str, label: str) -> re.Match[str]:
    matches = list(pattern.finditer(text))
    if len(matches) != 1:
        raise RuntimeError(f"expected exactly one {label}, found {len(matches)}")
    return matches[0]


def parse_sample(language: str, stdout: str, stderr: str) -> Sample:
    if language not in LANGUAGES:
        raise ValueError(f"unsupported language: {language}")
    benchmark = only_match(BENCHMARK_RE, stdout, "benchmark result line")

    if language == "taro":
        gc = only_match(TARO_GC_RE, stderr, "Taro GC statistics line")
        pause = only_match(TARO_PAUSE_RE, stderr, "Taro GC pause line")
        metrics = RuntimeMetrics(
            collections=int(gc.group("collections")),
            allocations=int(gc.group("allocations")),
            allocated_bytes=int(gc.group("allocated_bytes")),
            pause_count=int(pause.group("count")),
            pause_p50_ns=int(pause.group("p50")),
            pause_p95_ns=int(pause.group("p95")),
            pause_p99_ns=int(pause.group("p99")),
            pause_max_ns=int(pause.group("max")),
        )
    else:
        stats = only_match(GO_STATS_RE, stderr, "Go runtime statistics line")
        metrics = RuntimeMetrics(
            collections=int(stats.group("collections")),
            allocations=int(stats.group("allocations")),
            allocated_bytes=int(stats.group("allocated_bytes")),
        )

    return Sample(
        language=language,
        case=benchmark.group("case"),
        iterations=int(benchmark.group("iterations")),
        elapsed_ns=int(benchmark.group("elapsed_ns")),
        checksum=int(benchmark.group("checksum")),
        metrics=metrics,
    )


def execute_sample(
    language: str,
    binary: Path,
    workload: Workload,
    env: dict[str, str],
) -> Sample:
    completed = run_checked(
        program_command(binary, workload), cwd=PROJECT_ROOT, env=env
    )
    sample = parse_sample(language, completed.stdout, completed.stderr)
    if sample.case != workload.name or sample.iterations != workload.iterations:
        raise RuntimeError(
            f"{language} reported {sample.case}/{sample.iterations}, expected "
            f"{workload.name}/{workload.iterations}"
        )
    if sample.elapsed_ns < 1:
        raise RuntimeError(f"{language} reported a non-positive elapsed time")
    return sample


def validate_equivalent_samples(
    workloads: Sequence[Workload], samples: Sequence[Sample], runs: int
) -> None:
    for workload in workloads:
        by_language = {
            language: [
                sample
                for sample in samples
                if sample.case == workload.name and sample.language == language
            ]
            for language in LANGUAGES
        }
        for language, language_samples in by_language.items():
            if len(language_samples) != runs:
                raise RuntimeError(
                    f"{workload.name}/{language} has {len(language_samples)} samples; "
                    f"expected {runs}"
                )
            checksums = {sample.checksum for sample in language_samples}
            iterations = {sample.iterations for sample in language_samples}
            if len(checksums) != 1 or iterations != {workload.iterations}:
                raise RuntimeError(
                    f"{workload.name}/{language} produced unstable output across runs"
                )

        taro_checksum = by_language["taro"][0].checksum
        go_checksum = by_language["go"][0].checksum
        if taro_checksum != go_checksum:
            raise RuntimeError(
                f"checksum mismatch for {workload.name}: "
                f"Taro={taro_checksum}, Go={go_checksum}"
            )


def median(values: Iterable[int]) -> float:
    materialized = tuple(values)
    if not materialized:
        raise ValueError("median requires at least one value")
    return float(statistics.median(materialized))


def ratio(numerator: float, denominator: float) -> float:
    if denominator == 0.0:
        return float("inf") if numerator > 0.0 else 1.0
    return numerator / denominator


def summarize(
    workloads: Sequence[Workload], samples: Sequence[Sample]
) -> tuple[CaseSummary, ...]:
    summaries: list[CaseSummary] = []
    for workload in workloads:
        grouped = {
            language: [
                sample
                for sample in samples
                if sample.case == workload.name and sample.language == language
            ]
            for language in LANGUAGES
        }
        taro = grouped["taro"]
        go = grouped["go"]
        if not taro or not go:
            raise ValueError(f"cannot summarize incomplete case: {workload.name}")
        summaries.append(
            CaseSummary(
                case=workload.name,
                iterations=workload.iterations,
                checksum=taro[0].checksum,
                taro_elapsed_ns=median(sample.elapsed_ns for sample in taro),
                go_elapsed_ns=median(sample.elapsed_ns for sample in go),
                taro_allocations=median(sample.metrics.allocations for sample in taro),
                go_allocations=median(sample.metrics.allocations for sample in go),
                taro_allocated_bytes=median(
                    sample.metrics.allocated_bytes for sample in taro
                ),
                go_allocated_bytes=median(
                    sample.metrics.allocated_bytes for sample in go
                ),
                taro_collections=median(sample.metrics.collections for sample in taro),
                go_collections=median(sample.metrics.collections for sample in go),
                taro_pause_p50_ns=median(
                    sample.metrics.pause_p50_ns for sample in taro
                ),
                taro_pause_p95_ns=median(
                    sample.metrics.pause_p95_ns for sample in taro
                ),
                taro_pause_max_ns=median(
                    sample.metrics.pause_max_ns for sample in taro
                ),
            )
        )
    return tuple(summaries)


def format_table(headers: Sequence[str], rows: Sequence[Sequence[str]]) -> str:
    widths = [len(header) for header in headers]
    for row in rows:
        for index, cell in enumerate(row):
            widths[index] = max(widths[index], len(cell))

    def format_row(row: Sequence[str]) -> str:
        return "  ".join(cell.ljust(widths[index]) for index, cell in enumerate(row))

    separator = "  ".join("-" * width for width in widths)
    return "\n".join(
        [format_row(headers), separator, *(format_row(row) for row in rows)]
    )


def format_ratio(value: float) -> str:
    return "inf" if value == float("inf") else f"{value:.2f}x"


def print_results(
    summaries: Sequence[CaseSummary], runs: int, warmups: int
) -> None:
    print()
    print("Monkey host-gap diagnostics")
    print(f"Samples: {runs} measured, {warmups} unmeasured warmup(s)")
    print("Taro: release O2, TARO_WORKERS=1; Go: release defaults")
    print("Every sample is a fresh process; reported values are medians.")
    print()

    timing_rows = [
        (
            summary.case,
            f"{summary.iterations:,}",
            f"{summary.taro_elapsed_ns / 1_000_000.0:,.3f}",
            f"{summary.go_elapsed_ns / 1_000_000.0:,.3f}",
            format_ratio(summary.elapsed_ratio),
        )
        for summary in summaries
    ]
    print(
        format_table(
            ("Case", "Iterations", "Taro ms", "Go ms", "Taro/Go"), timing_rows
        )
    )
    print()

    allocation_rows = [
        (
            summary.case,
            f"{summary.taro_allocations:,.0f}",
            f"{summary.go_allocations:,.0f}",
            f"{summary.taro_allocations / summary.iterations:.3f}/"
            f"{summary.go_allocations / summary.iterations:.3f}",
            f"{summary.taro_allocated_bytes:,.0f}",
            f"{summary.go_allocated_bytes:,.0f}",
            f"{summary.taro_allocated_bytes / summary.iterations:.1f}/"
            f"{summary.go_allocated_bytes / summary.iterations:.1f}",
            f"{summary.taro_collections:,.0f}/{summary.go_collections:,.0f}",
        )
        for summary in summaries
    ]
    print(
        format_table(
            (
                "Case",
                "Taro allocs",
                "Go allocs",
                "Allocs/i T/G",
                "Taro bytes",
                "Go bytes",
                "Bytes/i T/G",
                "GCs T/G",
            ),
            allocation_rows,
        )
    )
    print()
    print(
        "Raw Taro counters include fixed root-task reporting work; per-iteration "
        "rates make that overhead visible."
    )
    print()

    pause_rows = [
        (
            summary.case,
            f"{summary.taro_pause_p50_ns / 1_000.0:,.1f}",
            f"{summary.taro_pause_p95_ns / 1_000.0:,.1f}",
            f"{summary.taro_pause_max_ns / 1_000.0:,.1f}",
        )
        for summary in summaries
    ]
    print(
        format_table(
            ("Case", "Taro GC p50 us", "Taro GC p95 us", "Taro GC max us"),
            pause_rows,
        )
    )
    print()

    ranked = sorted(summaries, key=lambda summary: summary.elapsed_ratio, reverse=True)
    print("Runtime-gap ranking: " + ", ".join(
        f"{summary.case} ({format_ratio(summary.elapsed_ratio)})"
        for summary in ranked
    ))


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


def benchmark(
    workloads: Sequence[Workload],
    runs: int,
    warmups: int,
    binaries: dict[str, Path],
    environments: dict[str, dict[str, str]],
) -> tuple[Sample, ...]:
    for warmup_index in range(warmups):
        for workload in workloads:
            for language in alternating_order(warmup_index):
                execute_sample(
                    language, binaries[language], workload, environments[language]
                )

    measured: list[Sample] = []
    for sample_index in range(runs):
        for workload in workloads:
            for language in alternating_order(sample_index):
                measured.append(
                    execute_sample(
                        language, binaries[language], workload, environments[language]
                    )
                )
    return tuple(measured)


def write_json_results(
    path: Path,
    workloads: Sequence[Workload],
    samples: Sequence[Sample],
    summaries: Sequence[CaseSummary],
    runs: int,
    warmups: int,
) -> None:
    import json

    payload = {
        "schema": 1,
        "runs": runs,
        "warmups": warmups,
        "workloads": [asdict(workload) for workload in workloads],
        "samples": [asdict(sample) for sample in samples],
        "summaries": [
            {**asdict(summary), "elapsed_ratio": summary.elapsed_ratio}
            for summary in summaries
        ],
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()
    std_path = args.std_path.resolve()
    if not std_path.is_dir():
        print(f"error: std path is not a directory: {std_path}", file=sys.stderr)
        return 2
    if args.taro_home is not None and args.compiler is None:
        print("error: --taro-home requires --compiler", file=sys.stderr)
        return 2

    workloads = selected_workloads(args.case, args.quick, args.iterations)
    try:
        with tempfile.TemporaryDirectory(prefix="taro_monkey_host_gap_") as temp:
            temp_root = Path(temp)
            if args.compiler is None:
                taro_home = temp_root / "dist"
                compiler = bootstrap_distribution(taro_home, std_path)
            else:
                compiler = args.compiler.resolve()
                if not compiler.is_file():
                    raise RuntimeError(f"Taro compiler is not a file: {compiler}")
                taro_home = (
                    args.taro_home.resolve()
                    if args.taro_home is not None
                    else compiler.parent.parent
                )
                if not taro_home.is_dir():
                    raise RuntimeError(f"TARO_HOME is not a directory: {taro_home}")

            taro_binary = temp_root / "bin" / "host_gap_taro"
            go_binary = temp_root / "bin" / "host_gap_go"
            taro_binary.parent.mkdir(parents=True, exist_ok=True)

            base_env = os.environ.copy()
            taro_env = base_env.copy()
            taro_env["TARO_HOME"] = str(taro_home)
            taro_env["TARO_WORKERS"] = "1"
            taro_env["TARO_RUNTIME_STATS"] = "1"
            taro_env.pop("TARO_RUNTIME_TRACE", None)

            run_checked(
                taro_compile_command(compiler, TARO_SOURCE, std_path, taro_binary),
                cwd=PROJECT_ROOT,
                env=taro_env,
            )
            run_checked(
                go_compile_command(go_binary), cwd=FIXTURE_DIR, env=base_env
            )

            samples = benchmark(
                workloads=workloads,
                runs=args.runs,
                warmups=args.warmups,
                binaries={"taro": taro_binary, "go": go_binary},
                environments={"taro": taro_env, "go": base_env},
            )
            validate_equivalent_samples(workloads, samples, args.runs)
            summaries = summarize(workloads, samples)
            print_results(summaries, args.runs, args.warmups)
            if args.json_output is not None:
                output_path = args.json_output.resolve()
                write_json_results(
                    output_path,
                    workloads,
                    samples,
                    summaries,
                    args.runs,
                    args.warmups,
                )
                print(f"JSON results: {output_path}")
    except RuntimeError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
