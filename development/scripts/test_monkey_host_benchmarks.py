#!/usr/bin/env python3
"""Regression tests for the Monkey host-gap diagnostic harness."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from monkey_host_benchmarks import (
    RuntimeMetrics,
    Sample,
    Workload,
    alternating_order,
    parse_sample,
    selected_workloads,
    summarize,
    taro_compile_command,
    validate_equivalent_samples,
    write_json_results,
)


TARO_STDERR = (
    "runtime stats:\n"
    "  gc collections=7 allocations=100 frees=90 allocated_bytes=8000 "
    "freed_bytes=7000 live_objects=10 heap_live_bytes=1000 heap_goal=1048576 "
    "memory_limit=off heap_reserved_bytes=4194304 heap_free_page_bytes=100 "
    "cached_span_refills=3 released_bytes=0 scavenged_bytes=0 "
    "soft_limit_exceedances=0\n"
    "  gc_pause_ns count=7 p50=100 p95=200 p99=300 max=400\n"
)


class MonkeyHostBenchmarkTests(unittest.TestCase):
    def test_sample_order_alternates_languages(self) -> None:
        self.assertEqual(alternating_order(0), ("taro", "go"))
        self.assertEqual(alternating_order(1), ("go", "taro"))
        self.assertEqual(alternating_order(2), ("taro", "go"))

    def test_taro_parser_reads_result_gc_and_pause_statistics(self) -> None:
        sample = parse_sample(
            "taro",
            "benchmark case=result_success iterations=10 elapsed_ns=1234 checksum=145\n",
            TARO_STDERR,
        )

        self.assertEqual(sample.case, "result_success")
        self.assertEqual(sample.elapsed_ns, 1234)
        self.assertEqual(sample.checksum, 145)
        self.assertEqual(sample.metrics.allocations, 100)
        self.assertEqual(sample.metrics.allocated_bytes, 8000)
        self.assertEqual(sample.metrics.collections, 7)
        self.assertEqual(sample.metrics.pause_p95_ns, 200)

    def test_go_parser_reads_memstats_delta(self) -> None:
        sample = parse_sample(
            "go",
            "benchmark case=small_allocation iterations=5 elapsed_ns=99 checksum=10\n",
            "go stats: collections=1 allocations=5 allocated_bytes=40\n",
        )

        self.assertEqual(sample.metrics, RuntimeMetrics(1, 5, 40))

    def test_parser_rejects_duplicate_structured_results(self) -> None:
        line = "benchmark case=result_success iterations=10 elapsed_ns=1 checksum=1\n"
        with self.assertRaisesRegex(RuntimeError, "exactly one benchmark"):
            parse_sample("taro", line + line, TARO_STDERR)

    def test_equivalence_rejects_cross_language_checksum_mismatch(self) -> None:
        workload = Workload("result_success", 10, 10)
        samples = (
            self.sample("taro", checksum=145),
            self.sample("go", checksum=144),
        )

        with self.assertRaisesRegex(RuntimeError, "checksum mismatch"):
            validate_equivalent_samples((workload,), samples, runs=1)

    def test_summary_uses_medians_and_ratios(self) -> None:
        workload = Workload("result_success", 10, 10)
        samples = (
            self.sample("taro", elapsed_ns=300, allocations=30),
            self.sample("taro", elapsed_ns=100, allocations=10),
            self.sample("taro", elapsed_ns=200, allocations=20),
            self.sample("go", elapsed_ns=40, allocations=4),
            self.sample("go", elapsed_ns=20, allocations=2),
            self.sample("go", elapsed_ns=30, allocations=3),
        )

        summary = summarize((workload,), samples)[0]
        self.assertEqual(summary.taro_elapsed_ns, 200)
        self.assertEqual(summary.go_elapsed_ns, 30)
        self.assertAlmostEqual(summary.elapsed_ratio, 200 / 30)
        self.assertEqual(summary.taro_allocations, 20)
        self.assertEqual(summary.go_allocations, 3)

    def test_quick_counts_and_overrides_preserve_manifest_order(self) -> None:
        workloads = selected_workloads(
            ("small_allocation", "environment_lookup"),
            quick=True,
            overrides=(("small_allocation", 77),),
        )

        self.assertEqual(
            [(workload.name, workload.iterations) for workload in workloads],
            [("environment_lookup", 25_000), ("small_allocation", 77)],
        )

    def test_taro_compile_is_release_o2_and_non_incremental(self) -> None:
        command = taro_compile_command(
            Path("/dist/bin/taro"),
            Path("/source/host_gap.tr"),
            Path("/source/std"),
            Path("/tmp/host_gap"),
        )

        self.assertIn("--release", command)
        self.assertIn("--no-incremental", command)
        self.assertIn("-O2", command)
        self.assertEqual(command[-2:], ["-o", "/tmp/host_gap"])

    def test_json_output_includes_raw_samples_and_derived_ratio(self) -> None:
        workload = Workload("result_success", 10, 10)
        samples = (
            self.sample("taro", elapsed_ns=200),
            self.sample("go", elapsed_ns=50),
        )
        summaries = summarize((workload,), samples)

        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "result.json"
            write_json_results(output, (workload,), samples, summaries, 1, 0)
            payload = json.loads(output.read_text(encoding="utf-8"))

        self.assertEqual(payload["schema"], 1)
        self.assertEqual(len(payload["samples"]), 2)
        self.assertEqual(payload["summaries"][0]["elapsed_ratio"], 4.0)

    @staticmethod
    def sample(
        language: str,
        *,
        elapsed_ns: int = 100,
        checksum: int = 145,
        allocations: int = 10,
    ) -> Sample:
        return Sample(
            language=language,
            case="result_success",
            iterations=10,
            elapsed_ns=elapsed_ns,
            checksum=checksum,
            metrics=RuntimeMetrics(
                collections=1,
                allocations=allocations,
                allocated_bytes=allocations * 8,
            ),
        )


if __name__ == "__main__":
    unittest.main()
