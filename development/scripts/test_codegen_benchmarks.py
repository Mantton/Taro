#!/usr/bin/env python3
"""Regression tests for the code-generation benchmark harness."""

from __future__ import annotations

import unittest
from pathlib import Path

from codegen_benchmarks import (
    BenchmarkResult,
    Variant,
    alternating_order,
    compile_command,
    validate_equivalent_outputs,
)


class CodegenBenchmarkTests(unittest.TestCase):
    def test_sample_order_alternates_to_avoid_systematic_bias(self) -> None:
        variants = (Variant("baseline", "-Obaseline"), Variant("O2", "-O2"))

        self.assertEqual(alternating_order(variants, 0), variants)
        self.assertEqual(alternating_order(variants, 1), tuple(reversed(variants)))
        self.assertEqual(alternating_order(variants, 2), variants)

    def test_compile_command_is_cold_release_and_variant_scoped(self) -> None:
        variant = Variant("baseline", "-Obaseline")
        command = compile_command(
            compiler=Path("/toolchain/bin/taro"),
            source=Path("/source/workload.tr"),
            std_path=Path("/source/std"),
            output=Path("/tmp/baseline/workload"),
            variant=variant,
        )

        self.assertIn("--release", command)
        self.assertIn("--no-incremental", command)
        self.assertIn("-Obaseline", command)
        self.assertEqual(command.count("--no-incremental"), 1)
        self.assertEqual(command[-2:], ["-o", "/tmp/baseline/workload"])

    def test_output_equivalence_accepts_matching_variants(self) -> None:
        validate_equivalent_outputs(
            (
                self.result("baseline", "42\n"),
                self.result("O2", "42\n"),
            )
        )

    def test_output_equivalence_rejects_optimizer_miscompile(self) -> None:
        with self.assertRaisesRegex(RuntimeError, "output mismatch"):
            validate_equivalent_outputs(
                (
                    self.result("baseline", "42\n"),
                    self.result("O2", "41\n"),
                )
            )

    @staticmethod
    def result(name: str, stdout: str) -> BenchmarkResult:
        return BenchmarkResult(
            variant=Variant(name, f"-O{name}"),
            compile_ms=(1.0,),
            runtime_ms=(1.0,),
            executable_bytes=1,
            stdout=stdout,
        )


if __name__ == "__main__":
    unittest.main()
