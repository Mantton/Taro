#!/usr/bin/env python3
"""Regression tests for compiler timing sample construction."""

from __future__ import annotations

import subprocess
import unittest
from pathlib import Path
from unittest import mock

from benchmark_timings import ProfileEnvironment, run_once


class BenchmarkTimingTests(unittest.TestCase):
    def assert_cold_sample_command(self, extra_args: list[str]) -> None:
        profile = ProfileEnvironment(
            profile="debug",
            compiler=Path("/toolchain/bin/taro"),
            taro_home=Path("/toolchain"),
            dist_dir=Path("/toolchain"),
        )
        completed = subprocess.CompletedProcess(
            args=[],
            returncode=0,
            stdout="Timings – std (compile)\n  total 1.00 ms\n",
            stderr="",
        )

        with mock.patch("benchmark_timings.subprocess.run", return_value=completed) as run:
            timings = run_once(
                env=profile,
                input_path=Path("/source/std"),
                std_path=Path("/source/std"),
                command="check",
                extra_args=extra_args,
            )

        command = run.call_args.args[0]
        self.assertEqual(command.count("--no-incremental"), 1)
        self.assertIn(("std", "compile", "total"), timings)

    def test_each_sample_forces_cold_compilation(self) -> None:
        self.assert_cold_sample_command([])

    def test_explicit_cold_flag_is_not_duplicated(self) -> None:
        self.assert_cold_sample_command(["--no-incremental"])


if __name__ == "__main__":
    unittest.main()
