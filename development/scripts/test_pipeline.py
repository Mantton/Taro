#!/usr/bin/env python3
"""Regression tests for full-suite orchestration and failure reporting."""

import contextlib
import io
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import test_all


class TestPipelineTests(unittest.TestCase):
    def test_captured_command_failure_prints_diagnostics(self) -> None:
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr), contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaises(subprocess.CalledProcessError):
                test_all.run_command_capture(
                    [sys.executable, "-c", "import sys; print('linker detail', file=sys.stderr); sys.exit(1)"],
                    cwd=Path.cwd(),
                )
        self.assertIn("linker detail", stderr.getvalue())

    def test_missing_std_is_a_failure_when_its_suite_is_enabled(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            taro = root / "dist/bin/taro"
            taro.parent.mkdir(parents=True)
            taro.touch()
            with (
                patch.object(test_all, "__file__", str(root / "development/scripts/test_all.py")),
                patch.object(test_all.sys, "argv", [
                    "test_all.py", "--skip-cargo-tests", "--skip-build-dist",
                    "--skip-compile-std", "--skip-bitcode-smoke", "--skip-lto-smoke",
                    "--skip-language-tests",
                ]),
                patch.object(test_all, "run_command"),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                self.assertEqual(test_all.main(), 1)


if __name__ == "__main__":
    unittest.main()
