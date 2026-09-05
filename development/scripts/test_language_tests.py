#!/usr/bin/env python3
"""Regression tests for language-test directives."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import language_tests
from language_tests import TestEnvironment, parse_test_directives, run_test


class LanguageTestDirectiveTests(unittest.TestCase):
    def test_stdin_is_decoded_from_a_json_string(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "stdin.tr"
            source.write_text('// STDIN: "first line\\nsecond line\\n"\n', encoding="utf-8")

            directives = parse_test_directives(source)

            self.assertEqual(directives["stdin"], "first line\nsecond line\n")

    def test_checked_overflow_is_explicit_in_both_profiles(self) -> None:
        for profile in ("debug", "release"):
            with self.subTest(profile=profile), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                source = root / "valid" / "overflow.tr"
                source.parent.mkdir()
                source.write_text("// TEST\n// OVERFLOW_CHECKS\n", encoding="utf-8")
                env = TestEnvironment(root / "scratch", Path("taro"), root, root / "std")
                with (
                    patch.object(language_tests, "SOURCE_FILES_DIR", root),
                    patch.object(language_tests, "OUTPUTS_DIR", root / "outputs"),
                    patch.object(language_tests.subprocess, "run") as run,
                ):
                    run.return_value = subprocess.CompletedProcess([], 0, "", "")
                    self.assertTrue(run_test(source, env, profile, None)[0])
                    self.assertIn("--overflow-checks", run.call_args.args[0])

    def test_generated_artifacts_are_cleaned_on_success_and_failure(self) -> None:
        for directive in ("// EXPECT_STDOUT_CONTAINS: ok", "// TEST", "// BENCH"):
            for exit_code in (0, 1):
                with (
                    self.subTest(directive=directive, exit_code=exit_code),
                    tempfile.TemporaryDirectory() as directory,
                ):
                    root = Path(directory)
                    source = root / "valid" / "case.tr"
                    source.parent.mkdir()
                    source.write_text(directive + "\n", encoding="utf-8")
                    outputs = root / "outputs"
                    (outputs / "valid").mkdir(parents=True)
                    (outputs / "valid/case.out").write_text("ok\n")
                    env = TestEnvironment(root / "scratch", Path("taro"), root, root / "std")
                    binary = env.temp_dir / "bin/debug/valid/case"

                    def compile_and_run(command, **kwargs):
                        self.assertIn("-o", command)
                        self.assertEqual(Path(command[command.index("-o") + 1]), binary)
                        binary.write_bytes(b"executable")
                        symbols = Path(str(binary) + ".dSYM")
                        symbols.mkdir()
                        (symbols / "debug-data").write_bytes(b"symbols")
                        return subprocess.CompletedProcess(command, exit_code, "ok\n", "")

                    with (
                        patch.object(language_tests, "SOURCE_FILES_DIR", root),
                        patch.object(language_tests, "OUTPUTS_DIR", outputs),
                        patch.object(
                            language_tests.subprocess, "run", side_effect=compile_and_run
                        ),
                    ):
                        self.assertEqual(
                            run_test(source, env, "debug", None)[0], exit_code == 0
                        )
                    self.assertFalse(binary.exists())
                    self.assertFalse(Path(str(binary) + ".dSYM").exists())


if __name__ == "__main__":
    unittest.main()
