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
    def test_malformed_directives_are_errors(self) -> None:
        for directive in (
            '// STDIN: "unfinished',
            '// STDIN: 3',
            '// EXPECT_EXIT: nope',
            '// EXPECT_STDERR_COUNT: nope panic',
            '// EXPECT_STDERR_COUNT: -1 panic',
            '// EXPECT_STDOUT_CONTAINS:',
            '// ENV: MISSING_EQUALS',
            '// ARGS: "unfinished',
            '// PACKAGE: ../outside',
            '// CHECK_ONLY\n// TEST',
            '// CHECK_ONLY: x',
            '// TEST:',
            '// OVERFLOW_CHECKS: true',
            '// ARGS',
            '// ENV',
        ):
            with self.subTest(directive=directive), tempfile.TemporaryDirectory() as directory:
                source = Path(directory) / "case.tr"
                source.write_text(directive + "\n", encoding="utf-8")
                with self.assertRaises(ValueError):
                    parse_test_directives(source)

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


class LanguageTestOracleTests(unittest.TestCase):
    def setUp(self) -> None:
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.root = Path(directory.name)
        self.sources = self.root / "sources"
        self.outputs = self.root / "outputs"
        self.env = TestEnvironment(self.root / "scratch", Path("taro"), self.root, self.root / "std")
        for name, value in (("SOURCE_FILES_DIR", self.sources), ("OUTPUTS_DIR", self.outputs)):
            patcher = patch.object(language_tests, name, value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def run_case(self, name: str, *, stdout="", stderr="", exit_code=0, directives=""):
        source = self.sources / name
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(directives, encoding="utf-8")
        with patch.object(language_tests.subprocess, "run", return_value=
                          subprocess.CompletedProcess([], exit_code, stdout, stderr)):
            return run_test(source, self.env, "debug", None)

    def test_missing_valid_snapshot_means_empty_stdout_without_writing(self) -> None:
        self.assertTrue(self.run_case("valid/empty.tr")[0])
        self.assertFalse(self.run_case("valid/unexpected.tr", stdout="unexpected\n")[0])
        self.assertFalse(self.outputs.exists())

    def test_invalid_case_requires_an_existing_diagnostic_snapshot(self) -> None:
        self.assertFalse(self.run_case("invalid/broken.tr", stderr="error: broken\n", exit_code=1)[0])
        self.assertFalse(self.outputs.exists())

    def test_valid_filename_containing_invalid_does_not_change_expectations(self) -> None:
        self.assertTrue(self.run_case("valid/invalid_utf8.tr")[0])

    def test_comment_prefix_does_not_disable_output_comparison(self) -> None:
        self.assertFalse(self.run_case(
            "valid/comment.tr", stdout="unexpected\n",
            directives="// TESTING ordinary behavior\n",
        )[0])

    def test_failed_bootstrap_cleans_its_temporary_directory(self) -> None:
        with (
            patch.object(tempfile, "tempdir", str(self.root)),
            patch.object(language_tests.subprocess, "run", side_effect=subprocess.CalledProcessError(1, [])),
            self.assertRaises(SystemExit),
        ):
            with language_tests.setup_test_environment(True):
                self.fail("bootstrap must fail")
        self.assertEqual(list(self.root.iterdir()), [])

    def test_invalid_cases_enforce_supplemental_assertions(self) -> None:
        snapshot = self.outputs / "invalid/broken.out"
        snapshot.parent.mkdir(parents=True)
        snapshot.write_text("error: broken\n", encoding="utf-8")
        self.assertFalse(self.run_case(
            "invalid/broken.tr", stderr="error: broken\n", exit_code=1,
            directives="// EXPECT_STDERR_NOT_CONTAINS: broken\n",
        )[0])

    def test_invalid_cases_honor_explicit_exit_codes(self) -> None:
        snapshot = self.outputs / "invalid/broken.out"
        snapshot.parent.mkdir(parents=True)
        snapshot.write_text("error: broken\n", encoding="utf-8")
        for expected, passes in ((1, True), (2, False)):
            with self.subTest(expected=expected):
                self.assertEqual(self.run_case(
                    "invalid/broken.tr", stderr="error: broken\n", exit_code=1,
                    directives=f"// EXPECT_EXIT: {expected}\n",
                )[0], passes)


if __name__ == "__main__":
    unittest.main()
