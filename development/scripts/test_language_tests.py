#!/usr/bin/env python3
"""Regression tests for language-test directives."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch

import language_tests
from language_tests import TestEnvironment, parse_test_directives, run_test


def completed_process(command, returncode, stdout, stderr):
    """Model Popen's result without starting a compiler or child process."""
    return Mock(returncode=returncode, communicate=Mock(return_value=(stdout, stderr)))


class LanguageTestDirectiveTests(unittest.TestCase):
    def test_repository_codegen_matrix_references_live_fixtures(self) -> None:
        root = Path(__file__).resolve().parents[2]
        self.assertTrue(language_tests.load_test_manifest(root / "language_tests/codegen_matrix.txt"))

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
            '// VET: invalid',
            '// VET\n// TEST',
            '// OVERFLOW_CHECKS: true',
            '// RUN_TWICE: yes',
            '// ARGS',
            '// ENV',
        ):
            with self.subTest(directive=directive), tempfile.TemporaryDirectory() as directory:
                source = Path(directory) / "case.tr"
                source.write_text(directive + "\n", encoding="utf-8")
                with self.assertRaises(ValueError):
                    parse_test_directives(source)

    def test_vet_directive_selects_analysis_command(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "vet.tr"
            source.write_text("// VET\nfunc main() {}\n", encoding="utf-8")
            self.assertEqual(parse_test_directives(source)["command"], "vet")

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
                    patch.object(language_tests.subprocess, "Popen") as run,
                ):
                    run.return_value = completed_process([], 0, "", "")
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
                        return completed_process(command, exit_code, "ok\n", "")

                    with (
                        patch.object(language_tests, "SOURCE_FILES_DIR", root),
                        patch.object(language_tests, "OUTPUTS_DIR", outputs),
                        patch.object(
                            language_tests.subprocess, "Popen", side_effect=compile_and_run
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
        with patch.object(language_tests.subprocess, "Popen", return_value=
                          completed_process([], exit_code, stdout, stderr)):
            return run_test(source, self.env, "debug", None)

    def test_compiler_temp_files_stay_inside_the_run_directory(self) -> None:
        source = self.sources / "valid/cache.tr"
        source.parent.mkdir(parents=True)
        source.write_text("", encoding="utf-8")
        with patch.object(language_tests.subprocess, "Popen", return_value=
                          completed_process([], 0, "", "")) as run:
            run_test(source, self.env, "debug", None)
        temp = Path(run.call_args.kwargs["env"]["TMPDIR"])
        self.assertTrue(temp.is_dir())
        self.assertEqual(temp.parent, self.env.temp_dir)

    def test_timeout_kills_the_process_group_and_reaps_the_compiler(self) -> None:
        source = self.sources / "valid/hung.tr"
        source.parent.mkdir(parents=True)
        source.write_text("", encoding="utf-8")
        process = Mock(pid=12345)
        process.communicate.side_effect = [
            subprocess.TimeoutExpired("taro", 1), ("partial output", "")
        ]
        with (
            patch.object(language_tests.subprocess, "Popen", return_value=process) as spawn,
            patch.object(language_tests.os, "killpg") as kill_group,
        ):
            passed, message, details = run_test(source, self.env, "debug", None)
        self.assertFalse(passed)
        self.assertIn("Timed out", message)
        self.assertEqual(details["stdout"], "partial output")
        self.assertTrue(spawn.call_args.kwargs["start_new_session"])
        kill_group.assert_called_once_with(process.pid, language_tests.signal.SIGKILL)
        self.assertEqual(process.communicate.call_count, 2)

    def test_missing_valid_snapshot_means_empty_stdout_without_writing(self) -> None:
        self.assertTrue(self.run_case("valid/empty.tr")[0])
        self.assertFalse(self.run_case("valid/unexpected.tr", stdout="unexpected\n")[0])
        self.assertFalse(self.outputs.exists())

    def test_invalid_case_requires_an_existing_diagnostic_snapshot(self) -> None:
        self.assertFalse(self.run_case("invalid/broken.tr", stderr="error: broken\n", exit_code=1)[0])
        self.assertFalse(self.outputs.exists())

    def test_invalid_snapshot_normalizes_only_the_active_std_location(self) -> None:
        self.env = TestEnvironment(
            self.env.temp_dir, self.env.compiler_path, self.env.taro_home,
            self.root / "current-sdk/std",
        )
        snapshot = self.outputs / "invalid/broken.out"
        snapshot.parent.mkdir(parents=True)
        snapshot.write_text(
            "error: broken\n -> std/src/definition.tr:1:0\n\tdeclaration\n",
            encoding="utf-8",
        )
        for root, passes in (("current-sdk/std", True), ("previous-sdk/std", False)):
            with self.subTest(root=root), patch.object(language_tests, "PROJECT_ROOT", self.root):
                stderr = f"error: broken\n -> {root}/src/definition.tr:1:0\n\tdeclaration\n"
                self.assertEqual(
                    self.run_case("invalid/broken.tr", stderr=stderr, exit_code=1)[0],
                    passes,
                )

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

    def test_run_twice_checks_the_second_run_and_requires_reuse(self) -> None:
        source = self.sources / "valid/twice.tr"
        source.parent.mkdir(parents=True)
        source.write_text(
            "// RUN_TWICE\n// EXPECT_STDERR_CONTAINS: replayed\n", encoding="utf-8"
        )
        for second, passes in (
            ("Reusing (metadata) - twice\nwarning: replayed\n", True),
            ("Compiling - twice\nwarning: replayed\n", False),
            ("Reusing (metadata) - twice\n", False),
        ):
            with self.subTest(second=second), patch.object(
                language_tests.subprocess, "Popen", side_effect=[
                    completed_process([], 0, "", "Compiling - twice\nwarning: replayed\n"),
                    completed_process([], 0, "", second),
                ],
            ) as run:
                self.assertEqual(run_test(source, self.env, "debug", None)[0], passes)
                self.assertEqual(run.call_count, 2)
                first, again = run.call_args_list
                self.assertEqual(first.kwargs["env"]["TMPDIR"], again.kwargs["env"]["TMPDIR"])

    def test_nonzero_expectation_accepts_failure_status_and_signals_only(self) -> None:
        for code in (1, 2, -6, 134, 0):
            with self.subTest(code=code):
                self.assertEqual(self.run_case(
                    "valid/fatal.tr", exit_code=code,
                    directives="// EXPECT_EXIT: nonzero\n",
                )[0], code != 0)


class LanguageTestRunTests(unittest.TestCase):
    def test_every_failure_is_reported_in_each_profile(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            sources = Path(directory)
            tests = [sources / "valid" / name for name in ["passed.tr", "failed.tr"]]
            for profile in ("debug", "release"):
                with (
                    self.subTest(profile=profile),
                    patch.object(language_tests, "SOURCE_FILES_DIR", sources),
                    patch.object(language_tests, "run_test", side_effect=lambda path, *_:
                                 (path.stem == "passed", "Unexpected exit code", None)),
                    patch("builtins.print"),
                ):
                    passed, failures = language_tests.run_tests(tests, None, 1, profile, None)
                self.assertEqual(passed, 1)
                self.assertEqual(failures, [(Path(profile) / "valid/failed.tr", "Unexpected exit code", None)])


if __name__ == "__main__":
    unittest.main()
