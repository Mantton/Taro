import argparse
import concurrent.futures
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any

# Configuration
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
LANGUAGE_TESTS_DIR = PROJECT_ROOT / "language_tests"
SOURCE_FILES_DIR = LANGUAGE_TESTS_DIR / "source_files"
OUTPUTS_DIR = LANGUAGE_TESTS_DIR / "outputs"
PACKAGE_FIXTURES_DIR = LANGUAGE_TESTS_DIR / "package_fixtures"
BUILD_DIST_SCRIPT = PROJECT_ROOT / "development" / "scripts" / "build_dist.py"


@dataclass(frozen=True)
class TestEnvironment:
    temp_dir: Path
    compiler_path: Path
    taro_home: Path
    std_path: Path


TestDetails = dict[str, Any]
TestRunResult = tuple[bool, str, TestDetails | None]


def setup_test_environment(use_release: bool) -> TestEnvironment:
    """Bootstrap a distribution and setup temporary directories."""
    profile = "release" if use_release else "debug"
    print(f"Bootstrapping distribution via build_dist.py ({profile})...")

    # Create temporary directory
    temp_dir = Path(tempfile.mkdtemp(prefix="taro_tests_"))
    print(f"Created temp directory: {temp_dir}")

    dist_dir = temp_dir / "dist"
    bootstrap_cmd = [
        sys.executable,
        str(BUILD_DIST_SCRIPT),
        "--profile",
        profile,
        "--dist-dir",
        str(dist_dir),
        "--std-path",
        str(PROJECT_ROOT / "std"),
    ]
    try:
        subprocess.run(
            bootstrap_cmd,
            cwd=PROJECT_ROOT,
            check=True,
        )
    except subprocess.CalledProcessError as error:
        print("Failed to bootstrap distribution for language tests:")
        sys.exit(error.returncode or 1)

    compiler_path = dist_dir / "bin" / "taro"
    taro_home = dist_dir
    std_path = dist_dir / "std"
    if not compiler_path.exists():
        print(f"Compiler binary missing at {compiler_path}")
        sys.exit(1)

    print(f"Compiler path: {compiler_path}")
    print(f"TARO_HOME: {taro_home}")
    print(f"STD_PATH: {std_path}")
    print()

    return TestEnvironment(
        temp_dir=temp_dir,
        compiler_path=compiler_path,
        taro_home=taro_home,
        std_path=std_path,
    )


def cleanup_test_environment(env: TestEnvironment):
    """Clean up temporary directories."""
    if env.temp_dir.exists():
        shutil.rmtree(env.temp_dir)
        print(f"Cleaned up temp directory: {env.temp_dir}")


def parse_test_directives(file_path: Path) -> dict[str, Any]:
    """Parse directives from the first few lines of a test file.

    Supported directives:
      // TARGET: <triple>          — cross-compile for the given target triple
      // CHECK_ONLY                — compile with `taro check` (no run, no output compare)
      // TEST                      — run with `taro test` instead of `taro run`; passes if exit 0
      // BENCH                     — run a short `taro bench`; passes if exit 0
      // BENCH_RELEASE             — run the short benchmark in its default release/O2 profile
      // OVERFLOW_CHECKS           — enable checked arithmetic in every codegen profile
      // ARGS: <values...>         — forward runtime args to `taro run` after `--`
      // STDIN: <JSON string>       — provide decoded text as the program's stdin
      // ENV: KEY=value …          — set environment variables for compile/run
      // EXPECT_EXIT: <code>       — expect the given exit code (default 0)
      // EXPECT_STDOUT_CONTAINS: … — assert this substring appears in stdout
      // EXPECT_STDERR_CONTAINS: … — assert this substring appears in stderr
      // EXPECT_STDERR_NOT_CONTAINS: … — assert this substring is absent from stderr
      // EXPECT_STDERR_COUNT: <n> <substring> — assert an exact stderr occurrence count
      // PACKAGE: <fixture>        — run package_fixtures/<fixture>/app
    """
    result = {
        "target": None,
        "check_only": False,
        "run_as_test": False,
        "run_as_bench": False,
        "bench_release": False,
        "overflow_checks": False,
        "args": [],
        "stdin": None,
        "env": {},
        "expect_exit": None,
        "expect_stdout_contains": [],
        "expect_stderr_contains": [],
        "expect_stderr_not_contains": [],
        "expect_stderr_counts": [],
        "package_fixture": None,
    }
    try:
        with open(file_path, "r") as f:
            for _ in range(30):  # Check first lines for directives
                line = f.readline()
                if not line:
                    break
                line = line.strip()
                if line.startswith("// TARGET:"):
                    result["target"] = line[len("// TARGET:") :].strip()
                elif line.startswith("// CHECK_ONLY"):
                    result["check_only"] = True
                elif line.startswith("// TEST"):
                    result["run_as_test"] = True
                elif line == "// OVERFLOW_CHECKS":
                    result["overflow_checks"] = True
                elif line.startswith("// BENCH_RELEASE"):
                    result["run_as_bench"] = True
                    result["bench_release"] = True
                elif line.startswith("// BENCH"):
                    result["run_as_bench"] = True
                elif line.startswith("// ARGS:"):
                    values = line[len("// ARGS:") :].strip()
                    result["args"] = shlex.split(values)
                elif line.startswith("// STDIN:"):
                    value = line[len("// STDIN:") :].strip()
                    try:
                        decoded = json.loads(value)
                    except json.JSONDecodeError:
                        continue
                    if isinstance(decoded, str):
                        result["stdin"] = decoded
                elif line.startswith("// ENV:"):
                    values = shlex.split(line[len("// ENV:") :].strip())
                    for value in values:
                        key, separator, env_value = value.partition("=")
                        if separator and key:
                            result["env"][key] = env_value
                elif line.startswith("// EXPECT_EXIT:"):
                    code = line[len("// EXPECT_EXIT:") :].strip()
                    try:
                        result["expect_exit"] = int(code)
                    except ValueError:
                        pass
                elif line.startswith("// EXPECT_STDOUT_CONTAINS:"):
                    needle = line[len("// EXPECT_STDOUT_CONTAINS:") :].strip()
                    if needle:
                        result["expect_stdout_contains"].append(needle)
                elif line.startswith("// EXPECT_STDERR_CONTAINS:"):
                    needle = line[len("// EXPECT_STDERR_CONTAINS:") :].strip()
                    if needle:
                        result["expect_stderr_contains"].append(needle)
                elif line.startswith("// EXPECT_STDERR_NOT_CONTAINS:"):
                    needle = line[len("// EXPECT_STDERR_NOT_CONTAINS:") :].strip()
                    if needle:
                        result["expect_stderr_not_contains"].append(needle)
                elif line.startswith("// EXPECT_STDERR_COUNT:"):
                    value = line[len("// EXPECT_STDERR_COUNT:") :].strip()
                    count_text, separator, needle = value.partition(" ")
                    if separator and needle.strip():
                        try:
                            result["expect_stderr_counts"].append(
                                (int(count_text), needle.strip())
                            )
                        except ValueError:
                            pass
                elif line.startswith("// PACKAGE:"):
                    fixture = line[len("// PACKAGE:") :].strip()
                    if fixture:
                        result["package_fixture"] = fixture
    except Exception:
        pass
    return result


def run_test(
    file_path: Path,
    env: TestEnvironment,
    codegen_profile: str,
    opt_level: str | None,
) -> TestRunResult:
    """Runs a single test file and compares output."""
    output_bin: Path | None = None
    try:
        # Construct output file path
        relative_path = file_path.relative_to(SOURCE_FILES_DIR)
        output_file_path = OUTPUTS_DIR / relative_path.with_suffix(".out")

        # Determine if this is an "invalid" test (expected to fail compilation)
        is_invalid_test = "invalid" in str(relative_path)

        # Ensure output directory exists
        output_file_path.parent.mkdir(parents=True, exist_ok=True)

        # Output binary path within temp directory
        codegen_variant = codegen_profile
        if opt_level is not None:
            codegen_variant = f"{codegen_profile}-O{opt_level}"
        output_bin = env.temp_dir / "bin" / codegen_variant / relative_path.with_suffix("")
        output_bin.parent.mkdir(parents=True, exist_ok=True)

        # Parse test directives (TARGET, CHECK_ONLY, TEST, …)
        directives = parse_test_directives(file_path)
        target_triple = directives["target"]
        is_check_only = directives["check_only"]
        is_run_as_test = directives["run_as_test"]
        is_run_as_bench = directives["run_as_bench"]
        is_bench_release = directives["bench_release"]
        program_args = directives["args"]
        program_stdin = directives["stdin"]
        environment = directives["env"]
        expected_exit = directives["expect_exit"]
        expected_stdout_contains = directives["expect_stdout_contains"]
        expected_stderr_contains = directives["expect_stderr_contains"]
        expected_stderr_not_contains = directives["expect_stderr_not_contains"]
        expected_stderr_counts = directives["expect_stderr_counts"]
        package_fixture = directives["package_fixture"]

        compile_input = file_path
        if package_fixture:
            fixture_source = PACKAGE_FIXTURES_DIR / package_fixture
            fixture_copy = (
                env.temp_dir
                / "package_fixtures"
                / codegen_variant
                / relative_path.stem
            )
            if not fixture_source.is_dir():
                return False, "Unknown package fixture", {"fixture": str(fixture_source)}
            shutil.copytree(fixture_source, fixture_copy)
            compile_input = fixture_copy / "app"

        # Choose sub-command:
        #   "check"  — CHECK_ONLY: type-check only, no binary produced
        #   "test"   — TEST: compile & run as a test binary (exit 0 = all pass)
        #   "bench"  — BENCH: compile & run a bounded benchmark smoke test
        #   "run"    — default: compile & run normally
        if is_check_only:
            command = "check"
        elif is_run_as_test:
            command = "test"
        elif is_run_as_bench:
            command = "bench"
        else:
            command = "run"

        cmd = [
            str(env.compiler_path),
            command,
            str(compile_input),
            "--std-path",
            str(env.std_path),
        ]

        # All executable modes use per-case temporary paths, including test/bench.
        if command != "check":
            cmd.extend(["-o", str(output_bin)])

        # Add --target flag if specified in test file
        if target_triple:
            cmd.extend(["--target", target_triple])

        if codegen_profile == "release":
            cmd.append("--release")
        elif is_run_as_bench and not is_bench_release:
            # `taro bench` defaults to release/O2; preserve the language-test
            # matrix's requested debug profile when it asks for one.
            cmd.append("--debug")
        if opt_level is not None:
            cmd.append(f"-O{opt_level}")
        if directives["overflow_checks"]:
            cmd.append("--overflow-checks")

        if is_run_as_bench:
            # Keep the regression in the normal language suite without adding
            # the production benchmark defaults to every test run.
            cmd.extend(
                [
                    "--warmup",
                    "0ms",
                    "--time",
                    "1ms",
                    "--samples",
                    "2",
                    "--timeout",
                    "10s",
                    "--format",
                    "json",
                ]
            )

        if program_args:
            if command != "run":
                return (
                    False,
                    "ARGS directive only supports `taro run` tests",
                    {"args": program_args, "command": command},
                )
            cmd.append("--")
            cmd.extend(program_args)

        process_env = os.environ.copy()
        process_env["TARO_HOME"] = str(env.taro_home)
        process_env.update(environment)

        # Run process
        result = subprocess.run(
            cmd,
            input=program_stdin,
            capture_output=True,
            text=True,
            cwd=PROJECT_ROOT,
            env=process_env,
        )

        if is_invalid_test:
            # For invalid tests, we expect compilation to fail
            if result.returncode == 0:
                return (
                    False,
                    "Expected compilation to fail",
                    {"stdout": result.stdout, "stderr": result.stderr},
                )

            # For invalid tests, compare stderr (error output) against expected
            actual_output = result.stderr

            # Normalize the error output: extract just the error lines
            # (skip compilation progress messages like "Compiling – std")
            error_lines = []
            for line in actual_output.split("\n"):
                stripped = line.strip()
                if not stripped or line.startswith("Compiling"):
                    continue
                # Rust panic output may include per-run thread IDs; normalize to keep snapshots stable.
                line = re.sub(r"thread 'main' \(\d+\)", "thread 'main' (<pid>)", line)
                error_lines.append(line)
            actual_output = "\n".join(error_lines).strip() + "\n" if error_lines else ""
        else:
            # For valid tests, default runtime exit is 0 unless overridden by directive.
            expected_code = 0 if expected_exit is None else expected_exit
            if result.returncode != expected_code:
                return (
                    False,
                    "Compilation error" if is_check_only else "Runtime error",
                    {
                        "stderr": result.stderr,
                        "stdout": result.stdout,
                        "expected_exit": expected_code,
                        "actual_exit": result.returncode,
                    },
                )

            for needle in expected_stdout_contains:
                if needle not in result.stdout:
                    return (
                        False,
                        "Missing expected stdout fragment",
                        {
                            "stdout": result.stdout,
                            "missing": needle,
                        },
                    )

            for needle in expected_stderr_contains:
                if needle not in result.stderr:
                    return (
                        False,
                        "Missing expected stderr fragment",
                        {
                            "stderr": result.stderr,
                            "missing": needle,
                        },
                    )
            for needle in expected_stderr_not_contains:
                if needle in result.stderr:
                    return (
                        False,
                        "Unexpected stderr fragment",
                        {
                            "stderr": result.stderr,
                            "unexpected": needle,
                        },
                    )
            for expected_count, needle in expected_stderr_counts:
                actual_count = result.stderr.count(needle)
                if actual_count != expected_count:
                    return (
                        False,
                        "Unexpected stderr fragment count",
                        {
                            "stderr": result.stderr,
                            "fragment": needle,
                            "expected_count": expected_count,
                            "actual_count": actual_count,
                        },
                    )
            # CHECK_ONLY and TEST files have no output snapshot to compare —
            # a clean exit code is the entire success criterion.
            if is_check_only or is_run_as_test or is_run_as_bench:
                return True, "Passed", None
            # Only capture stdout for normal run output comparison
            actual_output = result.stdout

        # Check if output file exists
        if not output_file_path.exists():
            with open(output_file_path, "w") as f:
                f.write(actual_output)
            return True, "Created snapshot", None

        # Compare output
        with open(output_file_path, "r") as f:
            expected_output = f.read()

        if actual_output != expected_output:
            return (
                False,
                "Output mismatch",
                {
                    "expected": expected_output,
                    "actual": actual_output,
                },
            )

        return True, "Passed", None

    except Exception as e:
        return False, "Exception", {"error": str(e)}
    finally:
        # Keeping every linked binary and dSYM until the whole matrix finishes
        # can consume many gigabytes. Diagnostics are already captured above.
        if output_bin is not None:
            output_bin.unlink(missing_ok=True)
            shutil.rmtree(str(output_bin) + ".dSYM", ignore_errors=True)


def load_test_manifest(manifest_path: Path) -> set[Path]:
    """Load checked source-file paths relative to language_tests/source_files."""
    if not manifest_path.is_file():
        raise ValueError(f"test manifest does not exist: {manifest_path}")

    selected: set[Path] = set()
    for line_number, raw_line in enumerate(
        manifest_path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        entry = raw_line.partition("#")[0].strip()
        if not entry:
            continue
        relative_path = Path(entry)
        if relative_path.is_absolute() or ".." in relative_path.parts:
            raise ValueError(
                f"{manifest_path}:{line_number}: path must stay under "
                f"{SOURCE_FILES_DIR}: {entry}"
            )
        source_path = SOURCE_FILES_DIR / relative_path
        if source_path.suffix != ".tr" or not source_path.is_file():
            raise ValueError(
                f"{manifest_path}:{line_number}: unknown Taro test source: {entry}"
            )
        selected.add(source_path)

    if not selected:
        raise ValueError(f"test manifest has no source entries: {manifest_path}")
    return selected


def discover_test_files(
    test_filter: str | None, manifest_path: Path | None = None
) -> tuple[list[Path], int]:
    """Discover tests, then apply an optional manifest and substring filter."""
    all_tests = sorted(
        [path for path in SOURCE_FILES_DIR.rglob("*.tr") if path.is_file()],
        key=lambda path: str(path.relative_to(SOURCE_FILES_DIR)),
    )
    selected_set = set(all_tests)
    if manifest_path is not None:
        selected_set &= load_test_manifest(manifest_path)

    if test_filter:
        selected_set = {
            path
            for path in selected_set
            if test_filter in str(path.relative_to(SOURCE_FILES_DIR))
        }

    selected = [path for path in all_tests if path in selected_set]
    skipped = len(all_tests) - len(selected)
    return selected, skipped


def positive_int(value: str) -> int:
    try:
        parsed = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"invalid int value: {value}") from error
    if parsed < 1:
        raise argparse.ArgumentTypeError("--jobs must be >= 1")
    return parsed


def resolve_jobs(requested_jobs: int | None, selected_tests: int) -> int:
    if requested_jobs is not None:
        return requested_jobs
    if selected_tests == 0:
        return 1
    cpu_count = max(1, os.cpu_count() or 1)
    return min(selected_tests, cpu_count)


def format_elapsed(seconds: float) -> str:
    total_seconds = max(0.0, seconds)
    minutes, secs = divmod(total_seconds, 60)
    hours, mins = divmod(int(minutes), 60)
    if hours > 0:
        return f"{hours:02d}:{mins:02d}:{secs:05.2f}"
    return f"{mins:02d}:{secs:05.2f}"


def run_tests_serial(
    test_files: list[Path],
    env: TestEnvironment,
    codegen_profile: str,
    opt_level: str | None,
) -> tuple[int, list[tuple[Path, str, TestDetails | None]]]:
    passed = 0
    failures: list[tuple[Path, str, TestDetails | None]] = []

    for file_path in test_files:
        relative_path = file_path.relative_to(SOURCE_FILES_DIR)
        codegen_variant = (
            codegen_profile if opt_level is None else f"{codegen_profile}-O{opt_level}"
        )
        display_path = Path(codegen_variant) / relative_path
        print(f"Running {display_path}...", end=" ", flush=True)
        success, msg, details = run_test(file_path, env, codegen_profile, opt_level)

        if success:
            print("OK")
            passed += 1
        else:
            print()
            failures.append((display_path, msg, details))

    return passed, failures


def run_tests_parallel(
    test_files: list[Path],
    env: TestEnvironment,
    jobs: int,
    codegen_profile: str,
    opt_level: str | None,
) -> tuple[int, list[tuple[Path, str, TestDetails | None]]]:
    passed = 0
    failures: list[tuple[Path, str, TestDetails | None]] = []

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        future_to_path = {
            executor.submit(
                run_test, file_path, env, codegen_profile, opt_level
            ): file_path
            for file_path in test_files
        }
        for future in concurrent.futures.as_completed(future_to_path):
            file_path = future_to_path[future]
            relative_path = file_path.relative_to(SOURCE_FILES_DIR)
            codegen_variant = (
                codegen_profile
                if opt_level is None
                else f"{codegen_profile}-O{opt_level}"
            )
            display_path = Path(codegen_variant) / relative_path
            try:
                success, msg, details = future.result()
            except (
                Exception
            ) as error:  # Defensive fallback; run_test also catches internally.
                success = False
                msg = "Exception"
                details = {"error": str(error)}

            if success:
                print(f"Running {display_path}... OK")
                passed += 1
            else:
                print(f"Running {display_path}...")
                failures.append((display_path, msg, details))

    return passed, failures


def main():
    start_time = time.perf_counter()
    parser = argparse.ArgumentParser(description="Run Taro language tests")
    parser.add_argument(
        "--filter",
        "-f",
        type=str,
        help="Filter tests by name (substring match). E.g., --filter optional_chaining",
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        help=(
            "Run only test paths listed in this manifest. Entries are relative to "
            "language_tests/source_files; blank lines and # comments are ignored."
        ),
    )
    parser.add_argument(
        "--codegen-profile",
        choices=["debug", "release", "both"],
        default="debug",
        help="Generated-program profile(s) to test (default: debug).",
    )
    parser.add_argument(
        "--opt-level",
        choices=["0", "1", "2", "3", "s", "z"],
        help="Pass an explicit LLVM optimization level to every generated program.",
    )
    parser.add_argument(
        "--jobs",
        "-j",
        type=positive_int,
        help="Number of concurrent workers. Defaults to min(selected_tests, CPU count). Use --jobs 1 for serial mode.",
    )
    profile_group = parser.add_mutually_exclusive_group()
    profile_group.add_argument(
        "--release",
        dest="release",
        action="store_true",
        default=True,
        help="Build and run tests with release compiler/runtime binaries (default).",
    )
    profile_group.add_argument(
        "--debug",
        dest="release",
        action="store_false",
        help="Build and run tests with debug compiler/runtime binaries.",
    )
    args = parser.parse_args()

    try:
        test_files, skipped = discover_test_files(args.filter, args.manifest)
    except ValueError as error:
        parser.error(str(error))

    codegen_profiles = (
        ["debug", "release"]
        if args.codegen_profile == "both"
        else [args.codegen_profile]
    )

    # Setup: build compiler and create temp directories
    env = setup_test_environment(args.release)

    try:
        print(f"Running tests in {SOURCE_FILES_DIR}...")
        if args.filter:
            print(f"Filter: {args.filter}")
        if args.manifest:
            print(f"Manifest: {args.manifest.resolve()}")
        print(f"Codegen profiles: {', '.join(codegen_profiles)}")
        if args.opt_level is not None:
            print(f"Optimization level: O{args.opt_level}")
        total = len(test_files) * len(codegen_profiles)
        jobs = resolve_jobs(args.jobs, total)
        if total > 0:
            print(f"Jobs: {jobs}")

        passed = 0
        failures: list[tuple[Path, str, TestDetails | None]] = []
        for codegen_profile in codegen_profiles:
            if jobs == 1:
                profile_passed, profile_failures = run_tests_serial(
                    test_files, env, codegen_profile, args.opt_level
                )
            else:
                profile_passed, profile_failures = run_tests_parallel(
                    test_files, env, jobs, codegen_profile, args.opt_level
                )
            passed += profile_passed
            failures.extend(profile_failures)

        print("-" * 40)
        elapsed = format_elapsed(time.perf_counter() - start_time)
        summary = f"Total: {total}, Passed: {passed}, Failed: {total - passed}"
        if skipped > 0:
            summary += f", Skipped: {skipped}"
        summary += f", Elapsed: {elapsed}"
        print(summary)
        if failures:
            print("Failures:")
            for failed_path, failed_msg, failed_details in sorted(
                failures,
                key=lambda item: str(item[0]),
            ):
                print(f" - {failed_path}: {failed_msg}")
                if not failed_details:
                    continue
                stderr = failed_details.get("stderr")
                stdout = failed_details.get("stdout")
                expected = failed_details.get("expected")
                actual = failed_details.get("actual")
                error = failed_details.get("error")
                missing = failed_details.get("missing")
                if missing:
                    print("--- Missing ---")
                    print(missing)
                if stderr:
                    print("--- Stderr ---")
                    print(stderr)
                if stdout:
                    print("--- Stdout ---")
                    print(stdout)
                if expected is not None:
                    print("--- Expected ---")
                    print(expected)
                if actual is not None:
                    print("--- Actual ---")
                    print(actual)
                if error:
                    print("--- Error ---")
                    print(error)

        if total != passed:
            sys.exit(1)
    finally:
        cleanup_test_environment(env)


if __name__ == "__main__":
    main()
