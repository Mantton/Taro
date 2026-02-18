import argparse
import concurrent.futures
import os
import re
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
TARO_BIN_CRATE = "taro-bin"


@dataclass(frozen=True)
class TestEnvironment:
    temp_dir: Path
    compiler_path: Path
    taro_home: Path
    std_path: Path


TestDetails = dict[str, Any]
TestRunResult = tuple[bool, str, TestDetails | None]


def setup_test_environment() -> TestEnvironment:
    """Build the compiler and setup temporary directories."""
    print("Building compiler...")

    # Build the compiler in debug mode for faster test execution
    build_result = subprocess.run(
        ["cargo", "build", "-p", TARO_BIN_CRATE],
        capture_output=True,
        text=True,
        cwd=PROJECT_ROOT,
    )

    if build_result.returncode != 0:
        print("Failed to build compiler:")
        print(build_result.stderr)
        sys.exit(1)

    print("Building runtime...")
    runtime_build_result = subprocess.run(
        ["cargo", "build", "-p", "taro-runtime"],
        capture_output=True,
        text=True,
        cwd=PROJECT_ROOT,
    )

    if runtime_build_result.returncode != 0:
        print("Failed to build runtime:")
        print(runtime_build_result.stderr)
        sys.exit(1)

    print("Compiler built successfully.")

    # Create temporary directory
    temp_dir = Path(tempfile.mkdtemp(prefix="taro_tests_"))
    print(f"Created temp directory: {temp_dir}")

    # Copy the compiler executable to temp directory
    source_bin = PROJECT_ROOT / "target" / "debug" / TARO_BIN_CRATE
    compiler_path = temp_dir / "taro"
    shutil.copy2(source_bin, compiler_path)

    # Setup TARO_HOME in temp directory
    taro_home = temp_dir / "taro_home"
    taro_home_lib = taro_home / "lib"
    taro_home_lib.mkdir(parents=True, exist_ok=True)

    # Copy runtime to TARO_HOME/lib
    runtime_lib_src = PROJECT_ROOT / "target" / "debug" / "libtaro_runtime.a"
    runtime_lib_dst = taro_home_lib / "libtaro_runtime.a"
    shutil.copy2(runtime_lib_src, runtime_lib_dst)

    # Standard library path
    std_path = PROJECT_ROOT / "std"

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
      // EXPECT_EXIT: <code>       — expect the given exit code (default 0)
      // EXPECT_STDERR_CONTAINS: … — assert this substring appears in stderr
    """
    result = {
        "target": None,
        "check_only": False,
        "run_as_test": False,
        "expect_exit": None,
        "expect_stderr_contains": [],
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
                elif line.startswith("// EXPECT_EXIT:"):
                    code = line[len("// EXPECT_EXIT:") :].strip()
                    try:
                        result["expect_exit"] = int(code)
                    except ValueError:
                        pass
                elif line.startswith("// EXPECT_STDERR_CONTAINS:"):
                    needle = line[len("// EXPECT_STDERR_CONTAINS:") :].strip()
                    if needle:
                        result["expect_stderr_contains"].append(needle)
    except Exception:
        pass
    return result


def run_test(file_path: Path, env: TestEnvironment) -> TestRunResult:
    """Runs a single test file and compares output."""
    try:
        # Construct output file path
        relative_path = file_path.relative_to(SOURCE_FILES_DIR)
        output_file_path = OUTPUTS_DIR / relative_path.with_suffix(".out")

        # Determine if this is an "invalid" test (expected to fail compilation)
        is_invalid_test = "invalid" in str(relative_path)

        # Ensure output directory exists
        output_file_path.parent.mkdir(parents=True, exist_ok=True)

        # Output binary path within temp directory
        output_bin = env.temp_dir / "bin" / relative_path.with_suffix("")
        output_bin.parent.mkdir(parents=True, exist_ok=True)

        # Parse test directives (TARGET, CHECK_ONLY, TEST, …)
        directives = parse_test_directives(file_path)
        target_triple = directives["target"]
        is_check_only = directives["check_only"]
        is_run_as_test = directives["run_as_test"]
        expected_exit = directives["expect_exit"]
        expected_stderr_contains = directives["expect_stderr_contains"]

        # Choose sub-command:
        #   "check"  — CHECK_ONLY: type-check only, no binary produced
        #   "test"   — TEST: compile & run as a test binary (exit 0 = all pass)
        #   "run"    — default: compile & run normally
        if is_check_only:
            command = "check"
        elif is_run_as_test:
            command = "test"
        else:
            command = "run"

        cmd = [
            str(env.compiler_path),
            command,
            str(file_path),
            "--std-path",
            str(env.std_path),
        ]

        # Add output flag only for run command (check/test handle their own output)
        if command == "run":
            cmd.extend(["-o", str(output_bin)])

        # Add --target flag if specified in test file
        if target_triple:
            cmd.extend(["--target", target_triple])

        process_env = os.environ.copy()
        process_env["TARO_HOME"] = str(env.taro_home)

        # Run process
        result = subprocess.run(
            cmd, capture_output=True, text=True, cwd=PROJECT_ROOT, env=process_env
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
            # CHECK_ONLY and TEST files have no output snapshot to compare —
            # a clean exit code is the entire success criterion.
            if is_check_only or is_run_as_test:
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


def discover_test_files(test_filter: str | None) -> tuple[list[Path], int]:
    """Discover and deterministically order tests, applying filter after discovery."""
    all_tests = sorted(
        [path for path in SOURCE_FILES_DIR.rglob("*.tr") if path.is_file()],
        key=lambda path: str(path.relative_to(SOURCE_FILES_DIR)),
    )
    if not test_filter:
        return all_tests, 0

    selected = [
        path
        for path in all_tests
        if test_filter in str(path.relative_to(SOURCE_FILES_DIR))
    ]
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
    test_files: list[Path], env: TestEnvironment
) -> tuple[int, list[tuple[Path, str, TestDetails | None]]]:
    passed = 0
    failures: list[tuple[Path, str, TestDetails | None]] = []

    for file_path in test_files:
        relative_path = file_path.relative_to(SOURCE_FILES_DIR)
        print(f"Running {relative_path}...", end=" ", flush=True)
        success, msg, details = run_test(file_path, env)

        if success:
            print("OK")
            passed += 1
        else:
            print()
            failures.append((relative_path, msg, details))

    return passed, failures


def run_tests_parallel(
    test_files: list[Path], env: TestEnvironment, jobs: int
) -> tuple[int, list[tuple[Path, str, TestDetails | None]]]:
    passed = 0
    failures: list[tuple[Path, str, TestDetails | None]] = []

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as executor:
        future_to_path = {
            executor.submit(run_test, file_path, env): file_path
            for file_path in test_files
        }
        for future in concurrent.futures.as_completed(future_to_path):
            file_path = future_to_path[future]
            relative_path = file_path.relative_to(SOURCE_FILES_DIR)
            try:
                success, msg, details = future.result()
            except (
                Exception
            ) as error:  # Defensive fallback; run_test also catches internally.
                success = False
                msg = "Exception"
                details = {"error": str(error)}

            if success:
                print(f"Running {relative_path}... OK")
                passed += 1
            else:
                print(f"Running {relative_path}...")
                failures.append((relative_path, msg, details))

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
        "--jobs",
        "-j",
        type=positive_int,
        help="Number of concurrent workers. Defaults to min(selected_tests, CPU count). Use --jobs 1 for serial mode.",
    )
    args = parser.parse_args()

    # Setup: build compiler and create temp directories
    env = setup_test_environment()

    try:
        print(f"Running tests in {SOURCE_FILES_DIR}...")
        if args.filter:
            print(f"Filter: {args.filter}")
        test_files, skipped = discover_test_files(args.filter)
        total = len(test_files)
        jobs = resolve_jobs(args.jobs, total)
        if total > 0:
            print(f"Jobs: {jobs}")

        if jobs == 1:
            passed, failures = run_tests_serial(test_files, env)
        else:
            passed, failures = run_tests_parallel(test_files, env, jobs)

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
                expected = failed_details.get("expected")
                actual = failed_details.get("actual")
                error = failed_details.get("error")
                if stderr:
                    print("--- Stderr ---")
                    print(stderr)
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
