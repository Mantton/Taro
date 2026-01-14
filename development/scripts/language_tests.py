import argparse
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# Configuration
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
LANGUAGE_TESTS_DIR = PROJECT_ROOT / "language_tests"
SOURCE_FILES_DIR = LANGUAGE_TESTS_DIR / "source_files"
OUTPUTS_DIR = LANGUAGE_TESTS_DIR / "outputs"
TARO_BIN_CRATE = "taro-bin"

# Global temp directory and compiler path (set during setup)
TEMP_DIR: Path | None = None
COMPILER_PATH: Path | None = None
TARO_HOME: Path | None = None
STD_PATH: Path | None = None


def setup_test_environment():
    """Build the compiler and setup temporary directories."""
    global TEMP_DIR, COMPILER_PATH, TARO_HOME, STD_PATH

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
    TEMP_DIR = Path(tempfile.mkdtemp(prefix="taro_tests_"))
    print(f"Created temp directory: {TEMP_DIR}")

    # Copy the compiler executable to temp directory
    source_bin = PROJECT_ROOT / "target" / "debug" / TARO_BIN_CRATE
    COMPILER_PATH = TEMP_DIR / "taro"
    shutil.copy2(source_bin, COMPILER_PATH)

    # Setup TARO_HOME in temp directory
    TARO_HOME = TEMP_DIR / "taro_home"
    TARO_HOME_LIB = TARO_HOME / "lib"
    TARO_HOME_LIB.mkdir(parents=True, exist_ok=True)

    # Copy runtime to TARO_HOME/lib
    runtime_lib_src = PROJECT_ROOT / "target" / "debug" / "libtaro_runtime.a"
    runtime_lib_dst = TARO_HOME_LIB / "libtaro_runtime.a"
    shutil.copy2(runtime_lib_src, runtime_lib_dst)

    # Standard library path
    STD_PATH = PROJECT_ROOT / "std"

    print(f"Compiler path: {COMPILER_PATH}")
    print(f"TARO_HOME: {TARO_HOME}")
    print(f"STD_PATH: {STD_PATH}")
    print()


def cleanup_test_environment():
    """Clean up temporary directories."""
    global TEMP_DIR
    if TEMP_DIR and TEMP_DIR.exists():
        shutil.rmtree(TEMP_DIR)
        print(f"Cleaned up temp directory: {TEMP_DIR}")


def run_test(file_path: Path):
    """Runs a single test file and compares output."""
    assert TEMP_DIR is not None, "setup_test_environment() must be called first"
    assert COMPILER_PATH is not None, "setup_test_environment() must be called first"
    assert TARO_HOME is not None, "setup_test_environment() must be called first"
    assert STD_PATH is not None, "setup_test_environment() must be called first"

    try:
        # Construct output file path
        relative_path = file_path.relative_to(SOURCE_FILES_DIR)
        output_file_path = OUTPUTS_DIR / relative_path.with_suffix(".out")

        # Determine if this is an "invalid" test (expected to fail compilation)
        is_invalid_test = "invalid" in str(relative_path)

        # Ensure output directory exists
        output_file_path.parent.mkdir(parents=True, exist_ok=True)

        # Output binary path within temp directory
        output_bin = TEMP_DIR / "bin" / file_path.stem
        output_bin.parent.mkdir(parents=True, exist_ok=True)

        cmd = [
            str(COMPILER_PATH),
            "run",
            str(file_path),
            "-o",
            str(output_bin),
            "--std-path",
            str(STD_PATH),
        ]

        env = os.environ.copy()
        env["TARO_HOME"] = str(TARO_HOME)

        # Run process
        result = subprocess.run(
            cmd, capture_output=True, text=True, cwd=PROJECT_ROOT, env=env
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
            error_lines = [line for line in actual_output.split('\n')
                          if line.startswith('error:') or
                             (line.strip().startswith('->')  or line.strip().startswith('^') or
                              (line.strip() and not line.startswith('Compiling')))]
            actual_output = '\n'.join(error_lines).strip() + '\n' if error_lines else ''
        else:
            # For valid tests, we expect compilation to succeed
            if result.returncode != 0:
                return (
                    False,
                    "Runtime error",
                    {
                        "stderr": result.stderr,
                        "stdout": result.stdout,
                    },
                )
            # Only capture stdout for valid test output
            actual_output = result.stdout

        # Check if output file exists
        if not output_file_path.exists():
            print(f"[NEW] Creating output snapshot for: {relative_path}")
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


def main():
    parser = argparse.ArgumentParser(description="Run Taro language tests")
    parser.add_argument(
        "--filter",
        "-f",
        type=str,
        help="Filter tests by name (substring match). E.g., --filter optional_chaining",
    )
    args = parser.parse_args()

    # Setup: build compiler and create temp directories
    setup_test_environment()

    try:
        print(f"Running tests in {SOURCE_FILES_DIR}...")
        if args.filter:
            print(f"Filter: {args.filter}")

        total = 0
        passed = 0
        skipped = 0
        failures: list[tuple[Path, str, dict[str, str] | None]] = []

        # Walk through source files
        for root, _, files in os.walk(SOURCE_FILES_DIR):
            for file in files:
                if file.endswith(".tr"):
                    file_path = Path(root) / file
                    relative_path = file_path.relative_to(SOURCE_FILES_DIR)

                    # Apply filter if specified
                    if args.filter and args.filter not in str(relative_path):
                        skipped += 1
                        continue

                    print(f"Running {relative_path}...", end=" ", flush=True)
                    success, msg, details = run_test(file_path)

                    if success:
                        print("OK")
                        passed += 1
                    else:
                        print()
                        failures.append((relative_path, msg, details))
                    total += 1

        print("-" * 40)
        summary = f"Total: {total}, Passed: {passed}, Failed: {total - passed}"
        if skipped > 0:
            summary += f", Skipped: {skipped}"
        print(summary)
        if failures:
            print("Failures:")
            for failed_path, failed_msg, failed_details in failures:
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
        cleanup_test_environment()


if __name__ == "__main__":
    main()
