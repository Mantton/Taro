#!/usr/bin/env python3
import argparse
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def positive_int(value: str) -> int:
    try:
        parsed = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError(f"invalid int value: {value}") from error
    if parsed < 1:
        raise argparse.ArgumentTypeError("--jobs must be >= 1")
    return parsed


def format_command(command: list[str]) -> str:
    return " ".join(shlex.quote(part) for part in command)


def run_command(command: list[str], cwd: Path, env: dict[str, str] | None = None) -> None:
    print(f"Running: {format_command(command)}")
    subprocess.run(command, cwd=str(cwd), env=env, check=True)


def run_command_capture(
    command: list[str], cwd: Path, env: dict[str, str] | None = None
) -> subprocess.CompletedProcess[str]:
    print(f"Running: {format_command(command)}")
    completed = subprocess.run(
        command,
        cwd=str(cwd),
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )
    if completed.stdout:
        print(completed.stdout, end="")
    if completed.stderr:
        print(completed.stderr, end="", file=sys.stderr)
    return completed


def print_stage(index: int, total: int, name: str) -> None:
    print()
    print(f"[{index}/{total}] {name}")


def is_llvm_bitcode(contents: bytes) -> bool:
    return contents.startswith(b"BC\xc0\xde") or contents.startswith(
        b"\xde\xc0\x17\x0b"
    )


def file_snapshot(directory: Path) -> dict[str, tuple[int, int]]:
    return {
        path.name: (path.stat().st_size, path.stat().st_mtime_ns)
        for path in sorted(directory.iterdir())
        if path.is_file()
    }


def main() -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(line_buffering=True)
    if hasattr(sys.stderr, "reconfigure"):
        sys.stderr.reconfigure(line_buffering=True)

    parser = argparse.ArgumentParser(description="Run all Taro development checks.")
    parser.add_argument("--jobs", type=positive_int, help="Forwarded to language_tests.py")
    parser.add_argument("--skip-cargo-tests", action="store_true")
    parser.add_argument("--skip-build-dist", action="store_true")
    parser.add_argument("--skip-compile-std", action="store_true")
    parser.add_argument("--skip-bitcode-smoke", action="store_true")
    parser.add_argument("--skip-lto-smoke", action="store_true")
    parser.add_argument("--skip-std-package-tests", action="store_true")
    parser.add_argument("--skip-language-tests", action="store_true")
    args = parser.parse_args()

    script_dir = Path(__file__).resolve().parent
    repo_root = script_dir.parent.parent
    verifiers_root = repo_root / "development" / "verifiers"
    build_script = repo_root / "development" / "scripts" / "build_dist.py"
    language_tests_script = repo_root / "development" / "scripts" / "language_tests.py"
    dist_dir = repo_root / "dist"
    taro_bin = dist_dir / "bin" / "taro"
    std_path = repo_root / "std"
    hello_example = repo_root / "examples" / "hello.tr"
    package_fixture = (
        repo_root / "language_tests" / "package_fixtures" / "default_params"
    )

    stage_count = 8
    current_stage = "startup"

    try:
        current_stage = "development script tests"
        print_stage(1, stage_count, "Development script and Cargo tests")
        run_command(
            [
                sys.executable,
                "-m",
                "unittest",
                "discover",
                "-s",
                str(script_dir),
                "-p",
                "test_*.py",
            ],
            cwd=repo_root,
        )
        # Verifier projects own their protocol tests. Discover each project
        # separately so adding one does not require Python package boilerplate.
        verifier_test_directories = sorted(
            {path.parent for path in verifiers_root.glob("*/test_*.py")}
        )
        for verifier_test_directory in verifier_test_directories:
            run_command(
                [
                    sys.executable,
                    "-m",
                    "unittest",
                    "discover",
                    "-s",
                    str(verifier_test_directory),
                    "-p",
                    "test_*.py",
                ],
                cwd=repo_root,
            )

        current_stage = "cargo tests"
        if args.skip_cargo_tests:
            print("SKIPPED: disabled via --skip-cargo-tests")
        else:
            run_command(["cargo", "test", "--workspace"], cwd=repo_root)

        current_stage = "build dist"
        print_stage(2, stage_count, "Build dist")
        if args.skip_build_dist:
            print("SKIPPED: disabled via --skip-build-dist")
        else:
            run_command(["python3", str(build_script)], cwd=repo_root)

        current_stage = "compile std smoke"
        print_stage(3, stage_count, "Compile std smoke")
        if args.skip_compile_std:
            print("SKIPPED: disabled via --skip-compile-std")
        else:
            if not taro_bin.exists():
                print(
                    f"error: compiler binary not found at {taro_bin}; run without --skip-build-dist first"
                )
                return 1

            env = os.environ.copy()
            env["TARO_HOME"] = str(dist_dir)
            run_command(
                [
                    str(taro_bin),
                    "check",
                    str(hello_example),
                    "--std-path",
                    str(std_path),
                ],
                cwd=repo_root,
                env=env,
            )

        current_stage = "bitcode artifact smoke"
        print_stage(4, stage_count, "LLVM bitcode artifact smoke")
        if args.skip_bitcode_smoke:
            print("SKIPPED: disabled via --skip-bitcode-smoke")
        else:
            if not taro_bin.exists():
                print(
                    f"error: compiler binary not found at {taro_bin}; run without --skip-build-dist first"
                )
                return 1

            env = os.environ.copy()
            env["TARO_HOME"] = str(dist_dir)
            with tempfile.TemporaryDirectory(prefix="taro_bitcode_smoke_") as temp:
                output = Path(temp) / "hello.bc"
                missing_runtime = Path(temp) / "runtime-does-not-exist.a"
                command = [
                    str(taro_bin),
                    "build",
                    str(hello_example),
                    "--std-path",
                    str(std_path),
                    "--emit",
                    "llvm-bc",
                    "--runtime-path",
                    str(missing_runtime),
                    "-o",
                    str(output),
                ]
                run_command([*command, "--no-incremental"], cwd=repo_root, env=env)
                reused = run_command_capture(command, cwd=repo_root, env=env)
                if "Reusing (metadata+bitcode)" not in reused.stderr:
                    raise RuntimeError("second bitcode build did not reuse its cached artifact")
                bitcode = output.read_bytes()
                if not is_llvm_bitcode(bitcode):
                    raise RuntimeError(
                        f"bitcode smoke output has invalid magic: {output}"
                    )

                copied_fixture = Path(temp) / "default_params"
                shutil.copytree(package_fixture, copied_fixture)
                package_output = Path(temp) / "default-params.bc"
                run_command(
                    [
                        str(taro_bin),
                        "build",
                        str(copied_fixture / "app"),
                        "--std-path",
                        str(std_path),
                        "--emit",
                        "llvm-bc",
                        "--runtime-path",
                        str(missing_runtime),
                        "--no-incremental",
                        "-o",
                        str(package_output),
                    ],
                    cwd=repo_root,
                    env=env,
                )
                package_artifacts = list(
                    (copied_fixture / "app" / "target" / "debug" / "objects").glob(
                        "*.bc"
                    )
                )
                native_objects = list(
                    (copied_fixture / "app" / "target" / "debug" / "objects").glob(
                        "*.o"
                    )
                )
                if len(package_artifacts) < 2:
                    raise RuntimeError(
                        "package bitcode build did not retain root and dependency artifacts"
                    )
                if native_objects:
                    raise RuntimeError(
                        "bitcode-only package build unexpectedly emitted native objects"
                    )
                for artifact in [package_output, *package_artifacts]:
                    if not is_llvm_bitcode(artifact.read_bytes()):
                        raise RuntimeError(
                            f"package bitcode artifact has invalid magic: {artifact}"
                        )

        current_stage = "full LTO smoke"
        print_stage(5, stage_count, "Full LTO smoke")
        if args.skip_lto_smoke:
            print("SKIPPED: disabled via --skip-lto-smoke")
        else:
            if not taro_bin.exists():
                print(
                    f"error: compiler binary not found at {taro_bin}; run without --skip-build-dist first"
                )
                return 1

            env = os.environ.copy()
            env["TARO_HOME"] = str(dist_dir)
            with tempfile.TemporaryDirectory(prefix="taro_full_lto_smoke_") as temp:
                copied_fixture = Path(temp) / "default_params"
                shutil.copytree(package_fixture, copied_fixture)
                output = Path(temp) / "default-params-lto"
                command = [
                    str(taro_bin),
                    "build",
                    str(copied_fixture / "app"),
                    "--std-path",
                    str(std_path),
                    "--release",
                    "--lto",
                    "full",
                    "-o",
                    str(output),
                ]
                cold = run_command_capture(
                    [*command, "--no-incremental"], cwd=repo_root, env=env
                )
                if "Full LTO – 2 modules" not in cold.stderr:
                    raise RuntimeError("cold package build did not merge both LTO modules")

                reused = run_command_capture(command, cwd=repo_root, env=env)
                if "Reusing (metadata+bitcode)" not in reused.stderr:
                    raise RuntimeError("second full-LTO build did not reuse package bitcode")
                if "Full LTO – 2 modules" not in reused.stderr:
                    raise RuntimeError("cached package build did not rerun full LTO")

                executed = run_command_capture([str(output)], cwd=repo_root, env=env)
                if "PASS: cross-package closure default" not in executed.stdout:
                    raise RuntimeError("full-LTO executable produced unexpected output")

                object_root = (
                    copied_fixture / "app" / "target" / "release" / "objects"
                )
                bitcode_inputs = list(object_root.glob("*.bc"))
                lto_objects = list(object_root.glob("*.lto.o"))
                pc_metadata_objects = list(object_root.glob("*.pcmeta.o"))
                native_objects = [
                    path
                    for path in object_root.glob("*.o")
                    if not path.name.endswith(".pcmeta.o")
                ]
                stack_map_descriptors = list(object_root.glob("*.lto.stackmaps"))
                if len(bitcode_inputs) != 2:
                    raise RuntimeError(
                        f"full LTO expected two package bitcode inputs, found {len(bitcode_inputs)}"
                    )
                if (
                    len(lto_objects) != 1
                    or native_objects != lto_objects
                    or len(pc_metadata_objects) != 1
                    or len(stack_map_descriptors) != 1
                ):
                    raise RuntimeError(
                        "full LTO did not emit one code object and its PC metadata companions"
                    )
                for artifact in bitcode_inputs:
                    if not is_llvm_bitcode(artifact.read_bytes()):
                        raise RuntimeError(
                            f"full-LTO input has invalid bitcode magic: {artifact}"
                        )

        current_stage = "ThinLTO smoke"
        print_stage(6, stage_count, "ThinLTO cache smoke")
        if args.skip_lto_smoke:
            print("SKIPPED: disabled via --skip-lto-smoke")
        else:
            if not taro_bin.exists():
                print(
                    f"error: compiler binary not found at {taro_bin}; run without --skip-build-dist first"
                )
                return 1

            env = os.environ.copy()
            env["TARO_HOME"] = str(dist_dir)
            with tempfile.TemporaryDirectory(prefix="taro_thin_lto_smoke_") as temp:
                copied_fixture = Path(temp) / "default_params"
                shutil.copytree(package_fixture, copied_fixture)
                output = Path(temp) / "default-params-thin-lto"
                command = [
                    str(taro_bin),
                    "build",
                    str(copied_fixture / "app"),
                    "--std-path",
                    str(std_path),
                    "--release",
                    "--lto",
                    "thin",
                    "-o",
                    str(output),
                ]

                cold = run_command_capture(command, cwd=repo_root, env=env)
                if "Thin LTO – 2 modules, 2 objects" not in cold.stderr:
                    raise RuntimeError(
                        "cold package build did not process both ThinLTO modules"
                    )

                object_root = (
                    copied_fixture / "app" / "target" / "release" / "objects"
                )
                cache_dir = object_root / "thinlto-cache"
                generated_dir = object_root / "thinlto-objects"
                if not cache_dir.is_dir():
                    raise RuntimeError("ThinLTO build did not create its backend cache")
                cache_entries = list(cache_dir.glob("llvmcache-*"))
                cache_entries = [
                    path for path in cache_entries if path.name != "llvmcache.timestamp"
                ]
                if len(cache_entries) != 2:
                    raise RuntimeError(
                        f"ThinLTO expected two backend cache entries, found {len(cache_entries)}"
                    )
                cold_cache = file_snapshot(cache_dir)

                reused = run_command_capture(command, cwd=repo_root, env=env)
                if "Reusing (metadata+bitcode)" not in reused.stderr:
                    raise RuntimeError("second ThinLTO build did not reuse package bitcode")
                if "Thin LTO – 2 modules, 2 objects" not in reused.stderr:
                    raise RuntimeError("cached package build did not rerun ThinLTO")
                if file_snapshot(cache_dir) != cold_cache:
                    raise RuntimeError("cached ThinLTO build rewrote its backend cache")

                uncached = run_command_capture(
                    [*command, "--no-incremental"], cwd=repo_root, env=env
                )
                if "Reusing (metadata+bitcode)" in uncached.stderr:
                    raise RuntimeError("--no-incremental reused package bitcode")
                if "Thin LTO – 2 modules, 2 objects" not in uncached.stderr:
                    raise RuntimeError("--no-incremental did not run ThinLTO")
                if file_snapshot(cache_dir) != cold_cache:
                    raise RuntimeError("--no-incremental modified the ThinLTO cache")

                executed = run_command_capture([str(output)], cwd=repo_root, env=env)
                if "PASS: cross-package closure default" not in executed.stdout:
                    raise RuntimeError("ThinLTO executable produced unexpected output")

                bitcode_inputs = list(object_root.glob("*.bc"))
                generated_pc_metadata = list(generated_dir.glob("*.pcmeta.o"))
                generated_objects = [
                    path
                    for path in generated_dir.glob("*.o")
                    if not path.name.endswith(".pcmeta.o")
                ]
                top_level_objects = list(object_root.glob("*.o"))
                stack_map_descriptors = list(object_root.glob("*.thinlto.stackmaps"))
                if len(bitcode_inputs) != 2:
                    raise RuntimeError(
                        f"ThinLTO expected two package bitcode inputs, found {len(bitcode_inputs)}"
                    )
                if (
                    len(generated_objects) != 2
                    or len(generated_pc_metadata) != 2
                    or len(stack_map_descriptors) != 1
                    or top_level_objects
                ):
                    raise RuntimeError(
                        "ThinLTO did not isolate two code objects and their PC metadata companions"
                    )
                for artifact in bitcode_inputs:
                    if not is_llvm_bitcode(artifact.read_bytes()):
                        raise RuntimeError(
                            f"ThinLTO input has invalid bitcode magic: {artifact}"
                        )

        current_stage = "std package tests"
        print_stage(7, stage_count, "Std package tests")
        if args.skip_std_package_tests:
            print("SKIPPED: disabled via --skip-std-package-tests")
        else:
            if not taro_bin.exists():
                print(
                    f"error: compiler binary not found at {taro_bin}; run without --skip-build-dist first"
                )
                return 1

            if not std_path.exists():
                print(f"SKIPPED: std package directory not found at {std_path}")
            else:
                env = os.environ.copy()
                env["TARO_HOME"] = str(dist_dir)
                run_command(
                    [
                        str(taro_bin),
                        "test",
                        "std",
                        "--std-path",
                        "std",
                    ],
                    cwd=repo_root,
                    env=env,
                )

        current_stage = "language tests"
        print_stage(8, stage_count, "Language tests")
        if args.skip_language_tests:
            print("SKIPPED: disabled via --skip-language-tests")
        else:
            command = ["python3", str(language_tests_script)]
            if args.jobs is not None:
                command.extend(["--jobs", str(args.jobs)])
            run_command(command, cwd=repo_root)

    except subprocess.CalledProcessError as error:
        print()
        print(
            f"error: stage '{current_stage}' failed with exit code {error.returncode}"
        )
        return error.returncode or 1
    except RuntimeError as error:
        print()
        print(f"error: stage '{current_stage}' failed: {error}")
        return 1
    except KeyboardInterrupt:
        print()
        print("Interrupted")
        return 130

    print()
    print("All enabled stages passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
