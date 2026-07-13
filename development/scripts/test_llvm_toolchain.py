#!/usr/bin/env python3
"""Regression tests for LLVM 22.1 toolchain discovery."""

from __future__ import annotations

import shlex
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from llvm_toolchain import (
    LLVM_PREFIX_ENV,
    LLVMToolchain,
    LLVMToolchainError,
    inspect_llvm_config,
    resolve_llvm_toolchain,
)


def make_llvm_config(prefix: Path, version: str) -> Path:
    """Create the smallest llvm-config implementation needed by the resolver."""
    bin_dir = prefix / "bin"
    lib_dir = prefix / "lib"
    bin_dir.mkdir(parents=True)
    lib_dir.mkdir()
    llvm_config = bin_dir / "llvm-config"
    llvm_config.write_text(
        "#!/bin/sh\n"
        'case "$1" in\n'
        f"  --version) printf '%s\\n' {shlex.quote(version)} ;;\n"
        f"  --prefix) printf '%s\\n' {shlex.quote(str(prefix))} ;;\n"
        f"  --libdir) printf '%s\\n' {shlex.quote(str(lib_dir))} ;;\n"
        "  *) exit 64 ;;\n"
        "esac\n",
        encoding="utf-8",
    )
    llvm_config.chmod(0o755)
    return llvm_config


class LLVMToolchainTests(unittest.TestCase):
    def test_inspection_rejects_wrong_minor_version(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            llvm_config = make_llvm_config(Path(directory), "22.2.0")

            toolchain, status = inspect_llvm_config(llvm_config)

            self.assertIsNone(toolchain)
            self.assertEqual(status, "version 22.2.0")

    def test_explicit_prefix_is_authoritative(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            requested = root / "requested"
            fallback = root / "fallback"
            make_llvm_config(requested, "16.0.6")
            make_llvm_config(fallback, "22.1.8")

            with self.assertRaisesRegex(
                LLVMToolchainError,
                f"{LLVM_PREFIX_ENV} does not identify a compatible LLVM 22.1.x",
            ):
                resolve_llvm_toolchain(
                    {
                        LLVM_PREFIX_ENV: str(requested),
                        "PATH": str(fallback / "bin"),
                    }
                )

    def test_path_fallback_finds_llvm_22_1(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            prefix = Path(directory)
            llvm_config = make_llvm_config(prefix, "22.1.8")

            toolchain = resolve_llvm_toolchain({"PATH": str(prefix / "bin")})

            self.assertEqual(toolchain.version, "22.1.8")
            self.assertEqual(toolchain.llvm_config, llvm_config.resolve())
            self.assertEqual(toolchain.prefix, prefix.resolve())

    def test_environment_selects_tools_and_linux_libraries(self) -> None:
        prefix = Path("/toolchains/llvm-22")
        toolchain = LLVMToolchain(
            llvm_config=prefix / "bin" / "llvm-config",
            prefix=prefix,
            lib_dir=prefix / "lib",
            version="22.1.8",
        )

        with mock.patch.object(sys, "platform", "linux"):
            environment = toolchain.environment(
                {"PATH": "/usr/bin", "LD_LIBRARY_PATH": "/usr/lib"}
            )

        self.assertEqual(environment[LLVM_PREFIX_ENV], str(prefix))
        self.assertEqual(environment["PATH"], f"{prefix}/bin:/usr/bin")
        self.assertEqual(
            environment["LD_LIBRARY_PATH"], f"{prefix}/lib:/usr/lib"
        )


if __name__ == "__main__":
    unittest.main()
