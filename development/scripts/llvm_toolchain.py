#!/usr/bin/env python3
"""Resolve LLVM 22.1 for Taro builds or run a command with that toolchain."""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping

LLVM_PREFIX_ENV = "LLVM_SYS_221_PREFIX"
REQUIRED_LLVM_VERSION = (22, 1)
VERSION_PATTERN = re.compile(r"^(\d+)\.(\d+)(?:\.(\d+))?")


class LLVMToolchainError(RuntimeError):
    """Raised when no LLVM installation satisfies Taro's toolchain contract."""


@dataclass(frozen=True)
class LLVMToolchain:
    llvm_config: Path
    prefix: Path
    lib_dir: Path
    version: str

    def environment(self, base: Mapping[str, str] | None = None) -> dict[str, str]:
        env = dict(os.environ if base is None else base)
        env[LLVM_PREFIX_ENV] = str(self.prefix)
        env["PATH"] = prepend_path(self.prefix / "bin", env.get("PATH"))
        # Homebrew LLVM dylibs carry an absolute install name. Other Unix
        # installations commonly use an LLVM-specific lib directory that is
        # not part of the system loader path.
        if sys.platform != "darwin":
            env["LD_LIBRARY_PATH"] = prepend_path(
                self.lib_dir, env.get("LD_LIBRARY_PATH")
            )
        return env


def prepend_path(path: Path, existing: str | None) -> str:
    value = str(path)
    if not existing:
        return value
    parts = existing.split(os.pathsep)
    if value in parts:
        return existing
    return os.pathsep.join([value, existing])


def run_llvm_config(llvm_config: Path, argument: str) -> str:
    result = subprocess.run(
        [str(llvm_config), argument],
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip()


def inspect_llvm_config(llvm_config: Path) -> tuple[LLVMToolchain | None, str]:
    if not llvm_config.is_file():
        return None, "not found"
    try:
        version = run_llvm_config(llvm_config, "--version")
        match = VERSION_PATTERN.match(version)
        if match is None:
            return None, f"unrecognized version `{version}`"
        actual = (int(match.group(1)), int(match.group(2)))
        if actual != REQUIRED_LLVM_VERSION:
            return None, f"version {version}"
        prefix = Path(run_llvm_config(llvm_config, "--prefix")).resolve()
        lib_dir = Path(run_llvm_config(llvm_config, "--libdir")).resolve()
        return (
            LLVMToolchain(
                llvm_config=llvm_config.resolve(),
                prefix=prefix,
                lib_dir=lib_dir,
                version=version,
            ),
            f"version {version}",
        )
    except (OSError, subprocess.CalledProcessError) as error:
        return None, str(error)


def homebrew_llvm_configs(env: Mapping[str, str]) -> Iterable[Path]:
    brew = shutil.which("brew", path=env.get("PATH"))
    if brew is None:
        return
    for formula in ("llvm@22", "llvm"):
        result = subprocess.run(
            [brew, "--prefix", formula],
            capture_output=True,
            text=True,
        )
        if result.returncode == 0 and result.stdout.strip():
            yield Path(result.stdout.strip()) / "bin" / "llvm-config"


def candidate_llvm_configs(env: Mapping[str, str]) -> Iterable[Path]:
    path = env.get("PATH")
    for name in ("llvm-config-22", "llvm-config-22.1", "llvm-config22", "llvm-config"):
        resolved = shutil.which(name, path=path)
        if resolved:
            yield Path(resolved)

    yield from homebrew_llvm_configs(env)

    for prefix in (
        "/opt/homebrew/opt/llvm@22",
        "/opt/homebrew/opt/llvm",
        "/usr/local/opt/llvm@22",
        "/usr/local/opt/llvm",
        "/usr/lib/llvm-22",
    ):
        yield Path(prefix) / "bin" / "llvm-config"


def resolution_error(attempts: list[tuple[Path, str]], explicit: bool) -> LLVMToolchainError:
    required = "LLVM 22.1.x"
    if explicit:
        heading = f"{LLVM_PREFIX_ENV} does not identify a compatible {required} installation."
    else:
        heading = f"could not find a compatible {required} installation."
    checked = "\n".join(f"  - {path}: {status}" for path, status in attempts)
    if not checked:
        checked = "  - no llvm-config candidates were found"
    return LLVMToolchainError(
        f"{heading}\n"
        f"Checked:\n{checked}\n"
        f"Set {LLVM_PREFIX_ENV} to the prefix containing bin/llvm-config.\n"
        f"Homebrew: export {LLVM_PREFIX_ENV}=\"$(brew --prefix llvm@22)\"\n"
        f"Linux example: export {LLVM_PREFIX_ENV}=/usr/lib/llvm-22"
    )


def resolve_llvm_toolchain(
    base: Mapping[str, str] | None = None,
) -> LLVMToolchain:
    env = os.environ if base is None else base
    explicit_prefix = env.get(LLVM_PREFIX_ENV)
    if explicit_prefix:
        llvm_config = Path(explicit_prefix).expanduser() / "bin" / "llvm-config"
        toolchain, status = inspect_llvm_config(llvm_config)
        if toolchain is not None:
            return toolchain
        raise resolution_error([(llvm_config, status)], explicit=True)

    attempts: list[tuple[Path, str]] = []
    seen: set[Path] = set()
    for candidate in candidate_llvm_configs(env):
        candidate = candidate.expanduser()
        identity = candidate.resolve(strict=False)
        if identity in seen:
            continue
        seen.add(identity)
        toolchain, status = inspect_llvm_config(candidate)
        attempts.append((candidate, status))
        if toolchain is not None:
            return toolchain
    raise resolution_error(attempts, explicit=False)


def main(arguments: list[str]) -> int:
    if arguments and arguments[0] in {"-h", "--help"}:
        print("usage: llvm_toolchain.py [COMMAND [ARG ...]]")
        print("Resolve LLVM 22.1, or run COMMAND with the resolved LLVM environment.")
        return 0

    try:
        toolchain = resolve_llvm_toolchain()
    except LLVMToolchainError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    if arguments:
        env = toolchain.environment()
        try:
            os.execvpe(arguments[0], arguments, env)
        except OSError as error:
            print(f"error: failed to run `{arguments[0]}`: {error}", file=sys.stderr)
            return 127

    print(f"LLVM: {toolchain.version}")
    print(f"llvm-config: {toolchain.llvm_config}")
    print(f"prefix: {toolchain.prefix}")
    print(f"{LLVM_PREFIX_ENV}: {toolchain.prefix}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
