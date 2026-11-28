#!/usr/bin/env python3
"""Build the static LLVM that release SDKs embed in the `taro` executable.

Developers link the compiler against any LLVM 22.1 installation, such as
Homebrew's. A downloadable SDK must instead run on machines other than the one
that built it, so the LLVM it embeds is built here with an explicit platform
floor: the macOS deployment target on macOS, and the glibc of the build
container on Linux (see `.github/workflows/sdk.yml`).

The result is libraries, headers and `llvm-config` only, for the AArch64 and
X86 backends, without optional compression, terminal or XML dependencies, so
`llvm-config --system-libs` names only libraries the OS always provides.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import tarfile
import urllib.request
from pathlib import Path

LLVM_VERSION = "22.1.8"
SOURCE_URL = (
    f"https://github.com/llvm/llvm-project/releases/download/llvmorg-{LLVM_VERSION}/"
    f"llvm-project-{LLVM_VERSION}.src.tar.xz"
)
SOURCE_SHA256 = "922f1817a0df7b1489272d18134ee0087a8b068828f87ac63b9861b1a9965888"
# Must match `MACOS_DEPLOYMENT_TARGET` in compiler/src/codegen/target.rs.
MACOS_DEPLOYMENT_TARGET = "14.0"
# Only these top-level source directories are needed to build LLVM itself.
SOURCE_DIRECTORIES = ("llvm", "cmake", "third-party")
STAMP = "taro-llvm.json"
LICENSE = "LICENSE.TXT"


def cmake_options(prefix: Path) -> dict[str, str]:
    options = {
        "CMAKE_BUILD_TYPE": "Release",
        "CMAKE_INSTALL_PREFIX": str(prefix),
        "LLVM_TARGETS_TO_BUILD": "AArch64;X86",
        "LLVM_ENABLE_PROJECTS": "",
        "LLVM_ENABLE_RUNTIMES": "",
        "BUILD_SHARED_LIBS": "OFF",
        "LLVM_BUILD_LLVM_DYLIB": "OFF",
        "LLVM_LINK_LLVM_DYLIB": "OFF",
        "LLVM_ENABLE_ASSERTIONS": "OFF",
        "LLVM_ENABLE_BINDINGS": "OFF",
        "LLVM_ENABLE_ZLIB": "OFF",
        "LLVM_ENABLE_ZSTD": "OFF",
        "LLVM_ENABLE_LIBXML2": "OFF",
        "LLVM_ENABLE_LIBEDIT": "OFF",
        "LLVM_ENABLE_LIBPFM": "OFF",
        "LLVM_ENABLE_CURL": "OFF",
        "LLVM_ENABLE_HTTPLIB": "OFF",
        "LLVM_INCLUDE_TESTS": "OFF",
        "LLVM_INCLUDE_BENCHMARKS": "OFF",
        "LLVM_INCLUDE_EXAMPLES": "OFF",
        "LLVM_INCLUDE_DOCS": "OFF",
        "LLVM_DISTRIBUTION_COMPONENTS": "llvm-config;llvm-headers;llvm-libraries;cmake-exports",
    }
    if sys.platform == "darwin":
        options["CMAKE_OSX_DEPLOYMENT_TARGET"] = MACOS_DEPLOYMENT_TARGET
        options["CMAKE_OSX_ARCHITECTURES"] = platform.machine()
    return options


def configuration(options: dict[str, str]) -> dict[str, object]:
    """Everything that determines the installed LLVM, for reuse checks."""
    portable = {key: value for key, value in options.items() if key != "CMAKE_INSTALL_PREFIX"}
    return {
        "version": LLVM_VERSION,
        "source_sha256": SOURCE_SHA256,
        "platform": sys.platform,
        "machine": platform.machine(),
        "options": portable,
    }


def download(destination: Path) -> None:
    if destination.exists() and sha256(destination) == SOURCE_SHA256:
        return
    partial = destination.with_suffix(".partial")
    print(f"Downloading {SOURCE_URL}")
    with urllib.request.urlopen(SOURCE_URL) as response, partial.open("wb") as output:
        shutil.copyfileobj(response, output, length=1 << 20)
    actual = sha256(partial)
    if actual != SOURCE_SHA256:
        partial.unlink()
        raise RuntimeError(f"LLVM source checksum mismatch: expected {SOURCE_SHA256}, got {actual}")
    partial.rename(destination)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as file:
        for block in iter(lambda: file.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def extract(archive: Path, destination: Path) -> Path:
    """Unpack the needed source directories; return the source root."""
    root = f"llvm-project-{LLVM_VERSION}.src"
    if destination.exists():
        shutil.rmtree(destination)
    destination.mkdir(parents=True)
    with tarfile.open(archive, "r:xz") as source:
        members = [
            member for member in source.getmembers()
            if member.name.split("/")[1:2] and member.name.split("/")[1] in SOURCE_DIRECTORIES
        ]
        source.extractall(destination, members=members, filter="data")
    return destination / root


def run(command: list[str], env: dict[str, str] | None = None) -> None:
    print("Running:", " ".join(command), flush=True)
    subprocess.run(command, check=True, env=env)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prefix", type=Path, help="Installation directory.")
    parser.add_argument("--work-dir", type=Path, help="Download and build directory (default: <prefix>.work).")
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 2)
    parser.add_argument("--keep-build", action="store_true", help="Keep the build tree afterwards.")
    parser.add_argument(
        "--print-cache-key", action="store_true",
        help="Print a digest of everything that determines the build, then exit.",
    )
    args = parser.parse_args()

    if args.print_cache_key:
        # The prefix path does not affect the installed libraries.
        portable = configuration(cmake_options(Path("/prefix")))
        print(hashlib.sha256(json.dumps(portable, sort_keys=True).encode()).hexdigest()[:16])
        return

    if args.prefix is None:
        parser.error("--prefix is required")
    prefix = args.prefix.absolute()
    work = (args.work_dir or prefix.with_name(prefix.name + ".work")).absolute()
    options = cmake_options(prefix)
    wanted = configuration(options)

    stamp = prefix / STAMP
    if stamp.exists() and json.loads(stamp.read_text()) == wanted:
        print(f"LLVM {LLVM_VERSION} is already installed at {prefix}")
        return
    if shutil.which("ninja") is None:
        raise RuntimeError("ninja is required to build LLVM")

    work.mkdir(parents=True, exist_ok=True)
    archive = work / f"llvm-project-{LLVM_VERSION}.src.tar.xz"
    download(archive)
    source = extract(archive, work / "src")
    build = work / "build"
    if build.exists():
        shutil.rmtree(build)
    if prefix.exists():
        shutil.rmtree(prefix)

    env = os.environ.copy()
    if sys.platform == "darwin":
        env["MACOSX_DEPLOYMENT_TARGET"] = MACOS_DEPLOYMENT_TARGET
    run(
        ["cmake", "-G", "Ninja", "-S", str(source / "llvm"), "-B", str(build)]
        + [f"-D{key}={value}" for key, value in options.items()],
        env=env,
    )
    run(["ninja", "-C", str(build), "-j", str(args.jobs), "install-distribution"], env=env)
    # The SDK's third-party notices include the license of the embedded LLVM.
    shutil.copy2(source / "llvm" / "LICENSE.TXT", prefix / LICENSE)
    stamp.write_text(json.dumps(wanted, indent=2, sort_keys=True) + "\n")

    shutil.rmtree(work / "src")
    if not args.keep_build:
        shutil.rmtree(build)
    print(f"LLVM {LLVM_VERSION} installed at {prefix}")


if __name__ == "__main__":
    main()
