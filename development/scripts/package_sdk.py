#!/usr/bin/env python3
"""Package a built SDK as `taro-<version>-<platform>.tar.gz` with a checksum.

The archive contains one top-level directory of the same name. Entries are
sorted and carry fixed ownership and timestamps, so rebuilding identical SDK
contents yields an identical archive and checksum.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import platform
import subprocess
import sys
import tarfile
from pathlib import Path

ARCHITECTURES = {"arm64": "arm64", "aarch64": "arm64", "x86_64": "x86_64", "amd64": "x86_64"}


def platform_name(system: str = sys.platform, machine: str = platform.machine()) -> str:
    os_name = {"darwin": "macos", "linux": "linux"}.get(system)
    architecture = ARCHITECTURES.get(machine.lower())
    if os_name is None or architecture is None:
        raise ValueError(f"no SDK platform name for {system}/{machine}")
    return f"{os_name}-{architecture}"


def sdk_version(sdk: Path) -> str:
    output = subprocess.check_output([sdk / "bin" / "taro", "--version"], text=True).split()
    if len(output) != 2 or output[0] != "taro":
        raise ValueError(f"unexpected `taro --version` output: {' '.join(output)}")
    return output[1]


def normalized(info: tarfile.TarInfo) -> tarfile.TarInfo:
    info.uid = info.gid = 0
    info.uname = info.gname = ""
    info.mtime = 0
    if info.isdir() or info.mode & 0o111:
        info.mode = 0o755
    else:
        info.mode = 0o644
    return info


def write_archive(sdk: Path, archive: Path, top: str) -> None:
    paths = sorted(sdk.rglob("*"))
    for path in paths:
        if path.is_symlink() or not (path.is_file() or path.is_dir()):
            raise ValueError(f"SDK entries must be regular files or directories: {path}")
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w", format=tarfile.PAX_FORMAT) as tar:
        tar.addfile(normalized(tar.gettarinfo(sdk, top)))
        for path in paths:
            info = normalized(tar.gettarinfo(path, f"{top}/{path.relative_to(sdk).as_posix()}"))
            if path.is_file():
                with path.open("rb") as file:
                    tar.addfile(info, file)
            else:
                tar.addfile(info)
    with archive.open("wb") as output:
        with gzip.GzipFile(filename="", mode="wb", fileobj=output, mtime=0, compresslevel=9) as zipped:
            zipped.write(buffer.getvalue())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sdk", type=Path, help="SDK directory from build_dist.py --sdk.")
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()

    sdk = args.sdk.resolve()
    top = f"taro-{sdk_version(sdk)}-{platform_name()}"
    args.output_dir.mkdir(parents=True, exist_ok=True)
    archive = args.output_dir / f"{top}.tar.gz"
    write_archive(sdk, archive, top)
    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    (args.output_dir / f"{archive.name}.sha256").write_text(f"{digest}  {archive.name}\n")
    print(archive)


if __name__ == "__main__":
    main()
