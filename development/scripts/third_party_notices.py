#!/usr/bin/env python3
"""Collect the license texts of third-party code shipped in a release SDK.

The SDK contains `taro` (with LLVM, libgit2 and OpenSSL), `taro-lsp`, and the
runtime archive that is linked into every program Taro builds. This walks the
normal (non-build, non-dev) Cargo dependencies of those three, for the target
being packaged, and copies each package's license files. LLVM's license comes
from the installation built by `build_llvm.py`.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path

LICENSE_PREFIXES = ("license", "licence", "copying", "notice", "copyright")
# Vendored C libraries carry their own licenses inside the crate source. Some
# are compiled by a build dependency (openssl-src), so they are included even
# when reached only through a build edge.
VENDORED_LICENSES = {
    "libgit2-sys": ["libgit2/COPYING"],
    "libssh2-sys": ["libssh2/COPYING"],
    "libz-sys": ["src/zlib/LICENSE"],
    "openssl-src": ["openssl/LICENSE.txt"],
}
# (manifest relative to the repository, root package, Cargo features)
ROOTS = (
    ("Cargo.toml", "taro-bin", ["taro-bin/release-sdk"]),
    ("Cargo.toml", "taro-runtime", []),
    ("taro-lsp/Cargo.toml", "taro-lsp", []),
)


def metadata(repo: Path, manifest: str, features: list[str], target: str) -> dict:
    command = [
        "cargo", "metadata", "--format-version", "1", "--locked",
        "--manifest-path", str(repo / manifest), "--filter-platform", target,
    ]
    if features:
        command.extend(["--features", ",".join(features)])
    return json.loads(subprocess.check_output(command, cwd=repo))


def shipped_packages(data: dict, root_name: str) -> list[dict]:
    """Third-party packages reachable from `root_name` through normal edges."""
    packages = {package["id"]: package for package in data["packages"]}
    nodes = {node["id"]: node for node in data["resolve"]["nodes"]}
    root = next(package["id"] for package in data["packages"] if package["name"] == root_name
                and package["source"] is None)
    seen, pending = set(), [root]
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        for dependency in nodes[current]["deps"]:
            if any(kind["kind"] is None for kind in dependency["dep_kinds"]):
                pending.append(dependency["pkg"])
            elif packages[dependency["pkg"]]["name"] in VENDORED_LICENSES:
                seen.add(dependency["pkg"])
    return [packages[identifier] for identifier in seen if packages[identifier]["source"] is not None]


def license_files(package: dict) -> list[Path]:
    directory = Path(package["manifest_path"]).parent
    files = sorted(
        path for path in directory.iterdir()
        if path.is_file() and path.name.lower().startswith(LICENSE_PREFIXES)
    )
    if package.get("license_file"):
        declared = directory / package["license_file"]
        if declared.is_file() and declared not in files:
            files.append(declared)
    for relative in VENDORED_LICENSES.get(package["name"], []):
        if (directory / relative).is_file():
            files.append(directory / relative)
    return files


def render(repo: Path, target: str, llvm_license: Path | None) -> str:
    packages = {}
    for manifest, root, features in ROOTS:
        for package in shipped_packages(metadata(repo, manifest, features, target), root):
            packages[(package["name"], package["version"])] = package

    sections = [
        "Third-party software included in this Taro SDK\n"
        "===============================================\n\n"
        "Taro itself is licensed under MIT OR Apache-2.0 (see LICENSE-MIT and\n"
        "LICENSE-APACHE). The components below keep their own licenses. The runtime\n"
        "archive, including the code listed for it here and the Go-derived allocator\n"
        "tables described in lib/taro/runtime/GO-LICENSE, is linked into programs\n"
        "that Taro builds.\n"
    ]
    if llvm_license is not None:
        sections.append(
            "\n--------------------------------------------------------------------------------\n"
            "LLVM (Apache-2.0 WITH LLVM-exception), embedded in bin/taro\n\n"
            + llvm_license.read_text(errors="replace")
        )
    missing = []
    for (name, version), package in sorted(packages.items()):
        files = license_files(package)
        if not files:
            missing.append(f"{name} {version}")
        header = (
            "\n--------------------------------------------------------------------------------\n"
            f"{name} {version} ({package.get('license') or 'license not declared'})\n"
        )
        if package.get("repository"):
            header += f"{package['repository']}\n"
        body = "".join(f"\n{path.name}:\n\n{path.read_text(errors='replace')}" for path in files)
        sections.append(header + body)
    if missing:
        sections.append(
            "\n--------------------------------------------------------------------------------\n"
            "Packages without a bundled license file (see their declared license above):\n"
            + "".join(f"  {entry}\n" for entry in missing)
        )
    return "".join(sections)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--target", required=True, help="Rust target triple being packaged.")
    parser.add_argument("--llvm-license", type=Path)
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[2]
    args.output.write_text(render(repo, args.target, args.llvm_license))


if __name__ == "__main__":
    main()
