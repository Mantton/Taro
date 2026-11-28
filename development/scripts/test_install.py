#!/usr/bin/env python3
"""The packaged archive installs, upgrades and verifies like a release download."""

import hashlib
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

import package_sdk

INSTALLER = Path(__file__).resolve().parents[2] / "install.sh"


class InstallTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.releases = self.root / "releases"
        self.home = self.root / "home"
        self.home.mkdir()
        self.install_root = self.root / "install"

    def release(self, version: str) -> Path:
        sdk = self.root / f"sdk-{version}"
        (sdk / "bin").mkdir(parents=True)
        (sdk / "lib/taro").mkdir(parents=True)
        taro = sdk / "bin/taro"
        taro.write_text(f"#!/bin/sh\necho taro {version}\n")
        taro.chmod(0o755)
        name = f"taro-{package_sdk.sdk_version(sdk)}-{package_sdk.platform_name()}"
        directory = self.releases / f"v{version}"
        directory.mkdir(parents=True)
        archive = directory / f"{name}.tar.gz"
        package_sdk.write_archive(sdk, archive, name)
        digest = hashlib.sha256(archive.read_bytes()).hexdigest()
        (directory / f"{archive.name}.sha256").write_text(f"{digest}  {archive.name}\n")
        return archive

    def install(self, version: str, **extra: str) -> subprocess.CompletedProcess:
        env = {
            "PATH": "/usr/bin:/bin:/usr/sbin:/sbin",
            "HOME": str(self.home),
            "TMPDIR": str(self.root),
            "TARO_VERSION": f"v{version}",
            "TARO_INSTALL": str(self.install_root),
            "TARO_DOWNLOAD_URL": (self.releases / f"v{version}").as_uri(),
            "TARO_NO_MODIFY_PATH": "1",
            **extra,
        }
        return subprocess.run(["sh", INSTALLER], env=env, capture_output=True, text=True)

    def current_version(self) -> str:
        taro = self.install_root / "current/bin/taro"
        return subprocess.check_output([taro, "--version"], text=True).strip()

    def test_installs_and_upgrades_to_a_single_toolchain(self) -> None:
        self.release("1.0.0")
        result = self.install("1.0.0")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.current_version(), "taro 1.0.0")
        self.assertTrue((self.install_root / "current").is_symlink())

        self.release("1.1.0")
        result = self.install("1.1.0")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.current_version(), "taro 1.1.0")
        self.assertEqual(len(list((self.install_root / "toolchains").iterdir())), 1)

    def test_checksum_mismatch_keeps_the_existing_install(self) -> None:
        self.release("1.0.0")
        self.assertEqual(self.install("1.0.0").returncode, 0)
        archive = self.release("2.0.0")
        archive.write_bytes(archive.read_bytes() + b"tampered")
        result = self.install("2.0.0")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("checksum mismatch", result.stderr)
        self.assertEqual(self.current_version(), "taro 1.0.0")

    def test_adds_the_toolchain_to_path_once(self) -> None:
        self.release("1.0.0")
        for _ in range(2):
            result = self.install("1.0.0", SHELL="/bin/zsh", TARO_NO_MODIFY_PATH="0")
            self.assertEqual(result.returncode, 0, result.stderr)
        profile = (self.home / ".zshrc").read_text()
        self.assertEqual(profile.count(str(self.install_root / "current/bin")), 1)

    def test_archives_are_reproducible(self) -> None:
        first = self.release("1.0.0")
        second = self.root / "again.tar.gz"
        os.utime(self.root / "sdk-1.0.0/bin/taro", (1, 1))
        package_sdk.write_archive(self.root / "sdk-1.0.0", second, first.name.removesuffix(".tar.gz"))
        self.assertEqual(first.read_bytes(), second.read_bytes())

    def test_platform_names_match_the_installer(self) -> None:
        self.assertEqual(package_sdk.platform_name("darwin", "arm64"), "macos-arm64")
        self.assertEqual(package_sdk.platform_name("linux", "x86_64"), "linux-x86_64")
        self.assertEqual(package_sdk.platform_name("linux", "aarch64"), "linux-arm64")
        script = INSTALLER.read_text()
        for name in ("macos-arm64", "linux-x86_64", "linux-arm64"):
            self.assertIn(f"echo {name}", script)


if __name__ == "__main__":
    unittest.main()
