#!/usr/bin/env python3
"""Distribution publication must preserve the last usable toolchain on failure."""

import argparse
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import build_dist


class BuildDistributionTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.repo = self.root / "repo"
        self.std = self.repo / "std"
        self.std.mkdir(parents=True)
        target = self.repo / "target/release"
        target.mkdir(parents=True)
        (target / "taro-bin").write_bytes(b"new compiler")
        (target / "libtaro_runtime.a").write_bytes(b"new runtime")
        self.dist = self.repo / "dist"
        self.dist.mkdir()
        (self.dist / "usable").write_text("old toolchain", encoding="utf-8")

    def build(self, command_runner, dist=None) -> None:
        args = argparse.Namespace(profile="release", dist_dir=dist or self.dist, std_path=self.std, target=None)
        with (
            patch.object(build_dist, "__file__", str(self.repo / "development/scripts/build_dist.py")),
            patch.object(build_dist, "parse_args", return_value=args),
            patch.object(build_dist, "run_command", side_effect=command_runner),
        ):
            build_dist.main()

    def test_bootstrap_failure_preserves_existing_distribution(self) -> None:
        def fail_bootstrap(command, **kwargs):
            if "check" in command:
                raise subprocess.CalledProcessError(1, command)

        with self.assertRaises(subprocess.CalledProcessError):
            self.build(fail_bootstrap)
        self.assertEqual((self.dist / "usable").read_text(), "old toolchain")

    def test_symlink_destination_is_rejected_before_building(self) -> None:
        link = self.repo / "linked-dist"
        link.symlink_to(self.dist, target_is_directory=True)
        calls = []
        with self.assertRaisesRegex(ValueError, "symlink"):
            self.build(lambda command, **kwargs: calls.append(command), dist=link)
        self.assertEqual(calls, [])
        self.assertEqual((self.dist / "usable").read_text(), "old toolchain")

    def test_regular_file_destination_is_rejected_before_building(self) -> None:
        destination = self.repo / "important-file"
        destination.write_text("keep this", encoding="utf-8")
        calls = []
        with self.assertRaisesRegex(ValueError, "directory"):
            self.build(lambda command, **kwargs: calls.append(command), dist=destination)
        self.assertEqual(calls, [])
        self.assertEqual(destination.read_text(), "keep this")

    def test_success_publishes_complete_distribution_once(self) -> None:
        def bootstrap(command, **kwargs):
            if "check" in command:
                self.assertEqual((self.dist / "usable").read_text(), "old toolchain")
                home = Path(kwargs["env"]["TARO_HOME"])
                (home / "attached-std").write_text("ready", encoding="utf-8")

        self.build(bootstrap)
        self.assertFalse((self.dist / "usable").exists())
        self.assertEqual((self.dist / "bin/taro").read_bytes(), b"new compiler")
        self.assertEqual((self.dist / "attached-std").read_text(), "ready")
        self.assertEqual((self.dist / "std").resolve(), self.std)
        self.assertFalse((self.dist / ".std_bootstrap.tr").exists())

    def test_publication_failure_restores_previous_distribution(self) -> None:
        rename = Path.rename

        def fail_publication(source, target):
            if source.name == "dist" and source.parent != self.repo:
                raise OSError("publication failed")
            return rename(source, target)

        with patch.object(Path, "rename", fail_publication):
            with self.assertRaisesRegex(OSError, "publication failed"):
                self.build(lambda command, **kwargs: None)
        self.assertEqual((self.dist / "usable").read_text(), "old toolchain")

    def test_failed_restore_retains_the_previous_distribution_for_recovery(self) -> None:
        rename = Path.rename

        def fail_publication_and_restore(source, target):
            if source.parent != self.repo:
                raise OSError("rename failed")
            return rename(source, target)

        with patch.object(Path, "rename", fail_publication_and_restore):
            with self.assertRaisesRegex(OSError, "rename failed"):
                self.build(lambda command, **kwargs: None)
        saved = list(self.repo.glob(".dist-*/previous/usable"))
        self.assertEqual(len(saved), 1)
        self.assertEqual(saved[0].read_text(), "old toolchain")


if __name__ == "__main__":
    unittest.main()
