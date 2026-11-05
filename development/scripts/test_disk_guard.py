#!/usr/bin/env python3
"""Tests for the repository disk budget guard."""

from __future__ import annotations

import fcntl
import os
import tempfile
import time
import unittest
from unittest.mock import patch
from pathlib import Path

import disk_guard
from disk_guard import GIB, guard

NOW = time.time()
DAY = 24 * 3600


def write(path: Path, size: int, mtime: float = NOW) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "wb") as handle:
        handle.write(os.urandom(size))
    os.utime(path, (mtime, mtime))
    return path


def age(path: Path, mtime: float) -> Path:
    os.utime(path, (mtime, mtime))
    return path


class DiskGuardTests(unittest.TestCase):
    def setUp(self) -> None:
        self._dir = tempfile.TemporaryDirectory()
        root = Path(self._dir.name)
        self.repo = root / "repo"
        self.tmp = root / "tmp"
        self.repo.mkdir()
        self.tmp.mkdir()

    def tearDown(self) -> None:
        self._dir.cleanup()

    def run_guard(self, limit: float, target: float) -> tuple[int, list[str]]:
        return guard(limit, target, repo=self.repo, tmp=self.tmp, now=NOW)

    def test_stale_temp_caches_are_always_removed(self) -> None:
        scripts = self.tmp / "taro-scripts"
        old = write(scripts / "aaaa" / "debug" / "bin", 4096).parent.parent
        fresh = write(scripts / "bbbb" / "debug" / "bin", 4096).parent.parent
        age(old, NOW - 2 * DAY)
        crashed = write(self.tmp / "taro_tests_x" / "dist", 4096).parent
        age(crashed, NOW - 2 * DAY)
        running = write(self.tmp / "taro_tests_y" / "dist", 4096).parent
        unrelated = write(self.tmp / "other-tool" / "file", 4096).parent
        age(unrelated, NOW - 2 * DAY)

        self.run_guard(limit=GIB, target=GIB)

        self.assertFalse(old.exists())
        self.assertFalse(crashed.exists())
        self.assertTrue(fresh.exists())
        self.assertTrue(running.exists())
        self.assertTrue(unrelated.exists())

    def test_superseded_cargo_hashes_go_once_over_target(self) -> None:
        deps = self.repo / "target" / "debug" / "deps"
        fingerprint = self.repo / "target" / "debug" / ".fingerprint"
        hashes = [f"{index:016x}" for index in range(5)]
        for index, digest in enumerate(hashes):
            mtime = NOW - (5 - index) * 60
            write(deps / f"libcompiler-{digest}.rlib", 64 * 1024, mtime)
            write(fingerprint / f"compiler-{digest}" / "lib-compiler", 16, mtime)
        write(deps / "libother-0000000000000009.rlib", 1024, NOW - 10 * DAY)

        self.run_guard(limit=10 * GIB, target=10 * GIB)
        self.assertEqual(len(list(deps.glob("libcompiler-*"))), 5)

        self.run_guard(limit=10 * GIB, target=0)
        kept = sorted(path.name for path in deps.glob("libcompiler-*"))
        self.assertEqual(kept, [f"libcompiler-{digest}.rlib" for digest in hashes[2:]])
        self.assertFalse((fingerprint / f"compiler-{hashes[0]}").exists())
        self.assertTrue((fingerprint / f"compiler-{hashes[4]}").exists())
        self.assertTrue((deps / "libother-0000000000000009.rlib").exists())

    def test_whole_profiles_go_only_over_the_limit(self) -> None:
        release = write(self.repo / "target" / "release" / "deps" / "big", 256 * 1024)
        debug = write(self.repo / "target" / "debug" / "deps" / "big", 256 * 1024)
        source = write(self.repo / "compiler" / "src" / "lib.rs", 1024)

        current, _ = self.run_guard(limit=300 * 1024, target=0)

        self.assertFalse(release.exists())
        self.assertTrue(debug.exists())
        self.assertTrue(source.exists())
        self.assertLessEqual(current, 300 * 1024)

    def test_running_cargo_build_is_never_pruned(self) -> None:
        profile = self.repo / "target" / "debug"
        artifact = write(profile / "deps" / "big", 256 * 1024)
        lock_path = write(profile / ".cargo-lock", 0)
        with open(lock_path, "a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            current, log = self.run_guard(limit=0, target=0)
        self.assertTrue(artifact.exists())
        self.assertGreater(current, 0)
        self.assertTrue(any("holds its lock" in line for line in log))

    def test_nested_package_targets_go_once_over_target(self) -> None:
        nested = write(self.repo / "std" / "target" / "debug" / "std.o", 4096)
        fixture = write(
            self.repo / "language_tests" / "package_fixtures" / "a" / "app" / "target" / "x", 4096
        )
        self.run_guard(limit=GIB, target=GIB)
        self.assertTrue(nested.exists())

        self.run_guard(limit=GIB, target=0)
        self.assertFalse(nested.exists())
        self.assertFalse(fixture.exists())

    def test_active_sdk_survives_forced_temp_pruning_and_stays_counted(self) -> None:
        for relative in ("taro_dist_active", "taro_tests_active/dist"):
            with self.subTest(relative=relative):
                active = self.tmp / relative
                binary = write(active / "bin" / "taro", 4096)
                age(self.tmp / relative.split("/")[0], NOW - 2 * DAY)
                obsolete = write(self.tmp / "taro_dist_unused" / "bin" / "taro", 4096)
                with patch.dict(os.environ, {"TARO_HOME": str(active)}):
                    current, _ = self.run_guard(limit=GIB, target=0)
                self.assertTrue(binary.is_file(), "cleanup removed the SDK executing this gate")
                self.assertFalse(obsolete.exists())
                self.assertGreaterEqual(current, disk_guard.tree_size(active))
                self.assertGreater(current, 0, "active SDK still counts against the disk budget")

    def test_dry_run_deletes_nothing(self) -> None:
        artifact = write(self.repo / "target" / "release" / "deps" / "big", 256 * 1024)
        guard(0, 0, repo=self.repo, tmp=self.tmp, dry_run=True, now=time.time())
        self.assertTrue(artifact.exists())


if __name__ == "__main__":
    unittest.main()
