#!/usr/bin/env python3
"""Keep the repository and its build caches under a fixed disk budget.

The budget covers the repository checkout plus the temporary directories that
Taro tooling creates (`taro run` script caches and runner work directories).
Pruning is staged: stale temporary caches always go; past the soft target,
nested package outputs and superseded Cargo artifacts go next; past the hard
limit, whole Cargo profiles are removed. Cargo's build lock is held while
touching `target/`, so a running build is never pruned underneath.
"""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import os
import re
import shutil
import sys
import tempfile
import time
from collections import defaultdict
from pathlib import Path
from typing import Iterator

PROJECT_ROOT = Path(__file__).resolve().parents[2]
GIB = 1024**3
DEFAULT_LIMIT_GIB = 15.0
DEFAULT_TARGET_GIB = 10.0
STALE_TEMP_SECONDS = 12 * 3600
# A crate legitimately has a few live hashes per profile (library, test
# harness, build-script compile and run), so only older hashes are pruned.
KEPT_ARTIFACT_HASHES = 3
ARTIFACT = re.compile(r"^(?:lib)?(?P<name>.+)-(?P<hash>[0-9a-f]{16})(?:\..*)?$")


def tree_size(path: Path) -> int:
    """Return allocated bytes under `path` without following symlinks."""
    try:
        if path.is_symlink() or not path.is_dir():
            return path.lstat().st_blocks * 512
    except FileNotFoundError:
        return 0
    total = 0
    stack = [path]
    while stack:
        current = stack.pop()
        try:
            entries = list(os.scandir(current))
        except (FileNotFoundError, PermissionError, NotADirectoryError):
            continue
        for entry in entries:
            try:
                info = entry.stat(follow_symlinks=False)
            except FileNotFoundError:
                continue
            total += info.st_blocks * 512
            if entry.is_dir(follow_symlinks=False):
                stack.append(Path(entry.path))
    return total


def remove(path: Path, dry_run: bool, log: list[str]) -> int:
    size = tree_size(path)
    log.append(f"remove {path} ({size / GIB:.2f} GiB)")
    if not dry_run:
        if path.is_dir() and not path.is_symlink():
            shutil.rmtree(path, ignore_errors=True)
        else:
            path.unlink(missing_ok=True)
    return size


def temp_root() -> Path:
    return Path(tempfile.gettempdir())


def taro_temp_dirs(root: Path) -> list[Path]:
    """Runner work directories and the `taro run` script cache."""
    try:
        return sorted(
            entry for entry in root.iterdir()
            if entry.name.startswith(("taro-", "taro_")) and entry.is_dir()
        )
    except FileNotFoundError:
        return []


def measured_paths(repo: Path, tmp: Path) -> list[Path]:
    return [repo, *taro_temp_dirs(tmp)]


def usage(repo: Path, tmp: Path) -> int:
    return sum(tree_size(path) for path in measured_paths(repo, tmp))


def is_stale(path: Path, now: float, age: float) -> bool:
    try:
        return now - path.stat().st_mtime > age
    except FileNotFoundError:
        return False


def contains_active_sdk(directory: Path) -> bool:
    """Keep the SDK executing this process (and an owning test directory).

    It remains measured; if other caches cannot make room, enforce fails rather
    than removing the compiler that a later gate stage still needs.
    """
    home = os.environ.get("TARO_HOME")
    return bool(home) and Path(home).resolve().is_relative_to(directory.resolve())


def prune_temp(tmp: Path, now: float, everything: bool, dry_run: bool, log: list[str]) -> int:
    freed = 0
    for directory in taro_temp_dirs(tmp):
        if contains_active_sdk(directory):
            continue
        if directory.name == "taro-scripts":
            for cache in sorted(directory.iterdir()):
                if everything or is_stale(cache, now, STALE_TEMP_SECONDS):
                    freed += remove(cache, dry_run, log)
        elif everything or is_stale(directory, now, STALE_TEMP_SECONDS):
            freed += remove(directory, dry_run, log)
    return freed


def nested_package_targets(repo: Path) -> list[Path]:
    """Taro package build outputs outside the Cargo workspace target."""
    found = []
    for top in ("std", "showcase", "examples", "language_tests", "development"):
        base = repo / top
        if not base.is_dir():
            continue
        for current, dirs, _ in os.walk(base):
            if "target" in dirs:
                found.append(Path(current) / "target")
                dirs.remove("target")
            dirs[:] = [name for name in dirs if name != "node_modules"]
    return found


@contextlib.contextmanager
def cargo_lock(profile_dir: Path) -> Iterator[bool]:
    """Hold Cargo's build lock for a profile; yield False if a build owns it."""
    lock_path = profile_dir / ".cargo-lock"
    if not lock_path.exists():
        yield True
        return
    with open(lock_path, "a+") as handle:
        try:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            yield False
            return
        try:
            yield True
        finally:
            fcntl.flock(handle, fcntl.LOCK_UN)


def superseded_artifacts(profile_dir: Path) -> list[Path]:
    """Artifacts whose crate has newer builds under other hashes.

    Removed features and changed flags leave whole extra copies of each crate
    behind. Keeping the newest hashes per crate name preserves the builds in
    current use. A hash is removed from deps, fingerprints and build outputs
    together, so Cargo sees the unit as never built and rebuilds it if needed.
    """
    groups: dict[str, dict[str, list[Path]]] = defaultdict(lambda: defaultdict(list))
    for sub in ("deps", ".fingerprint", "build"):
        directory = profile_dir / sub
        if not directory.is_dir():
            continue
        for entry in directory.iterdir():
            match = ARTIFACT.match(entry.name)
            if match:
                groups[match["name"]][match["hash"]].append(entry)

    stale = []
    for hashes in groups.values():
        def newest(paths: list[Path]) -> float:
            return max((path.lstat().st_mtime for path in paths), default=0.0)

        ordered = sorted(hashes.values(), key=newest, reverse=True)
        for paths in ordered[KEPT_ARTIFACT_HASHES:]:
            stale.extend(paths)
    return stale


def prune_cargo(
    repo: Path, profiles: list[str], whole: bool, dry_run: bool, log: list[str]
) -> int:
    freed = 0
    for profile in profiles:
        profile_dir = repo / "target" / profile
        if not profile_dir.is_dir():
            continue
        with cargo_lock(profile_dir) as acquired:
            if not acquired:
                log.append(f"skip {profile_dir}: a Cargo build holds its lock")
                continue
            if whole:
                freed += remove(profile_dir, dry_run, log)
                continue
            incremental = profile_dir / "incremental"
            if incremental.is_dir():
                for cache in sorted(incremental.iterdir()):
                    freed += remove(cache, dry_run, log)
            for path in superseded_artifacts(profile_dir):
                freed += remove(path, dry_run, log)
    return freed


def largest_entries(repo: Path, tmp: Path, count: int = 8) -> list[tuple[int, Path]]:
    candidates = [*repo.iterdir(), *taro_temp_dirs(tmp)]
    sized = [(tree_size(path), path) for path in candidates]
    return sorted(sized, reverse=True)[:count]


def guard(
    limit: float,
    target: float,
    repo: Path = PROJECT_ROOT,
    tmp: Path | None = None,
    dry_run: bool = False,
    now: float | None = None,
) -> tuple[int, list[str]]:
    """Prune toward `target` bytes; return the final usage and actions taken."""
    tmp = tmp or temp_root()
    now = time.time() if now is None else now
    log: list[str] = []

    current = usage(repo, tmp) - prune_temp(tmp, now, False, dry_run, log)
    stages = [
        lambda: prune_temp(tmp, now, True, dry_run, log),
        lambda: sum(remove(path, dry_run, log) for path in nested_package_targets(repo)),
        lambda: prune_cargo(repo, ["release", "debug"], False, dry_run, log),
    ]
    for stage in stages:
        if current <= target:
            break
        current -= stage()
    for profile in ("release", "debug"):
        if current <= limit:
            break
        current -= prune_cargo(repo, [profile], True, dry_run, log)
    return current, log


def enforce(quiet: bool = True) -> None:
    """Entry point for build scripts: prune, and refuse to build over budget."""
    limit = float(os.environ.get("TARO_DISK_LIMIT_GIB", DEFAULT_LIMIT_GIB)) * GIB
    target = float(os.environ.get("TARO_DISK_TARGET_GIB", DEFAULT_TARGET_GIB)) * GIB
    current, log = guard(limit, target)
    if not quiet:
        for line in log:
            print(f"disk-guard: {line}")
    if current > limit:
        report_over_budget(current, limit)
        raise SystemExit(1)


def report_over_budget(current: int, limit: float, tmp: Path | None = None) -> None:
    print(
        f"disk-guard: {current / GIB:.1f} GiB is over the {limit / GIB:.1f} GiB budget "
        "after pruning build caches. Largest entries:",
        file=sys.stderr,
    )
    for size, path in largest_entries(PROJECT_ROOT, tmp or temp_root()):
        print(f"  {size / GIB:6.2f} GiB  {path}", file=sys.stderr)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--limit-gib", type=float,
                        default=float(os.environ.get("TARO_DISK_LIMIT_GIB", DEFAULT_LIMIT_GIB)))
    parser.add_argument("--target-gib", type=float,
                        default=float(os.environ.get("TARO_DISK_TARGET_GIB", DEFAULT_TARGET_GIB)))
    parser.add_argument("--dry-run", action="store_true", help="report without deleting")
    parser.add_argument("--quiet", action="store_true", help="print only when over budget")
    parser.add_argument("--report", action="store_true", help="measure only")
    args = parser.parse_args()

    limit, target = args.limit_gib * GIB, args.target_gib * GIB
    if args.report:
        current = usage(PROJECT_ROOT, temp_root())
        print(f"{current / GIB:.2f} GiB used of {args.limit_gib:.1f} GiB")
        for size, path in largest_entries(PROJECT_ROOT, temp_root()):
            print(f"  {size / GIB:6.2f} GiB  {path}")
        return 0

    current, log = guard(limit, target, dry_run=args.dry_run)
    if not args.quiet:
        for line in log:
            print(line)
        print(f"{current / GIB:.2f} GiB used of {args.limit_gib:.1f} GiB")
    if current > limit:
        report_over_budget(current, limit)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
