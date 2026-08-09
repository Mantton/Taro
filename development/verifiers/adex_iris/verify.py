#!/usr/bin/env python3
"""Prepare UCI Iris and run the deterministic Taro classifier offline."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import tomllib
import urllib.request
import zipfile


REPO_ROOT = Path(__file__).resolve().parents[3]
PROJECT_ROOT = Path(__file__).resolve().parent
MANIFEST_PATH = PROJECT_ROOT / "verifier.toml"
CACHE_ROOT = REPO_ROOT / "target" / "verifiers" / "adex_iris"
PACKAGE = REPO_ROOT / "showcase" / "adex_iris"
DEFAULT_TARO = REPO_ROOT / "dist" / "bin" / "taro"
DEFAULT_STD = REPO_ROOT / "std"
MAX_ARCHIVE_BYTES = 1_000_000


class VerificationError(RuntimeError):
    pass


def load_manifest(path: Path = MANIFEST_PATH) -> dict[str, object]:
    with path.open("rb") as handle:
        manifest = tomllib.load(handle)
    required = {
        "format_version",
        "url",
        "archive_sha256",
        "member",
        "member_sha256",
        "member_bytes",
        "rows",
        "classes",
        "rows_per_class",
    }
    missing = sorted(required - manifest.keys())
    if missing:
        raise VerificationError(f"manifest missing: {', '.join(missing)}")
    if manifest["format_version"] != 1:
        raise VerificationError("unsupported manifest format")
    return manifest


def require_digest(contents: bytes, expected: str, label: str) -> None:
    actual = hashlib.sha256(contents).hexdigest()
    if actual != expected:
        raise VerificationError(f"{label} SHA-256 mismatch: expected {expected}, found {actual}")


def validate_dataset(contents: bytes, manifest: dict[str, object]) -> None:
    if len(contents) != manifest["member_bytes"]:
        raise VerificationError(
            f"dataset byte count mismatch: expected {manifest['member_bytes']}, found {len(contents)}"
        )
    require_digest(contents, str(manifest["member_sha256"]), "dataset")
    try:
        text = contents.decode("ascii")
    except UnicodeDecodeError as error:
        raise VerificationError(f"dataset is not ASCII: {error}") from error

    classes = list(manifest["classes"])
    counts = {name: 0 for name in classes}
    rows = 0
    for line_number, fields in enumerate(csv.reader(io.StringIO(text)), start=1):
        if not fields:
            continue
        if len(fields) != 5:
            raise VerificationError(f"line {line_number}: expected five fields")
        try:
            features = [float(value) for value in fields[:4]]
        except ValueError as error:
            raise VerificationError(f"line {line_number}: invalid feature") from error
        if not all(value == value and abs(value) != float("inf") for value in features):
            raise VerificationError(f"line {line_number}: non-finite feature")
        label = fields[4]
        if label not in counts:
            raise VerificationError(f"line {line_number}: unknown class {label!r}")
        counts[label] += 1
        rows += 1

    if rows != manifest["rows"]:
        raise VerificationError(f"expected {manifest['rows']} rows, found {rows}")
    expected_per_class = manifest["rows_per_class"]
    if any(count != expected_per_class for count in counts.values()):
        raise VerificationError(f"unexpected class counts: {counts}")


def extract_dataset(archive: bytes, manifest: dict[str, object]) -> bytes:
    require_digest(archive, str(manifest["archive_sha256"]), "archive")
    try:
        with zipfile.ZipFile(io.BytesIO(archive)) as zipped:
            members = zipped.namelist()
            member = str(manifest["member"])
            if member not in members:
                raise VerificationError(f"archive does not contain {member!r}")
            info = zipped.getinfo(member)
            if info.file_size > MAX_ARCHIVE_BYTES:
                raise VerificationError("dataset member exceeds size limit")
            contents = zipped.read(info)
    except zipfile.BadZipFile as error:
        raise VerificationError(f"invalid ZIP archive: {error}") from error
    validate_dataset(contents, manifest)
    return contents


def cache_path(manifest: dict[str, object]) -> Path:
    return CACHE_ROOT / str(manifest["member_sha256"]) / str(manifest["member"])


def prepared_dataset(manifest: dict[str, object]) -> Path:
    path = cache_path(manifest)
    if not path.is_file():
        raise VerificationError("Iris data is not prepared; run `make -C showcase/adex_iris prepare`")
    validate_dataset(path.read_bytes(), manifest)
    return path


def prepare(manifest: dict[str, object], refresh: bool) -> Path:
    destination = cache_path(manifest)
    if destination.is_file() and not refresh:
        validate_dataset(destination.read_bytes(), manifest)
        print(f"Prepared dataset already valid: {destination}")
        return destination

    request = urllib.request.Request(str(manifest["url"]), headers={"User-Agent": "Taro-verifier/1"})
    with urllib.request.urlopen(request, timeout=30) as response:
        archive = response.read(MAX_ARCHIVE_BYTES + 1)
    if len(archive) > MAX_ARCHIVE_BYTES:
        raise VerificationError("archive exceeds size limit")
    contents = extract_dataset(archive, manifest)

    destination.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(prefix="iris-", suffix=".data", dir=destination.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as staged:
            staged.write(contents)
            staged.flush()
            os.fsync(staged.fileno())
        validate_dataset(temporary.read_bytes(), manifest)
        os.replace(temporary, destination)
    finally:
        temporary.unlink(missing_ok=True)
    print(f"Prepared {manifest['name']}: {destination}")
    return destination


def run_command(command: list[str], environment: dict[str, str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        command,
        cwd=REPO_ROOT,
        env=environment,
        text=True,
        capture_output=True,
    )


def require_success(completed: subprocess.CompletedProcess[str], label: str) -> None:
    if completed.returncode != 0:
        if completed.stdout:
            print(completed.stdout, end="", file=sys.stderr)
        if completed.stderr:
            print(completed.stderr, end="", file=sys.stderr)
        raise VerificationError(f"{label} failed with exit {completed.returncode}")


def validate_metrics(payload: object) -> dict[str, object]:
    if not isinstance(payload, dict) or payload.get("schema") != 1:
        raise VerificationError("classifier returned an unsupported result schema")
    folds = payload.get("folds")
    if not isinstance(folds, list) or len(folds) != 5:
        raise VerificationError("classifier must return five folds")
    if not all(isinstance(fold, dict) for fold in folds):
        raise VerificationError("classifier returned malformed fold metrics")
    if sorted(fold.get("fold") for fold in folds) != list(range(5)):
        raise VerificationError("classifier returned invalid fold identifiers")
    if any(
        fold.get("training_samples") != 120
        or fold.get("testing_samples") != 30
        or not isinstance(fold.get("correct"), int)
        or not 0 <= fold["correct"] <= 30
        or not isinstance(fold.get("loss"), (int, float))
        or not float("-inf") < fold["loss"] < float("inf")
        or fold.get("finite") is not True
        for fold in folds
    ):
        raise VerificationError("classifier returned invalid per-fold metrics")
    if payload.get("samples") != 150:
        raise VerificationError("classifier did not evaluate 150 held-out samples")
    correct = payload.get("correct")
    if not isinstance(correct, int) or correct < 135 or correct > 150:
        raise VerificationError(f"classifier accuracy gate failed: {correct}/150")
    if sum(fold["correct"] for fold in folds) != correct:
        raise VerificationError("classifier fold totals do not match aggregate correct count")
    accuracy = payload.get("accuracy")
    if (
        not isinstance(accuracy, (int, float))
        or not float("-inf") < accuracy < float("inf")
        or abs(accuracy - correct / 150.0) > 1e-9
    ):
        raise VerificationError("classifier returned inconsistent aggregate accuracy")
    if payload.get("finite") is not True:
        raise VerificationError("classifier reported non-finite state")
    confusion = payload.get("confusion")
    if (
        not isinstance(confusion, list)
        or len(confusion) != 3
        or any(
            not isinstance(row, list)
            or len(row) != 3
            or any(not isinstance(cell, int) or cell < 0 for cell in row)
            for row in confusion
        )
        or sum(sum(row) for row in confusion) != 150
        or any(sum(row) != 50 for row in confusion)
        or sum(confusion[index][index] for index in range(3)) != correct
    ):
        raise VerificationError("classifier returned an invalid confusion matrix")
    return payload


def run(manifest: dict[str, object], taro: Path, std_path: Path) -> None:
    dataset = prepared_dataset(manifest)
    if not taro.is_file():
        raise VerificationError(f"Taro compiler not found at {taro}; run `make dist`")
    environment = os.environ.copy()
    environment["TARO_HOME"] = str(taro.parent.parent)

    for profile in ("debug", "release"):
        command = [str(taro), "test", str(PACKAGE), "--std-path", str(std_path)]
        if profile == "release":
            command.append("--release")
        completed = run_command(command, environment)
        require_success(completed, f"{profile} showcase tests")
        print(completed.stdout, end="")

    smoke_results: list[dict[str, object]] = []
    for profile in ("debug", "release"):
        command = [
            str(taro),
            "run",
            str(PACKAGE),
            "--std-path",
            str(std_path),
        ]
        if profile == "release":
            command.append("--release")
        command.extend(["--", "--data", str(dataset), "--smoke", "--format", "json"])
        completed = run_command(command, environment)
        require_success(completed, f"{profile} smoke run")
        try:
            smoke = json.loads(completed.stdout)
        except json.JSONDecodeError as error:
            raise VerificationError(f"{profile} smoke returned invalid JSON: {error}") from error
        if not isinstance(smoke, dict) or smoke.get("schema") != 1 or smoke.get("finite") is not True:
            raise VerificationError(f"{profile} smoke returned invalid metrics")
        smoke_results.append(smoke)
    debug_smoke, release_smoke = smoke_results
    if debug_smoke.get("prediction") != release_smoke.get("prediction"):
        raise VerificationError("debug/release smoke predictions disagree")
    debug_loss = debug_smoke.get("loss")
    release_loss = release_smoke.get("loss")
    if not isinstance(debug_loss, (int, float)) or not isinstance(release_loss, (int, float)):
        raise VerificationError("debug/release smoke loss is not numeric")
    if abs(debug_loss - release_loss) > 1e-10:
        raise VerificationError("debug/release smoke losses differ by more than 1e-10")

    command = [
        str(taro),
        "run",
        str(PACKAGE),
        "--std-path",
        str(std_path),
        "--release",
        "--",
        "--data",
        str(dataset),
        "--fold",
        "all",
        "--format",
        "json",
    ]
    completed = run_command(command, environment)
    if not completed.stdout.strip():
        require_success(completed, "classifier")
        raise VerificationError("classifier returned no metrics")
    try:
        payload = validate_metrics(json.loads(completed.stdout))
    except json.JSONDecodeError as error:
        raise VerificationError(f"classifier returned invalid JSON: {error}") from error
    require_success(completed, "classifier")
    print(json.dumps(payload, sort_keys=True, separators=(",", ":")))
    print(f"PASS: AdEx Iris classifier — {payload['correct']}/150")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    prepare_parser = subparsers.add_parser("prepare")
    prepare_parser.add_argument("--refresh", action="store_true")
    run_parser = subparsers.add_parser("run")
    run_parser.add_argument("--taro", type=Path, default=DEFAULT_TARO)
    run_parser.add_argument("--std-path", type=Path, default=DEFAULT_STD)
    args = parser.parse_args()

    try:
        manifest = load_manifest()
        if args.command == "prepare":
            prepare(manifest, args.refresh)
        else:
            run(manifest, args.taro.resolve(), args.std_path.resolve())
    except (OSError, VerificationError, urllib.error.URLError) as error:
        print(f"adex-iris verifier error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
