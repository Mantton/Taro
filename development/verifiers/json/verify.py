#!/usr/bin/env python3
"""Prepare and run Taro's pinned multi-corpus JSON verifier."""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import tomllib
from typing import Callable, Iterable
from urllib.parse import quote, urlparse
from urllib.request import Request, urlopen


REPO_ROOT = Path(__file__).resolve().parents[3]
VERIFIER_ROOT = Path(__file__).resolve().parent
DEFAULT_MANIFEST = VERIFIER_ROOT / "verifier.toml"
DEFAULT_CACHE_BASE = REPO_ROOT / "target/verifiers/json"
DEFAULT_PACKAGE = VERIFIER_ROOT
DEFAULT_BINARY = DEFAULT_CACHE_BASE / "json-verifier"
DEFAULT_TARO = REPO_ROOT / "dist/bin/taro"
DEFAULT_STD = REPO_ROOT / "std"
BUILD_DIST = REPO_ROOT / "development/scripts/build_dist.py"

PROTOCOL_VERSION = 1
INDEX_VERSION = 1
FULL_MODES = (
    ("oneshot", 0),
    ("stream", 1),
    ("stream", 2),
    ("stream", 3),
    ("stream", 7),
    ("stream", 4096),
)
DOCUMENT_MODES = (("oneshot", 0), ("stream", 7), ("stream", 4096))
MATRICES = {"full": FULL_MODES, "documents": DOCUMENT_MODES}
PROFILES = ("rfc", "safe")
CLASSIFICATIONS = ("yes", "no", "implementation")
PREFIX_BY_CLASS = {"yes": "y_", "no": "n_", "implementation": "i_"}
CLASS_BY_PREFIX = {value: key for key, value in PREFIX_BY_CLASS.items()}
SAFE_POLICY_ERRORS = {"duplicateKey", "depthLimit", "inputLimit"}
ERROR_KINDS = {
    "unexpectedEof",
    "unexpectedToken",
    "trailingData",
    "invalidNumber",
    "invalidEscape",
    "invalidUnicodeEscape",
    "invalidUtf8",
    "unescapedControlCharacter",
    "duplicateKey",
    "depthLimit",
    "inputLimit",
    "io",
}
RESULT_FIELDS = {
    "version",
    "file",
    "class",
    "profile",
    "mode",
    "chunk_size",
    "input_bytes",
    "accepted",
    "canonical",
    "error_kind",
    "error_offset",
    "error_line",
    "error_column",
    "error_path",
    "error_invariants",
}
INDEX_FIELDS = {"version", "suite", "revision", "cases"}
INDEX_CASE_FIELDS = {"file", "source", "class", "size", "sha256"}
TREE_HASH_RECIPE = (
    "sha256-v2(source-relative-path NUL classification NUL decimal-size NUL "
    "contents, byte-sorted)"
)
SHA256_PATTERN = re.compile(r"[0-9a-f]{64}\Z")
REVISION_PATTERN = re.compile(r"[0-9a-f]{40}\Z")
SUITE_ID_PATTERN = re.compile(r"[a-z0-9](?:[a-z0-9-]*[a-z0-9])?\Z")

UrlOpen = Callable[..., object]


class VerificationError(RuntimeError):
    """The verifier cannot establish the claimed result."""


class VerifierProcessError(VerificationError):
    """The native verifier failed outside its versioned result protocol."""

    def __init__(self, kind: str, detail: str) -> None:
        super().__init__(f"verifier {kind}: {detail}")
        self.kind = kind


@dataclass(frozen=True)
class ClassificationRule:
    classification: str
    patterns: tuple[str, ...]


@dataclass(frozen=True)
class Selection:
    root: str
    include: tuple[str, ...]
    default_classification: str | None
    rules: tuple[ClassificationRule, ...]


@dataclass(frozen=True)
class VerifierConfig:
    id: str
    name: str
    matrix: str
    repository: str
    revision: str
    revision_date: str
    license: str
    license_path: str
    license_size: int
    license_sha256: str
    fetch: str
    archive_max_bytes: int | None
    file_count: int
    total_bytes: int
    tree_hash: str
    tree_sha256: str
    selections: tuple[Selection, ...]

    @property
    def modes(self) -> tuple[tuple[str, int], ...]:
        return MATRICES[self.matrix]


@dataclass(frozen=True)
class SourceCase:
    path: str
    classification: str
    data: bytes


@dataclass(frozen=True)
class CorpusFile:
    name: str
    classification: str
    size: int
    source_path: str
    sha256: str


@dataclass(frozen=True)
class CorpusInfo:
    config: VerifierConfig
    directory: Path
    files: tuple[CorpusFile, ...]

    def display_name(self, normalized: str) -> str:
        for item in self.files:
            if item.name == normalized:
                return item.source_path
        return normalized


@dataclass(frozen=True)
class Result:
    file: str
    classification: str
    profile: str
    mode: str
    chunk_size: int
    input_bytes: int
    accepted: bool
    canonical: bool
    error_kind: str
    error_offset: int
    error_line: int
    error_column: int
    error_path: str
    error_invariants: bool

    def key(self) -> tuple[str, str, str, int]:
        return (self.file, self.profile, self.mode, self.chunk_size)

    def diagnostic(self) -> tuple[object, ...]:
        return (
            self.accepted,
            self.canonical,
            self.error_kind,
            self.error_offset,
            self.error_line,
            self.error_column,
            self.error_path,
        )


@dataclass(frozen=True)
class DiagnosticDifference:
    file: str
    profile: str
    oneshot: Result
    stream: Result


@dataclass(frozen=True)
class Summary:
    row_count: int
    counts: dict[tuple[str, str, bool], int]
    safe_policy_deviations: tuple[Result, ...]
    implementation_decisions: tuple[tuple[str, Result, Result], ...]
    diagnostic_differences: tuple[DiagnosticDifference, ...]


def _required_string(table: dict[str, object], field: str) -> str:
    value = table.get(field)
    if not isinstance(value, str) or not value:
        raise VerificationError(f"manifest field {field!r} must be a non-empty string")
    return value


def _required_positive_int(table: dict[str, object], field: str) -> int:
    value = table.get(field)
    if type(value) is not int or value < 1:
        raise VerificationError(f"manifest field {field!r} must be a positive integer")
    return value


def _string_list(table: dict[str, object], field: str) -> tuple[str, ...]:
    value = table.get(field)
    if (
        not isinstance(value, list)
        or not value
        or any(not isinstance(item, str) or not item for item in value)
    ):
        raise VerificationError(f"manifest field {field!r} must be a non-empty string array")
    return tuple(value)


def _safe_relative_path(value: str, field: str, *, allow_dot: bool = False) -> str:
    path = PurePosixPath(value)
    if (
        path.is_absolute()
        or ".." in path.parts
        or "\\" in value
        or "\0" in value
        or (not path.parts and not (allow_dot and value == "."))
    ):
        raise VerificationError(f"manifest field {field!r} must be a safe relative path")
    return value


def _safe_pattern(value: str, field: str) -> str:
    if value.startswith("/") or "\\" in value or "\0" in value:
        raise VerificationError(f"manifest field {field!r} must be a safe relative glob")
    if ".." in PurePosixPath(value).parts:
        raise VerificationError(f"manifest field {field!r} must not traverse parents")
    return value


def _check_fields(table: dict[str, object], expected: set[str], context: str) -> None:
    unknown = sorted(set(table) - expected)
    if unknown:
        raise VerificationError(
            f"{context} contains unsupported fields: "
            + ", ".join(f"{context}.{field}" for field in unknown)
        )


def _load_selection(raw: object, index: int) -> Selection:
    if not isinstance(raw, dict):
        raise VerificationError(f"selection {index} must be a table")
    _check_fields(
        raw,
        {"root", "include", "default_classification", "rule"},
        f"selection[{index}]",
    )
    root = _safe_relative_path(
        _required_string(raw, "root"), f"selection[{index}].root", allow_dot=True
    )
    include = tuple(
        _safe_pattern(item, f"selection[{index}].include")
        for item in _string_list(raw, "include")
    )
    default = raw.get("default_classification")
    if default is not None and default not in CLASSIFICATIONS:
        raise VerificationError(
            f"selection[{index}].default_classification must be a known classification"
        )

    rules_raw = raw.get("rule", [])
    if not isinstance(rules_raw, list):
        raise VerificationError(f"selection[{index}].rule must be an array of tables")
    rules: list[ClassificationRule] = []
    for rule_index, rule_raw in enumerate(rules_raw):
        if not isinstance(rule_raw, dict):
            raise VerificationError(
                f"selection[{index}].rule[{rule_index}] must be a table"
            )
        _check_fields(
            rule_raw,
            {"classification", "patterns"},
            f"selection[{index}].rule[{rule_index}]",
        )
        classification = _required_string(rule_raw, "classification")
        if classification not in CLASSIFICATIONS:
            raise VerificationError(
                f"selection[{index}].rule[{rule_index}] has unknown classification"
            )
        patterns = tuple(
            _safe_pattern(item, f"selection[{index}].rule[{rule_index}].patterns")
            for item in _string_list(rule_raw, "patterns")
        )
        rules.append(ClassificationRule(classification, patterns))
    if default is None and not rules:
        raise VerificationError(f"selection {index} has no classification policy")
    return Selection(root, include, default, tuple(rules))


def load_config(path: Path) -> VerifierConfig:
    try:
        document = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        raise VerificationError(f"cannot read suite manifest {path}: {error}") from error
    _check_fields(
        document,
        {"format_version", "id", "name", "matrix", "source", "expected", "selection"},
        "manifest",
    )
    if document.get("format_version") != 1:
        raise VerificationError("suite manifest format_version must be 1")

    source = document.get("source")
    expected = document.get("expected")
    selections = document.get("selection")
    if not isinstance(source, dict) or not isinstance(expected, dict):
        raise VerificationError("suite manifest must contain [source] and [expected] tables")
    if not isinstance(selections, list) or not selections:
        raise VerificationError("suite manifest must contain at least one [[selection]]")
    _check_fields(
        source,
        {
            "repository",
            "revision",
            "revision_date",
            "license",
            "license_path",
            "license_size",
            "license_sha256",
            "fetch",
            "archive_max_bytes",
        },
        "source",
    )
    _check_fields(
        expected,
        {"file_count", "total_bytes", "tree_hash", "tree_sha256"},
        "expected",
    )

    suite_id = _required_string(document, "id")
    if SUITE_ID_PATTERN.fullmatch(suite_id) is None:
        raise VerificationError("manifest id must be a lowercase kebab-case identifier")
    matrix = _required_string(document, "matrix")
    if matrix not in MATRICES:
        raise VerificationError(f"manifest matrix must be one of {', '.join(MATRICES)}")

    repository = _required_string(source, "repository")
    parsed_repository = urlparse(repository)
    if (
        parsed_repository.scheme != "https"
        or parsed_repository.netloc != "github.com"
        or parsed_repository.query
        or parsed_repository.fragment
    ):
        raise VerificationError("source.repository must be an HTTPS github.com URL")
    _github_coordinates(repository)

    revision = _required_string(source, "revision")
    if REVISION_PATTERN.fullmatch(revision) is None:
        raise VerificationError("source.revision must be a full lowercase Git commit ID")
    license_sha256 = _required_string(source, "license_sha256")
    tree_sha256 = _required_string(expected, "tree_sha256")
    if SHA256_PATTERN.fullmatch(license_sha256) is None:
        raise VerificationError("source.license_sha256 must be lowercase SHA-256")
    if SHA256_PATTERN.fullmatch(tree_sha256) is None:
        raise VerificationError("expected.tree_sha256 must be lowercase SHA-256")
    if _required_string(expected, "tree_hash") != TREE_HASH_RECIPE:
        raise VerificationError("suite manifest uses an unknown corpus tree hash recipe")

    fetch = _required_string(source, "fetch")
    archive_max = source.get("archive_max_bytes")
    if fetch == "archive":
        archive_max = _required_positive_int(source, "archive_max_bytes")
    elif fetch == "files":
        if archive_max is not None:
            raise VerificationError("source.archive_max_bytes is only valid for archive fetches")
    else:
        raise VerificationError("source.fetch must be 'archive' or 'files'")

    return VerifierConfig(
        id=suite_id,
        name=_required_string(document, "name"),
        matrix=matrix,
        repository=repository.rstrip("/"),
        revision=revision,
        revision_date=_required_string(source, "revision_date"),
        license=_required_string(source, "license"),
        license_path=_safe_relative_path(
            _required_string(source, "license_path"), "source.license_path"
        ),
        license_size=_required_positive_int(source, "license_size"),
        license_sha256=license_sha256,
        fetch=fetch,
        archive_max_bytes=archive_max if isinstance(archive_max, int) else None,
        file_count=_required_positive_int(expected, "file_count"),
        total_bytes=_required_positive_int(expected, "total_bytes"),
        tree_hash=TREE_HASH_RECIPE,
        tree_sha256=tree_sha256,
        selections=tuple(_load_selection(raw, index) for index, raw in enumerate(selections)),
    )


def load_registry(path: Path) -> tuple[VerifierConfig, ...]:
    try:
        document = tomllib.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as error:
        raise VerificationError(f"cannot read verifier registry {path}: {error}") from error
    _check_fields(document, {"format_version", "suites"}, "registry")
    if document.get("format_version") != 2:
        raise VerificationError("verifier registry format_version must be 2")
    manifests = _string_list(document, "suites")
    configs: list[VerifierConfig] = []
    seen_paths: set[Path] = set()
    seen_ids: set[str] = set()
    for entry in manifests:
        _safe_relative_path(entry, "registry.suites")
        manifest = (path.parent / entry).resolve()
        try:
            manifest.relative_to(path.parent.resolve())
        except ValueError as error:
            raise VerificationError("registry suite path escapes the verifier directory") from error
        if manifest in seen_paths:
            raise VerificationError(f"registry repeats suite manifest {entry!r}")
        seen_paths.add(manifest)
        config = load_config(manifest)
        if config.id in seen_ids:
            raise VerificationError(f"registry repeats suite id {config.id!r}")
        seen_ids.add(config.id)
        configs.append(config)
    return tuple(configs)


def _github_coordinates(repository: str) -> tuple[str, str]:
    path = urlparse(repository).path.strip("/").split("/")
    if len(path) != 2 or not all(path):
        raise VerificationError("GitHub repository URL must identify exactly owner/repository")
    return path[0], path[1]


def _glob_matches(path: str, pattern: str) -> bool:
    # Corpus globs deliberately let '*' span '/', which keeps recursive source
    # selections concise while still pinning the resulting exact tree digest.
    import fnmatch

    return fnmatch.fnmatchcase(path, pattern)


def _relative_to_root(source_path: str, root: str) -> str | None:
    if root == ".":
        return source_path
    if source_path.startswith(root + "/"):
        return source_path[len(root) + 1 :]
    return None


def classify_source_path(config: VerifierConfig, source_path: str) -> str | None:
    matches: list[str] = []
    for selection in config.selections:
        relative = _relative_to_root(source_path, selection.root)
        if relative is None or not any(
            _glob_matches(relative, pattern) for pattern in selection.include
        ):
            continue
        classification = selection.default_classification
        for rule in selection.rules:
            if any(_glob_matches(relative, pattern) for pattern in rule.patterns):
                classification = rule.classification
                break
        if classification is None:
            raise VerificationError(
                f"selected source file has no classification: {config.id}:{source_path}"
            )
        matches.append(classification)
    if len(matches) > 1:
        raise VerificationError(
            f"source file matches multiple selections: {config.id}:{source_path}"
        )
    return matches[0] if matches else None


def source_tree_digest(cases: Iterable[SourceCase]) -> str:
    digest = hashlib.sha256()
    for case in sorted(cases, key=lambda item: item.path.encode("utf-8")):
        digest.update(case.path.encode("utf-8"))
        digest.update(b"\0")
        digest.update(case.classification.encode("ascii"))
        digest.update(b"\0")
        digest.update(str(len(case.data)).encode("ascii"))
        digest.update(b"\0")
        digest.update(case.data)
    return digest.hexdigest()


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(64 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _validate_source(config: VerifierConfig, cases: list[SourceCase], license_data: bytes) -> None:
    if len(license_data) != config.license_size:
        raise VerificationError(f"{config.id} license size does not match the pinned manifest")
    if hashlib.sha256(license_data).hexdigest() != config.license_sha256:
        raise VerificationError(f"{config.id} license checksum does not match the pinned manifest")
    paths = [case.path for case in cases]
    if len(paths) != len(set(paths)):
        raise VerificationError(f"{config.id} selected duplicate source paths")
    if len(cases) != config.file_count:
        raise VerificationError(
            f"{config.id} file count changed: expected {config.file_count}, found {len(cases)}"
        )
    total = sum(len(case.data) for case in cases)
    if total != config.total_bytes:
        raise VerificationError(
            f"{config.id} byte count changed: expected {config.total_bytes}, found {total}"
        )
    actual_digest = source_tree_digest(cases)
    if actual_digest != config.tree_sha256:
        raise VerificationError(
            f"{config.id} tree checksum changed: expected {config.tree_sha256}, "
            f"found {actual_digest}"
        )


def _fetch_bytes(url: str, *, maximum: int, opener: UrlOpen = urlopen) -> bytes:
    request = Request(url, headers={"User-Agent": "Taro-JSON-verifier/2"})
    try:
        with opener(request, timeout=60) as response:  # type: ignore[attr-defined]
            data = response.read(maximum + 1)
    except OSError as error:
        raise VerificationError(f"cannot download {url}: {error}") from error
    if len(data) > maximum:
        raise VerificationError(f"download exceeds the declared size limit: {url}")
    return data


def _fetch_archive_source(
    config: VerifierConfig, *, opener: UrlOpen
) -> tuple[list[SourceCase], bytes]:
    owner, repository = _github_coordinates(config.repository)
    assert config.archive_max_bytes is not None
    url = (
        f"https://codeload.github.com/{quote(owner)}/{quote(repository)}/tar.gz/"
        f"{quote(config.revision)}"
    )
    raw = _fetch_bytes(url, maximum=config.archive_max_bytes, opener=opener)
    selected: dict[str, SourceCase] = {}
    license_data: bytes | None = None
    archive_root: str | None = None
    member_count = 0
    try:
        with tarfile.open(fileobj=io.BytesIO(raw), mode="r:gz") as archive:
            for member in archive:
                member_count += 1
                if member_count > 100_000:
                    raise VerificationError(f"{config.id} archive contains too many entries")
                path = PurePosixPath(member.name)
                if path.is_absolute() or ".." in path.parts or len(path.parts) < 2:
                    continue
                root = path.parts[0]
                if archive_root is None:
                    archive_root = root
                elif root != archive_root:
                    raise VerificationError(f"{config.id} archive has multiple roots")
                if not member.isfile():
                    continue
                source_path = PurePosixPath(*path.parts[1:]).as_posix()
                classification = classify_source_path(config, source_path)
                is_license = source_path == config.license_path
                if classification is None and not is_license:
                    continue
                maximum = config.license_size if is_license else config.total_bytes
                if member.size < 0 or member.size > maximum:
                    raise VerificationError(
                        f"{config.id} archive entry exceeds its declared bound: {source_path}"
                    )
                stream = archive.extractfile(member)
                if stream is None:
                    raise VerificationError(f"cannot read {config.id} archive entry {source_path}")
                data = stream.read(maximum + 1)
                if len(data) != member.size:
                    raise VerificationError(
                        f"{config.id} archive entry size changed while reading {source_path}"
                    )
                if is_license:
                    if license_data is not None:
                        raise VerificationError(f"{config.id} archive repeats its license")
                    license_data = data
                if classification is not None:
                    if source_path in selected:
                        raise VerificationError(
                            f"{config.id} archive repeats selected path {source_path}"
                        )
                    selected[source_path] = SourceCase(source_path, classification, data)
    except (tarfile.TarError, OSError) as error:
        raise VerificationError(f"cannot read {config.id} source archive: {error}") from error
    if license_data is None:
        raise VerificationError(f"{config.id} archive does not contain its declared license")
    cases = sorted(selected.values(), key=lambda item: item.path.encode("utf-8"))
    _validate_source(config, cases, license_data)
    return cases, license_data


def _fetch_file_source(
    config: VerifierConfig, *, jobs: int, opener: UrlOpen
) -> tuple[list[SourceCase], bytes]:
    owner, repository = _github_coordinates(config.repository)
    tree_url = (
        f"https://api.github.com/repos/{quote(owner)}/{quote(repository)}/git/trees/"
        f"{quote(config.revision)}?recursive=1"
    )
    raw_tree = _fetch_bytes(tree_url, maximum=16 * 1024 * 1024, opener=opener)
    try:
        tree = json.loads(raw_tree)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise VerificationError(f"GitHub returned an invalid tree for {config.id}: {error}") from error
    if not isinstance(tree, dict) or tree.get("truncated") is not False:
        raise VerificationError(f"GitHub returned a truncated or invalid tree for {config.id}")
    entries = tree.get("tree")
    if not isinstance(entries, list):
        raise VerificationError(f"GitHub tree for {config.id} has no entry list")

    selected: list[tuple[str, str, int]] = []
    license_entry: tuple[str, int] | None = None
    for entry in entries:
        if not isinstance(entry, dict) or entry.get("type") != "blob":
            continue
        path = entry.get("path")
        size = entry.get("size")
        if not isinstance(path, str) or type(size) is not int or size < 0:
            raise VerificationError(f"GitHub tree for {config.id} has an invalid blob entry")
        _safe_relative_path(path, f"{config.id} tree path")
        if path == config.license_path:
            if license_entry is not None:
                raise VerificationError(f"GitHub tree for {config.id} repeats its license")
            license_entry = (path, size)
        classification = classify_source_path(config, path)
        if classification is not None:
            selected.append((path, classification, size))
    if license_entry is None:
        raise VerificationError(f"GitHub tree for {config.id} omits its declared license")
    if len(selected) != config.file_count:
        raise VerificationError(
            f"{config.id} upstream file count changed: expected {config.file_count}, "
            f"found {len(selected)}"
        )
    if sum(size for _, _, size in selected) != config.total_bytes:
        raise VerificationError(f"{config.id} upstream byte count changed")

    raw_root = (
        f"https://raw.githubusercontent.com/{quote(owner)}/{quote(repository)}/"
        f"{quote(config.revision)}"
    )

    def download(item: tuple[str, str, int]) -> SourceCase:
        path, classification, expected_size = item
        data = _fetch_bytes(
            f"{raw_root}/{quote(path, safe='/')}", maximum=expected_size, opener=opener
        )
        if len(data) != expected_size:
            raise VerificationError(f"downloaded size changed for {config.id}:{path}")
        return SourceCase(path, classification, data)

    selected.sort(key=lambda item: item[0].encode("utf-8"))
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        cases = list(executor.map(download, selected))
    license_path, license_size = license_entry
    license_data = _fetch_bytes(
        f"{raw_root}/{quote(license_path, safe='/')}",
        maximum=license_size,
        opener=opener,
    )
    _validate_source(config, cases, license_data)
    return cases, license_data


def fetch_source(
    config: VerifierConfig, *, jobs: int, opener: UrlOpen = urlopen
) -> tuple[list[SourceCase], bytes]:
    if config.fetch == "archive":
        return _fetch_archive_source(config, opener=opener)
    return _fetch_file_source(config, jobs=jobs, opener=opener)


def _normalized_name(config: VerifierConfig, source_path: str, classification: str) -> str:
    path = PurePosixPath(source_path)
    label = path.parent.name if path.name == "input" else path.stem
    label = re.sub(r"[^A-Za-z0-9._-]+", "_", label).strip("._-") or "case"
    label = label[:96]
    path_hash = hashlib.sha256(source_path.encode("utf-8")).hexdigest()[:12]
    return f"{PREFIX_BY_CLASS[classification]}{config.id}__{path_hash}__{label}.json"


def _index_bytes(config: VerifierConfig, files: Iterable[CorpusFile]) -> bytes:
    document = {
        "version": INDEX_VERSION,
        "suite": config.id,
        "revision": config.revision,
        "cases": [
            {
                "file": item.name,
                "source": item.source_path,
                "class": item.classification,
                "size": item.size,
                "sha256": item.sha256,
            }
            for item in files
        ],
    }
    return (json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n").encode()


def _parse_index(cache_dir: Path, config: VerifierConfig) -> tuple[CorpusFile, ...]:
    index_path = cache_dir / "index.json"
    try:
        raw = json.loads(index_path.read_bytes())
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise VerificationError(f"cannot read cached index {index_path}: {error}") from error
    if not isinstance(raw, dict) or set(raw) != INDEX_FIELDS:
        raise VerificationError(f"cached index for {config.id} has an invalid schema")
    if (
        raw.get("version") != INDEX_VERSION
        or raw.get("suite") != config.id
        or raw.get("revision") != config.revision
        or not isinstance(raw.get("cases"), list)
    ):
        raise VerificationError(f"cached index for {config.id} has invalid identity fields")

    files: list[CorpusFile] = []
    seen_names: set[str] = set()
    seen_sources: set[str] = set()
    for number, item in enumerate(raw["cases"], start=1):
        if not isinstance(item, dict) or set(item) != INDEX_CASE_FIELDS:
            raise VerificationError(f"cached index case {number} has an invalid schema")
        name = item.get("file")
        source_path = item.get("source")
        classification = item.get("class")
        size = item.get("size")
        sha256 = item.get("sha256")
        if (
            not isinstance(name, str)
            or Path(name).name != name
            or not isinstance(source_path, str)
            or classification not in CLASSIFICATIONS
            or type(size) is not int
            or size < 0
            or not isinstance(sha256, str)
            or SHA256_PATTERN.fullmatch(sha256) is None
        ):
            raise VerificationError(f"cached index case {number} contains invalid values")
        _safe_relative_path(source_path, f"cached index case {number} source")
        if name != _normalized_name(config, source_path, classification):
            raise VerificationError(f"cached index case {number} has a non-canonical filename")
        if name in seen_names or source_path in seen_sources:
            raise VerificationError(f"cached index case {number} is duplicated")
        seen_names.add(name)
        seen_sources.add(source_path)
        files.append(CorpusFile(name, classification, size, source_path, sha256))
    files.sort(key=lambda item: item.source_path.encode("utf-8"))
    return tuple(files)


def load_corpus(cache_dir: Path, config: VerifierConfig) -> CorpusInfo:
    license_path = cache_dir / config.license_path
    try:
        license_size = license_path.stat().st_size
    except OSError as error:
        raise VerificationError(f"cannot read cached license {license_path}: {error}") from error
    if license_size != config.license_size or _file_sha256(license_path) != config.license_sha256:
        raise VerificationError(f"cached {config.id} license does not match its manifest")

    files = _parse_index(cache_dir, config)
    input_dir = cache_dir / "inputs"
    try:
        entries = sorted(input_dir.iterdir(), key=lambda item: os.fsencode(item.name))
    except OSError as error:
        raise VerificationError(f"cannot read cached corpus {input_dir}: {error}") from error
    if any(not path.is_file() for path in entries):
        raise VerificationError(f"cached corpus {config.id} contains a non-file entry")
    expected_names = {item.name for item in files}
    actual_names = {path.name for path in entries}
    if actual_names != expected_names:
        raise VerificationError(f"cached corpus {config.id} file set does not match its index")

    source_cases: list[SourceCase] = []
    for item in files:
        path = input_dir / item.name
        if path.stat().st_size != item.size or _file_sha256(path) != item.sha256:
            raise VerificationError(f"cached input changed: {config.id}:{item.source_path}")
        source_cases.append(SourceCase(item.source_path, item.classification, path.read_bytes()))
    _validate_source(config, source_cases, license_path.read_bytes())
    return CorpusInfo(config=config, directory=input_dir, files=files)


def prepare_corpus(
    cache_dir: Path,
    config: VerifierConfig,
    *,
    refresh: bool = False,
    jobs: int = 8,
    opener: UrlOpen = urlopen,
) -> CorpusInfo:
    if cache_dir.exists() and not refresh:
        try:
            return load_corpus(cache_dir, config)
        except VerificationError as error:
            raise VerificationError(
                f"existing {config.id} cache is invalid ({error}); rerun prepare with --refresh"
            ) from error

    cases, license_data = fetch_source(config, jobs=jobs, opener=opener)
    cache_dir.parent.mkdir(parents=True, exist_ok=True)
    staging = Path(tempfile.mkdtemp(prefix=f".{config.id}-prepare-", dir=cache_dir.parent))
    try:
        input_dir = staging / "inputs"
        input_dir.mkdir()
        indexed: list[CorpusFile] = []
        for case in cases:
            name = _normalized_name(config, case.path, case.classification)
            destination = input_dir / name
            destination.write_bytes(case.data)
            indexed.append(
                CorpusFile(
                    name=name,
                    classification=case.classification,
                    size=len(case.data),
                    source_path=case.path,
                    sha256=hashlib.sha256(case.data).hexdigest(),
                )
            )
        indexed.sort(key=lambda item: item.source_path.encode("utf-8"))
        (staging / "index.json").write_bytes(_index_bytes(config, indexed))
        license_destination = staging / config.license_path
        license_destination.parent.mkdir(parents=True, exist_ok=True)
        license_destination.write_bytes(license_data)
        prepared = load_corpus(staging, config)
        if cache_dir.exists():
            shutil.rmtree(cache_dir)
        os.replace(staging, cache_dir)
        return CorpusInfo(
            config=config,
            directory=cache_dir / "inputs",
            files=prepared.files,
        )
    finally:
        shutil.rmtree(staging, ignore_errors=True)


def _expect_type(record: dict[str, object], field: str, expected: type, line: int) -> object:
    value = record[field]
    if type(value) is not expected:
        raise VerificationError(
            f"result line {line} field {field!r} must be {expected.__name__}"
        )
    return value


def parse_results(text: str, corpus: CorpusInfo) -> list[Result]:
    corpus_by_name = {item.name: item for item in corpus.files}
    results: list[Result] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        if not line:
            raise VerificationError(f"result line {line_number} is empty")
        try:
            raw = json.loads(line)
        except json.JSONDecodeError as error:
            raise VerificationError(f"result line {line_number} is invalid JSON: {error}") from error
        if not isinstance(raw, dict):
            raise VerificationError(f"result line {line_number} must be an object")
        fields = set(raw)
        if fields != RESULT_FIELDS:
            missing = sorted(RESULT_FIELDS - fields)
            unknown = sorted(fields - RESULT_FIELDS)
            detail = []
            if missing:
                detail.append(f"missing {', '.join(missing)}")
            if unknown:
                detail.append(f"unknown {', '.join(unknown)}")
            raise VerificationError(
                f"result line {line_number} schema mismatch: {'; '.join(detail)}"
            )

        version = _expect_type(raw, "version", int, line_number)
        file = _expect_type(raw, "file", str, line_number)
        classification = _expect_type(raw, "class", str, line_number)
        profile = _expect_type(raw, "profile", str, line_number)
        mode = _expect_type(raw, "mode", str, line_number)
        chunk_size = _expect_type(raw, "chunk_size", int, line_number)
        input_bytes = _expect_type(raw, "input_bytes", int, line_number)
        accepted = _expect_type(raw, "accepted", bool, line_number)
        canonical = _expect_type(raw, "canonical", bool, line_number)
        error_kind = _expect_type(raw, "error_kind", str, line_number)
        error_offset = _expect_type(raw, "error_offset", int, line_number)
        error_line = _expect_type(raw, "error_line", int, line_number)
        error_column = _expect_type(raw, "error_column", int, line_number)
        error_path = _expect_type(raw, "error_path", str, line_number)
        error_invariants = _expect_type(raw, "error_invariants", bool, line_number)

        if version != PROTOCOL_VERSION:
            raise VerificationError(
                f"result line {line_number} has protocol version {version}, "
                f"expected {PROTOCOL_VERSION}"
            )
        expected_file = corpus_by_name.get(file)
        if expected_file is None:
            raise VerificationError(f"result line {line_number} names unknown corpus file {file!r}")
        if classification != expected_file.classification:
            raise VerificationError(f"result line {line_number} misclassifies {file!r}")
        if profile not in PROFILES:
            raise VerificationError(f"result line {line_number} has unknown profile {profile!r}")
        if (mode, chunk_size) not in corpus.config.modes:
            raise VerificationError(
                f"result line {line_number} has unknown mode/chunk pair {mode!r}/{chunk_size}"
            )
        if input_bytes != expected_file.size:
            raise VerificationError(
                f"result line {line_number} reports {input_bytes} bytes for {file!r}; "
                f"expected {expected_file.size}"
            )
        if min(error_offset, error_line, error_column) < 0:
            raise VerificationError(f"result line {line_number} has a negative error position")
        if not error_invariants:
            raise VerificationError(f"result line {line_number} failed error invariants")
        if accepted:
            if not canonical:
                raise VerificationError(f"accepted result line {line_number} is not canonical")
            if error_kind or error_offset or error_line or error_column or error_path:
                raise VerificationError(f"accepted result line {line_number} contains error data")
        else:
            if canonical:
                raise VerificationError(f"rejected result line {line_number} is canonical")
            if error_kind not in ERROR_KINDS:
                raise VerificationError(
                    f"result line {line_number} has unknown error kind {error_kind!r}"
                )
            if error_offset > input_bytes or error_line < 1 or error_column < 1:
                raise VerificationError(f"result line {line_number} has an invalid error position")
            if not error_path.startswith("$"):
                raise VerificationError(f"result line {line_number} has an invalid JSON path")

        results.append(
            Result(
                file=file,
                classification=classification,
                profile=profile,
                mode=mode,
                chunk_size=chunk_size,
                input_bytes=input_bytes,
                accepted=accepted,
                canonical=canonical,
                error_kind=error_kind,
                error_offset=error_offset,
                error_line=error_line,
                error_column=error_column,
                error_path=error_path,
                error_invariants=error_invariants,
            )
        )
    return results


def _allowed_decoder_diagnostic_difference(oneshot: Result, stream: Result) -> bool:
    if oneshot.accepted or stream.accepted or oneshot.error_kind != "trailingData":
        return False
    # Parser parses one complete document, so it stops at the first byte after
    # the root. Decoder is intentionally a sequence API: its second `next()`
    # parses that suffix and may diagnose an error later inside the next value.
    # The complete-document diagnostic remains authoritative, while requiring
    # the sequence diagnostic not to move before the actual trailing data.
    return stream.error_offset >= oneshot.error_offset


def validate_matrix(results: list[Result], corpus: CorpusInfo) -> Summary:
    by_key: dict[tuple[str, str, str, int], Result] = {}
    for result in results:
        if result.key() in by_key:
            raise VerificationError(f"duplicate result for {result.key()}")
        by_key[result.key()] = result

    expected = {
        (item.name, profile, mode, chunk)
        for item in corpus.files
        for profile in PROFILES
        for mode, chunk in corpus.config.modes
    }
    actual = set(by_key)
    if actual != expected:
        missing = sorted(expected - actual)
        unknown = sorted(actual - expected)
        detail = []
        if missing:
            detail.append(f"missing {len(missing)} (first: {missing[0]})")
        if unknown:
            detail.append(f"unexpected {len(unknown)} (first: {unknown[0]})")
        raise VerificationError(f"incomplete result matrix: {'; '.join(detail)}")

    diagnostic_differences: list[DiagnosticDifference] = []
    stream_modes = [item for item in corpus.config.modes if item[0] == "stream"]
    for item in corpus.files:
        for profile in PROFILES:
            oneshot = by_key[(item.name, profile, "oneshot", 0)]
            streams = [by_key[(item.name, profile, mode, size)] for mode, size in stream_modes]
            if any(stream.diagnostic() != streams[0].diagnostic() for stream in streams[1:]):
                raise VerificationError(
                    f"streaming result for {item.source_path}/{profile} depends on chunk size"
                )
            if any(stream.accepted != oneshot.accepted for stream in streams):
                raise VerificationError(
                    f"one-shot and streaming acceptance disagree for {item.source_path}/{profile}"
                )
            if streams[0].diagnostic() != oneshot.diagnostic():
                if not _allowed_decoder_diagnostic_difference(oneshot, streams[0]):
                    raise VerificationError(
                        f"one-shot and streaming diagnostics disagree for "
                        f"{item.source_path}/{profile}"
                    )
                diagnostic_differences.append(
                    DiagnosticDifference(item.name, profile, oneshot, streams[0])
                )

    representatives = {
        (item.name, profile): by_key[(item.name, profile, "oneshot", 0)]
        for item in corpus.files
        for profile in PROFILES
    }
    safe_deviations: list[Result] = []
    implementation_decisions: list[tuple[str, Result, Result]] = []
    for item in corpus.files:
        rfc = representatives[(item.name, "rfc")]
        safe = representatives[(item.name, "safe")]
        if item.classification == "yes":
            if not rfc.accepted:
                raise VerificationError(
                    f"RFC profile rejected required input {corpus.config.id}:{item.source_path} "
                    f"with {rfc.error_kind}"
                )
            if not safe.accepted:
                if safe.error_kind not in SAFE_POLICY_ERRORS:
                    raise VerificationError(
                        f"safe profile rejected required input {corpus.config.id}:"
                        f"{item.source_path} with unexpected policy {safe.error_kind}"
                    )
                safe_deviations.append(safe)
        elif item.classification == "no":
            if rfc.accepted:
                raise VerificationError(
                    f"RFC profile accepted forbidden input {corpus.config.id}:{item.source_path}"
                )
            if safe.accepted:
                raise VerificationError(
                    f"safe profile accepted forbidden input {corpus.config.id}:{item.source_path}"
                )
        else:
            implementation_decisions.append((item.name, rfc, safe))

    counts = Counter(
        (result.profile, result.classification, result.accepted)
        for result in representatives.values()
    )
    return Summary(
        row_count=len(results),
        counts=dict(counts),
        safe_policy_deviations=tuple(safe_deviations),
        implementation_decisions=tuple(implementation_decisions),
        diagnostic_differences=tuple(diagnostic_differences),
    )


def run_verifier(command: list[str], *, timeout: float, cwd: Path) -> str:
    try:
        completed = subprocess.run(
            command,
            cwd=cwd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise VerifierProcessError("timeout", f"exceeded {timeout:g}s") from error
    except OSError as error:
        raise VerifierProcessError("launch failure", str(error)) from error

    stderr = completed.stderr.decode("utf-8", errors="replace").strip()
    if completed.returncode < 0:
        number = -completed.returncode
        try:
            name = signal.Signals(number).name
        except ValueError:
            name = str(number)
        raise VerifierProcessError("crash", f"terminated by signal {name}; {stderr}")
    if completed.returncode != 0:
        kind = "panic" if "panic" in stderr.lower() else "failure"
        raise VerifierProcessError(
            kind,
            f"exit {completed.returncode}" + (f"; {stderr}" if stderr else ""),
        )
    if stderr:
        raise VerifierProcessError("protocol failure", f"unexpected stderr: {stderr}")
    try:
        return completed.stdout.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise VerifierProcessError("protocol failure", f"stdout is not UTF-8: {error}") from error


def build_verifier(args: argparse.Namespace) -> None:
    taro = args.taro.resolve()
    if not taro.is_file():
        subprocess.run([sys.executable, str(BUILD_DIST)], cwd=REPO_ROOT, check=True)
    args.binary.resolve().parent.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    environment["TARO_HOME"] = str(taro.parent.parent)
    subprocess.run(
        [
            str(taro),
            "build",
            str(args.package.resolve()),
            "--std-path",
            str(args.std_path.resolve()),
            "--release",
            "--locked",
            "--no-incremental",
            # A verifier must certify workspace std sources, not an older
            # attached standard-library artifact from a previous build.
            "--build-std",
            "-o",
            str(args.binary.resolve()),
        ],
        cwd=REPO_ROOT,
        env=environment,
        check=True,
    )


def _status(result: Result) -> str:
    return "accept" if result.accepted else f"reject ({result.error_kind})"


def _print_names(corpus: CorpusInfo, names: list[str], *, verbose: bool) -> None:
    limit = len(names) if verbose else min(len(names), 12)
    for name in names[:limit]:
        print(f"    {corpus.display_name(name)}")
    if limit < len(names):
        print(f"    ... and {len(names) - limit} more (use --verbose)")


def print_summary(corpus: CorpusInfo, summary: Summary, *, verbose: bool) -> None:
    config = corpus.config
    print(
        f"PASS: {config.name}@{config.revision[:12]} — {len(corpus.files)} inputs, "
        f"{summary.row_count} parser runs"
    )
    for profile in PROFILES:
        for classification in CLASSIFICATIONS:
            accepted = summary.counts.get((profile, classification, True), 0)
            rejected = summary.counts.get((profile, classification, False), 0)
            print(
                f"  {profile:4} {classification:14} "
                f"accepted={accepted:4} rejected={rejected:4}"
            )
    if summary.safe_policy_deviations:
        print(f"  safe-policy deviations: {len(summary.safe_policy_deviations)}")
        _print_names(
            corpus,
            [result.file for result in summary.safe_policy_deviations],
            verbose=verbose,
        )
    if summary.implementation_decisions:
        print(f"  implementation-defined decisions: {len(summary.implementation_decisions)}")
        limit = len(summary.implementation_decisions) if verbose else min(
            len(summary.implementation_decisions), 12
        )
        for name, rfc, safe in summary.implementation_decisions[:limit]:
            print(
                f"    {corpus.display_name(name)}: "
                f"rfc={_status(rfc)}, safe={_status(safe)}"
            )
        if limit < len(summary.implementation_decisions):
            print(
                f"    ... and {len(summary.implementation_decisions) - limit} more "
                "(use --verbose)"
            )
    if summary.diagnostic_differences:
        print(
            "  expected document/sequence diagnostic differences: "
            f"{len(summary.diagnostic_differences)}"
        )


def positive_int(value: str) -> int:
    try:
        parsed = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("value must be an integer") from error
    if parsed < 1:
        raise argparse.ArgumentTypeError("value must be at least 1")
    return parsed


def positive_timeout(value: str) -> float:
    try:
        parsed = float(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("timeout must be a number of seconds") from error
    if parsed <= 0:
        raise argparse.ArgumentTypeError("timeout must be greater than zero")
    return parsed


def _select_configs(
    configs: tuple[VerifierConfig, ...], requested: list[str] | None
) -> tuple[VerifierConfig, ...]:
    if not requested:
        return configs
    by_id = {config.id: config for config in configs}
    unknown = [item for item in requested if item not in by_id]
    if unknown:
        raise VerificationError(f"unknown verifier suite: {', '.join(unknown)}")
    if len(requested) != len(set(requested)):
        raise VerificationError("a verifier suite was selected more than once")
    return tuple(by_id[item] for item in requested)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument(
        "--cache-base",
        type=Path,
        default=DEFAULT_CACHE_BASE,
        help="parent directory for suite/revision-keyed ignored inputs",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    prepare = subparsers.add_parser("prepare", help="download and validate pinned inputs")
    prepare.add_argument("--refresh", action="store_true")
    prepare.add_argument("--jobs", type=positive_int, default=8)
    prepare.add_argument("--suite", action="append", help="prepare only this suite id")

    run = subparsers.add_parser("run", help="run against already prepared inputs")
    run.add_argument("--package", type=Path, default=DEFAULT_PACKAGE)
    run.add_argument("--binary", type=Path, default=DEFAULT_BINARY)
    run.add_argument("--taro", type=Path, default=DEFAULT_TARO)
    run.add_argument("--std-path", type=Path, default=DEFAULT_STD)
    run.add_argument("--timeout", type=positive_timeout, default=180.0)
    run.add_argument("--no-build", action="store_true", help="reuse --binary as-is")
    run.add_argument("--suite", action="append", help="run only this suite id")
    run.add_argument("--verbose", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    try:
        configs = _select_configs(
            load_registry(args.manifest.resolve()),
            args.suite,
        )
        cache_base = args.cache_base.resolve()
        if args.command == "prepare":
            for config in configs:
                cache_dir = cache_base / config.id / config.revision
                existed = cache_dir.exists()
                corpus = prepare_corpus(
                    cache_dir,
                    config,
                    refresh=args.refresh,
                    jobs=args.jobs,
                )
                action = "validated cached" if existed and not args.refresh else "prepared"
                print(
                    f"PASS: {action} {config.name}@{config.revision[:12]} — "
                    f"{len(corpus.files)} files in {cache_dir}"
                )
            return 0

        corpora: list[CorpusInfo] = []
        for config in configs:
            cache_dir = cache_base / config.id / config.revision
            if not cache_dir.exists():
                raise VerificationError(
                    f"{config.id} inputs are not prepared; run "
                    f"`python3 development/verifiers/json/verify.py prepare --suite {config.id}`"
                )
            corpora.append(load_corpus(cache_dir, config))
        if not args.no_build:
            build_verifier(args)

        total_runs = 0
        total_inputs = 0
        for corpus in corpora:
            output = run_verifier(
                [
                    str(args.binary.resolve()),
                    str(corpus.directory),
                    corpus.config.matrix,
                ],
                timeout=args.timeout,
                cwd=REPO_ROOT,
            )
            summary = validate_matrix(parse_results(output, corpus), corpus)
            print_summary(corpus, summary, verbose=args.verbose)
            total_runs += summary.row_count
            total_inputs += len(corpus.files)
        print(
            f"PASS: JSON certification complete — {len(corpora)} suites, "
            f"{total_inputs} inputs, {total_runs} parser runs"
        )
        return 0
    except (VerificationError, subprocess.CalledProcessError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
