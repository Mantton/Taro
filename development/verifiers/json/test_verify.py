#!/usr/bin/env python3
"""Offline regression tests for the multi-corpus JSON verifier runner."""

from __future__ import annotations

from dataclasses import replace
import hashlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest

from verify import (
    DOCUMENT_MODES,
    FULL_MODES,
    PROFILES,
    ClassificationRule,
    CorpusFile,
    CorpusInfo,
    Result,
    Selection,
    SourceCase,
    VerificationError,
    VerifierConfig,
    classify_source_path,
    load_corpus,
    load_registry,
    prepare_corpus,
    source_tree_digest,
    validate_matrix,
)


class FakeResponse(io.BytesIO):
    def __enter__(self) -> FakeResponse:
        return self

    def __exit__(self, *_: object) -> None:
        self.close()


def fixture_config(
    cases: dict[str, tuple[str, bytes]],
    license_data: bytes,
    *,
    fetch: str,
    matrix: str = "full",
) -> VerifierConfig:
    source_cases = [
        SourceCase(path, classification, data)
        for path, (classification, data) in sorted(cases.items())
    ]
    return VerifierConfig(
        id="fixture",
        name="Fixture",
        matrix=matrix,
        repository="https://github.com/example/fixture",
        revision="a" * 40,
        revision_date="2026-07-21T00:00:00Z",
        license="MIT",
        license_path="LICENSE",
        license_size=len(license_data),
        license_sha256=hashlib.sha256(license_data).hexdigest(),
        fetch=fetch,
        archive_max_bytes=1024 * 1024 if fetch == "archive" else None,
        file_count=len(cases),
        total_bytes=sum(len(data) for _, data in cases.values()),
        tree_hash=(
            "sha256-v2(source-relative-path NUL classification NUL decimal-size NUL "
            "contents, byte-sorted)"
        ),
        tree_sha256=source_tree_digest(source_cases),
        selections=(
            Selection(
                root="cases",
                include=("*.json",),
                default_classification=None,
                rules=(
                    ClassificationRule("yes", ("y_*.json",)),
                    ClassificationRule("no", ("n_*.json",)),
                    ClassificationRule("implementation", ("i_*.json",)),
                ),
            ),
        ),
    )


def archive_bytes(files: dict[str, bytes]) -> bytes:
    destination = io.BytesIO()
    with tarfile.open(fileobj=destination, mode="w:gz") as archive:
        for path, data in sorted(files.items()):
            info = tarfile.TarInfo(f"fixture-revision/{path}")
            info.size = len(data)
            archive.addfile(info, io.BytesIO(data))
    return destination.getvalue()


def outcome(
    file: CorpusFile,
    profile: str,
    mode: str,
    chunk: int,
    *,
    accepted: bool,
    error_kind: str = "invalidNumber",
) -> Result:
    return Result(
        file=file.name,
        classification=file.classification,
        profile=profile,
        mode=mode,
        chunk_size=chunk,
        input_bytes=file.size,
        accepted=accepted,
        canonical=accepted,
        error_kind="" if accepted else error_kind,
        error_offset=0,
        error_line=0 if accepted else 1,
        error_column=0 if accepted else 1,
        error_path="" if accepted else "$",
        error_invariants=True,
    )


class JsonVerifierTests(unittest.TestCase):
    def test_committed_registry_is_well_formed_and_pins_expected_scope(self) -> None:
        registry = Path(__file__).with_name("verifier.toml")
        configs = load_registry(registry)

        self.assertEqual(len(configs), 10)
        self.assertEqual(sum(config.file_count for config in configs), 1313)
        self.assertEqual(
            sum(
                config.file_count * len(PROFILES) * len(config.modes)
                for config in configs
            ),
            12600,
        )
        self.assertEqual(configs[0].id, "json-test-suite")
        self.assertEqual(configs[-1].id, "cjson-fuzz")

    def test_manifest_classification_preserves_rfc_policy_distinctions(self) -> None:
        configs = {
            config.id: config
            for config in load_registry(Path(__file__).with_name("verifier.toml"))
        }
        self.assertEqual(
            classify_source_path(
                configs["jansson"],
                "test/suites/invalid/too-big-positive-integer/input",
            ),
            "implementation",
        )
        self.assertEqual(
            classify_source_path(
                configs["jansson"], "test/suites/invalid/null-escape-in-string/input"
            ),
            "yes",
        )
        self.assertEqual(
            classify_source_path(
                configs["yyjson"],
                "test/data/json/test_yyjson/invalid_utf8_escape_1(fail).min.json",
            ),
            "implementation",
        )
        self.assertEqual(
            classify_source_path(
                configs["jsoncpp"], "test/data/legacy_test_basic_01.json"
            ),
            "no",
        )
        self.assertEqual(
            classify_source_path(
                configs["jsoncpp"], "test/data/legacy_test_integer_05.json"
            ),
            "yes",
        )
        self.assertEqual(
            classify_source_path(
                configs["json-schema"],
                "tests/draft2020-12/optional/format/idn-email.json",
            ),
            "implementation",
        )

    def test_registry_rejects_unversioned_extension_fields(self) -> None:
        registry = Path(__file__).with_name("verifier.toml")
        with tempfile.TemporaryDirectory() as temp:
            modified = Path(temp) / "verifier.toml"
            modified.write_text(
                registry.read_text(encoding="utf-8") + "\nextra = true\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(VerificationError, "unsupported fields"):
                load_registry(modified)

    def test_archive_prepare_is_verified_atomic_and_offline_after_fetch(self) -> None:
        license_data = b"fixture license\n"
        payloads = {
            "cases/n_invalid.json": ("no", b"{"),
            "cases/y_valid.json": ("yes", b"{}"),
        }
        config = fixture_config(payloads, license_data, fetch="archive")
        source_archive = archive_bytes(
            {
                "LICENSE": license_data,
                **{path: data for path, (_, data) in payloads.items()},
            }
        )

        def opener(request: object, *, timeout: int) -> FakeResponse:
            self.assertEqual(timeout, 60)
            self.assertIn("codeload.github.com", request.full_url)  # type: ignore[attr-defined]
            return FakeResponse(source_archive)

        with tempfile.TemporaryDirectory() as temp:
            cache = Path(temp) / "cache" / config.revision
            prepared = prepare_corpus(cache, config, opener=opener)
            self.assertEqual(len(prepared.files), 2)
            self.assertEqual(load_corpus(cache, config), prepared)

            def reject_network(*_: object, **__: object) -> object:
                raise AssertionError("valid prepared inputs must not access the network")

            self.assertEqual(
                prepare_corpus(cache, config, opener=reject_network),
                prepared,
            )

            (prepared.directory / prepared.files[0].name).write_bytes(b"[]")
            with self.assertRaisesRegex(VerificationError, "--refresh"):
                prepare_corpus(cache, config, opener=reject_network)

    def test_file_prepare_validates_tree_and_exact_raw_sizes(self) -> None:
        license_data = b"fixture license\n"
        payloads = {
            "cases/i_choice.json": ("implementation", b"0"),
            "cases/y_valid.json": ("yes", b"[]"),
        }
        config = fixture_config(payloads, license_data, fetch="files")
        tree = {
            "truncated": False,
            "tree": [
                {"path": "LICENSE", "type": "blob", "size": len(license_data)},
                *[
                    {"path": path, "type": "blob", "size": len(data)}
                    for path, (_, data) in payloads.items()
                ],
            ],
        }

        def opener(request: object, *, timeout: int) -> FakeResponse:
            self.assertEqual(timeout, 60)
            url = request.full_url  # type: ignore[attr-defined]
            if "api.github.com" in url:
                return FakeResponse(json.dumps(tree).encode())
            if url.endswith("/LICENSE"):
                return FakeResponse(license_data)
            for path, (_, data) in payloads.items():
                if url.endswith("/" + path):
                    return FakeResponse(data)
            raise AssertionError(f"unexpected URL: {url}")

        with tempfile.TemporaryDirectory() as temp:
            corpus = prepare_corpus(Path(temp) / "cache", config, jobs=2, opener=opener)
            self.assertEqual(
                [item.source_path for item in corpus.files],
                sorted(payloads),
            )

    def test_matrix_enforces_contracts_and_allows_declared_safe_limits(self) -> None:
        license_data = b"x"
        cases = {
            "cases/i_choice.json": ("implementation", b"0"),
            "cases/n_forbidden.json": ("no", b"{"),
            "cases/y_required.json": ("yes", b"[]"),
        }
        config = fixture_config(cases, license_data, fetch="archive", matrix="documents")
        files = tuple(
            CorpusFile(
                name=f"{classification[0]}_{Path(path).stem}.json",
                classification=classification,
                size=len(data),
                source_path=path,
                sha256=hashlib.sha256(data).hexdigest(),
            )
            for path, (classification, data) in sorted(cases.items())
        )
        corpus = CorpusInfo(config=config, directory=Path("fixture"), files=files)
        results: list[Result] = []
        for file in files:
            for profile in PROFILES:
                for mode, chunk in DOCUMENT_MODES:
                    accepted = file.classification == "yes" or (
                        file.classification == "implementation" and profile == "rfc"
                    )
                    error_kind = "inputLimit" if (
                        file.classification == "yes" and profile == "safe"
                    ) else "invalidNumber"
                    if file.classification == "yes" and profile == "safe":
                        accepted = False
                    results.append(
                        outcome(
                            file,
                            profile,
                            mode,
                            chunk,
                            accepted=accepted,
                            error_kind=error_kind,
                        )
                    )

        summary = validate_matrix(results, corpus)
        self.assertEqual(summary.row_count, 18)
        self.assertEqual(len(summary.safe_policy_deviations), 1)
        self.assertEqual(len(summary.implementation_decisions), 1)

        changed = list(results)
        index = next(
            index
            for index, result in enumerate(changed)
            if result.classification == "yes"
            and result.profile == "rfc"
            and result.mode == "stream"
            and result.chunk_size == 7
        )
        changed[index] = replace(
            changed[index],
            accepted=False,
            canonical=False,
            error_kind="invalidNumber",
            error_line=1,
            error_column=1,
            error_path="$",
        )
        with self.assertRaisesRegex(VerificationError, "depends on chunk size"):
            validate_matrix(changed, corpus)

    def test_mode_sets_keep_full_boundary_stress_out_of_large_documents(self) -> None:
        self.assertEqual(len(FULL_MODES), 6)
        self.assertEqual(DOCUMENT_MODES, (("oneshot", 0), ("stream", 7), ("stream", 4096)))

    def test_sequence_diagnostic_may_advance_within_trailing_document_data(self) -> None:
        data = b"null\nfoo"
        source = "cases/n_trailing.json"
        config = fixture_config(
            {source: ("no", data)},
            b"license",
            fetch="archive",
            matrix="documents",
        )
        file = CorpusFile(
            name="n_trailing.json",
            classification="no",
            size=len(data),
            source_path=source,
            sha256=hashlib.sha256(data).hexdigest(),
        )
        corpus = CorpusInfo(config=config, directory=Path("fixture"), files=(file,))
        results: list[Result] = []
        for profile in PROFILES:
            for mode, chunk in DOCUMENT_MODES:
                result = outcome(file, profile, mode, chunk, accepted=False)
                if mode == "oneshot":
                    result = replace(
                        result,
                        error_kind="trailingData",
                        error_offset=5,
                        error_line=2,
                        error_column=1,
                    )
                else:
                    result = replace(
                        result,
                        error_kind="unexpectedToken",
                        error_offset=6,
                        error_line=2,
                        error_column=2,
                    )
                results.append(result)

        summary = validate_matrix(results, corpus)
        self.assertEqual(len(summary.diagnostic_differences), 2)

        moved_before_suffix = list(results)
        moved_before_suffix[1] = replace(moved_before_suffix[1], error_offset=4)
        moved_before_suffix[2] = replace(moved_before_suffix[2], error_offset=4)
        with self.assertRaisesRegex(VerificationError, "diagnostics disagree"):
            validate_matrix(moved_before_suffix, corpus)


if __name__ == "__main__":
    unittest.main()
