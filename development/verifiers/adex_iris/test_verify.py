import importlib.util
import io
import json
from pathlib import Path
import unittest
import zipfile


MODULE_PATH = Path(__file__).with_name("verify.py")
SPEC = importlib.util.spec_from_file_location("adex_iris_verify", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
verify = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(verify)


def fixture_rows() -> bytes:
    rows = []
    for label in ("Iris-setosa", "Iris-versicolor", "Iris-virginica"):
        rows.extend([f"5.0,3.0,2.0,1.0,{label}\n"] * 50)
    return "".join(rows).encode("ascii")


def manifest_for(member: bytes) -> dict[str, object]:
    return {
        "member_sha256": verify.hashlib.sha256(member).hexdigest(),
        "member_bytes": len(member),
        "rows": 150,
        "classes": ["Iris-setosa", "Iris-versicolor", "Iris-virginica"],
        "rows_per_class": 50,
    }


class VerifyTests(unittest.TestCase):
    def test_extract_validates_pinned_member(self):
        member = fixture_rows()
        archive_io = io.BytesIO()
        with zipfile.ZipFile(archive_io, "w") as archive:
            archive.writestr("iris.data", member)
        archive = archive_io.getvalue()
        manifest = manifest_for(member) | {
            "archive_sha256": verify.hashlib.sha256(archive).hexdigest(),
            "member": "iris.data",
        }
        self.assertEqual(verify.extract_dataset(archive, manifest), member)

    def test_checksum_mismatch_fails(self):
        with self.assertRaises(verify.VerificationError):
            verify.require_digest(b"wrong", "0" * 64, "fixture")

    def test_dataset_rejects_malformed_nonfinite_and_unknown_rows(self):
        original = fixture_rows()
        for replacement in (
            b"5.0,3.0,2.0,Iris-setosa",
            b"nan,3.0,2.0,1.0,Iris-setosa",
            b"5.0,3.0,2.0,1.0,Iris-unknown",
        ):
            first, remainder = original.split(b"\n", 1)
            changed = replacement + b"\n" + remainder
            with self.subTest(replacement=replacement):
                with self.assertRaises(verify.VerificationError):
                    verify.validate_dataset(changed, manifest_for(changed))

    def test_dataset_rejects_wrong_class_counts(self):
        changed = fixture_rows().replace(b"Iris-versicolor", b"Iris-setosa", 1)
        with self.assertRaises(verify.VerificationError):
            verify.validate_dataset(changed, manifest_for(changed))

    def test_metrics_require_accuracy_and_confusion(self):
        payload = {
            "schema": 1,
            "folds": [
                {
                    "fold": fold,
                    "training_samples": 120,
                    "testing_samples": 30,
                    "correct": 27,
                    "loss": 0.5,
                    "finite": True,
                }
                for fold in range(5)
            ],
            "correct": 135,
            "samples": 150,
            "accuracy": 0.9,
            "finite": True,
            "confusion": [[45, 5, 0], [2, 43, 5], [0, 3, 47]],
        }
        self.assertEqual(verify.validate_metrics(json.loads(json.dumps(payload))), payload)
        payload["correct"] = 134
        with self.assertRaises(verify.VerificationError):
            verify.validate_metrics(payload)


if __name__ == "__main__":
    unittest.main()
