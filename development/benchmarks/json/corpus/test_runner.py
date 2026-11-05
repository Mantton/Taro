import importlib.util, unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent


def module(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


oracle = module("oracle")
runner = module("run")
report = module("report")


class CorpusChecks(unittest.TestCase):
    def test_unicode_boolean_and_numeric_shape(self):
        value = {"☃": [True, False, None, 3, "é"]}
        actual = oracle.shape(value)
        self.assertEqual(
            {
                k: actual[k]
                for k in [
                    "objects",
                    "arrays",
                    "strings",
                    "numbers",
                    "booleans",
                    "nulls",
                    "utf8_bytes",
                    "depth",
                    "top",
                ]
            },
            dict(
                objects=1,
                arrays=1,
                strings=1,
                numbers=1,
                booleans=2,
                nulls=1,
                utf8_bytes=5,
                depth=2,
                top=1,
            ),
        )
        self.assertEqual(oracle.shape("é")["top"], 2)

    def test_protocol_preserves_digit_field_names(self):
        self.assertEqual(
            runner.fields("utf8_bytes=00012 ops=1"), dict(utf8_bytes=12, ops=1)
        )

    def test_reject_duplicate_input_members(self):
        with self.assertRaises(ValueError):
            oracle.unique_object([("x", 1), ("x", 2)])

    def test_protocol_rejects_missing_and_wrong_results(self):
        original = runner.expected
        runner.expected = lambda _: dict(top=2)
        try:
            for mode in ["dom"]:
                case = dict(language="taro", mode=mode, dataset="small")
                actual = runner.parse_run(
                    case, "sample ns=100 ops=2 checksum=4\nstats ops=2", 2, 1
                )
                self.assertEqual(actual["samples_ns_per_op"], [50])
            for text in [
                "stats ops=2",
                "sample ns=100 ops=2 checksum=2\nstats ops=2",
                "sample ns=100 ops=2 checksum=4\nstats ops=1",
            ]:
                with self.assertRaises(RuntimeError):
                    runner.parse_run(case, text, 2, 1)
            actual = runner.parse_run(
                case, "sample ns=100 ops=2 checksum=4\nstats ops=2", 2, 1
            )
            self.assertEqual(actual["samples_ns_per_op"], [50])
        finally:
            runner.expected = original

    def test_summary_uses_round_medians_and_rejects_incomplete_runs(self):
        rows = []
        for round_index, samples in enumerate(
            [[1, 2, 100], [10, 20, 1000], [100, 200, 10000]]
        ):
            rows.append(
                dict(
                    ok=True,
                    round=round_index,
                    data=dict(samples_ns_per_op=samples),
                    peak_rss_bytes=1024,
                    process_usage={},
                    before={},
                    after={},
                )
            )
        summary = report.timing_summary(rows, 100)
        self.assertEqual(summary["median_ms"], 20 / 1e6)
        self.assertEqual(summary["round_range_ms"], [2 / 1e6, 200 / 1e6])
        self.assertEqual(summary["samples"], 9)
        with self.assertRaises(ValueError):
            report.timing_summary(rows[:2], 100)

    def test_allocation_slope_excludes_setup_and_distinguishes_bytes(self):
        rows = [
            dict(
                ok=True,
                count=n,
                stats=dict(allocated_bytes=100 * n, collections=n),
                process_stats=dict(allocations=40 + 7 * n),
            )
            for n in [1, 2]
        ]
        summary = report.audit_summary("taro", rows)
        self.assertEqual(summary["allocations_per_op_estimate"], 7)
        self.assertEqual(summary["allocated_bytes_per_op"], 100)
        self.assertEqual(summary["collections_in_two_ops"], 2)
        self.assertEqual(summary["bytes_per_op_variation"], 0)

    def test_report_labels_public_dom_without_calling_it_typed(self):
        cases = {}
        for language, mode in [
            ("taro", "dom"),
            ("swift", "dom"),
            ("rust", "dom"),
            ("go", "dom"),
        ]:
            case = dict(language=language, mode=mode, dataset="small")
            cases[runner.key(case)] = dict(
                case=case,
                timing=dict(
                    median_ms=1,
                    round_range_ms=[1, 2],
                    decimal_MB_per_second=1,
                    peak_process_rss_bytes=1024,
                ),
            )
        text = report.render(
            dict(cases=cases, fixtures=dict(files=[dict(name="small", bytes=1000)]))
        )
        self.assertIn("Taro public ms", text)
        self.assertIn("taro/dom/small", text)
        self.assertNotIn("Complete typed Canada model", text)


if __name__ == "__main__":
    unittest.main()
