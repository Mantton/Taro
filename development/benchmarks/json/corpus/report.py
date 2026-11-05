#!/usr/bin/env python3
"""Summarize validated, identity-matched measurements without tracking results."""
import json
import argparse
import statistics
from datetime import datetime, timezone
from collections import defaultdict
from pathlib import Path
import run


def timing_summary(rows, size):
    successful = [row for row in rows if row["ok"]]
    medians = [
        statistics.median(row["data"]["samples_ns_per_op"]) for row in successful
    ]
    if len(successful) != 3 or {row["round"] for row in successful} != {0, 1, 2}:
        raise ValueError("need three successful, distinct timing rounds")
    ns = statistics.median(medians)
    return {
        "median_ms": ns / 1e6,
        "round_range_ms": [min(medians) / 1e6, max(medians) / 1e6],
        "sample_range_ms": [
            min(v for row in successful for v in row["data"]["samples_ns_per_op"])
            / 1e6,
            max(v for row in successful for v in row["data"]["samples_ns_per_op"])
            / 1e6,
        ],
        "decimal_MB_per_second": size * 1000 / ns,
        "peak_process_rss_bytes": max(row["peak_rss_bytes"] for row in successful),
        "samples": sum(len(row["data"]["samples_ns_per_op"]) for row in successful),
        "process_usage": [row["process_usage"] for row in successful],
        "load_before_after": [[row["before"], row["after"]] for row in successful],
    }


def audit_summary(language, rows):
    by_count = {row["count"]: row for row in rows if row["ok"]}
    if set(by_count) != {1, 2}:
        raise ValueError("need successful one- and two-operation audits")
    one, two = by_count[1], by_count[2]
    result = {
        "allocated_bytes_per_op": two["stats"]["allocated_bytes"] / 2,
        "one_op_allocated_bytes": one["stats"]["allocated_bytes"],
        "two_op_allocated_bytes": two["stats"]["allocated_bytes"],
        "bytes_per_op_variation": abs(
            one["stats"]["allocated_bytes"] - two["stats"]["allocated_bytes"] / 2
        ),
        "collections_in_two_ops": two["stats"]["collections"],
        "collections_per_op": two["stats"]["collections"] / 2,
    }
    if language == "taro":
        result["allocations_per_op_estimate"] = (
            two["process_stats"]["allocations"] - one["process_stats"]["allocations"]
        )
    else:
        result["allocations_per_op"] = two["stats"]["allocations"] / 2
    if "pause_ns" in two["stats"]:
        result["pause_ms_in_two_ops"] = two["stats"]["pause_ns"] / 1e6
    return result


def render(report):
    lines = [
        "# Large JSON results",
        "",
        "Local macOS; median of three round medians, five samples per round. "
        "Times are milliseconds per full fresh parse; MB means decimal megabytes.",
        "",
    ]
    cases = report["cases"]
    paths = [("Taro public", "taro/dom")]
    paths += [
        (language.title(), f"{language}/dom") for language in ["swift", "rust", "go"]
    ]
    lines += [
        "| DOM document | MB | "
        + " | ".join(label + " ms" for label, _ in paths)
        + " |",
        "|---|---:|" + "---:|" * len(paths),
    ]
    for fixture in report["fixtures"]["files"]:
        name = fixture["name"]
        cells = [
            f"{cases[f'{path}/{name}']['timing']['median_ms']:.3f}" for _, path in paths
        ]
        lines.append(
            f"| {name} | {fixture['bytes'] / 1e6:.2f} | " + " | ".join(cells) + " |"
        )
    if any(not run.is_dom(c["case"]) for c in cases.values()):
        lines += [
            "",
            "## Complete typed Canada model",
            "",
            "| Path | ms | Round median range, ms | MB/s | Peak process MiB |",
            "|---|---:|---:|---:|---:|",
        ]
    for name, case in cases.items():
        if run.is_dom(case["case"]):
            continue
        timing = case["timing"]
        low, high = timing["round_range_ms"]
        lines.append(
            f"| {name} | {timing['median_ms']:.3f} | {low:.3f}–{high:.3f} | {timing['decimal_MB_per_second']:.1f} | {timing['peak_process_rss_bytes'] / 1024**2:.1f} |"
        )
    lines += [
        "",
        "## Allocation audit",
        "",
        "Per-parse cumulative bytes; collection counts cover two parses. "
        "Taro allocation counts are counter-slope estimates; Rust counts include reallocations. "
        "Swift cumulative counters are unavailable; ARC has no tracing collections.",
        "",
        "| Case | Allocations/parse | Allocated MiB/parse | Collections / 2 parses |",
        "|---|---:|---:|---:|",
    ]
    for name, case in cases.items():
        audit = case.get("audit")
        if not audit:
            continue
        allocations = audit.get(
            "allocations_per_op", audit.get("allocations_per_op_estimate")
        )
        lines.append(
            f"| {name} | {allocations:,.0f} | {audit['allocated_bytes_per_op'] / 1024**2:.2f} | {audit['collections_in_two_ops']} |"
        )
    lines += [
        "",
        "## DOM range, throughput and peak memory",
        "",
        "| Case | Round median range, ms | MB/s | Peak process MiB |",
        "|---|---:|---:|---:|",
    ]
    for name, case in cases.items():
        if not run.is_dom(case["case"]):
            continue
        timing = case["timing"]
        low, high = timing["round_range_ms"]
        lines.append(
            f"| {name} | {low:.3f}–{high:.3f} | {timing['decimal_MB_per_second']:.1f} | {timing['peak_process_rss_bytes'] / 1024**2:.1f} |"
        )
    lines += [
        "",
        "Raw samples, whole-process CPU/instruction counters, observations and identities "
        "are in neighboring JSON files. Read the corpus README for representation, GC and counter caveats. "
        "public typed decoding constructs the requested model without an intermediate DOM.",
        "",
    ]
    return "\n".join(lines)


def main():
    ids = run.identity()
    timings = json.loads((run.OUT / "timings.json").read_text())
    audits = json.loads((run.OUT / "audit.json").read_text())
    checks = json.loads((run.OUT / "checks.json").read_text())
    for data in [timings, audits, checks]:
        if data["identities"] != ids:
            raise RuntimeError("stale binary identities")
    if (
        not timings.get("complete")
        or {run.key(r["case"]) for r in checks["rows"]}
        != {run.key(c) for c in run.cases()}
        or not all(r["ok"] for r in checks["rows"])
    ):
        raise RuntimeError("incomplete timings or checks")
    fixtures = json.loads((run.HERE / "fixtures.json").read_text())
    sizes = {f["name"]: f["bytes"] for f in fixtures["files"]}
    groups, audit_groups = defaultdict(list), defaultdict(list)
    for row in timings["rows"]:
        groups[run.key(row["case"])].append(row)
    for row in audits["rows"]:
        audit_groups[run.key(row["case"])].append(row)
    report = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "fixtures": fixtures,
        "identities": ids,
        "toolchain": json.loads((run.OUT / "toolchain.json").read_text()),
        "rejected_processes": len(timings["rejected"]),
        "cases": {},
    }
    for case in run.cases():
        name = run.key(case)
        entry = {
            "case": case,
            "timing": timing_summary(groups[name], sizes[case["dataset"]]),
        }
        if case["language"] != "swift":
            entry["audit"] = audit_summary(case["language"], audit_groups[name])
        report["cases"][name] = entry
    run.save(run.OUT / "report.json", report)
    (run.OUT / "report.md").write_text(render(report))
    print(run.OUT / "report.md")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    args = parser.parse_args()
    main()
