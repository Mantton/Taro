#!/usr/bin/env python3
"""Audit a prebuilt allocation_audit.tr; keep the JSON output outside Git."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


CASES = {
    "baseline": 0, "new-builder": 0, "new-buffer": 0,
    "span-copy": 23, "io-write": 23, "buffer-write": 23,
    "printf-integer": 2, "builder-snapshot": 23,
    "encode-person": 23, "encode-people": 3073,
    "stream-person": 23, "stream-people": 3073,
    "encode-bool": 4, "encode-integer": 2, "encode-string": 5,
}


def fields(line):
    return {key: int(value) for key, value in re.findall(r"(\w+)=(\d+)", line)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    binary = args.binary.resolve()
    env = dict(os.environ, TARO_WORKERS="1", TARO_RUNTIME_STATS="1")
    for key in ("TARO_GC_PERCENT", "TARO_GC_MEMORY_LIMIT", "TARO_GC_STRESS", "TARO_GC_TRACE", "TARO_RUNTIME_TRACE"):
        env.pop(key, None)
    rows = []
    for case, size in CASES.items():
        for count in (128, 256, 512):
            result = subprocess.run([str(binary), case, str(count)], env=env,
                                    capture_output=True, text=True, check=True, timeout=30)
            combined = result.stdout + result.stderr
            audit = next(line for line in combined.splitlines() if line.startswith("audit "))
            runtime = next(line for line in combined.splitlines() if line.startswith("  gc collections="))
            values, totals = fields(audit), fields(runtime)
            assert values["iterations"] == count
            assert values["checksum"] == size * count, (case, values)
            writes = {"io-write": 1, "stream-person": 15, "stream-people": 2049}.get(case, 0)
            assert values["writes"] == writes * count, (case, values)
            rows.append(dict(case=case, count=count, loop=values, process=totals, raw=combined))
    summary = []
    for case in CASES:
        samples = [row for row in rows if row["case"] == case]
        allocation_slopes = [(b["process"]["allocations"] - a["process"]["allocations"]) / (b["count"] - a["count"])
                             for a, b in zip(samples, samples[1:])]
        byte_counts = [row["loop"]["bytes"] / row["count"] for row in samples]
        assert len(set(byte_counts)) == 1, (case, byte_counts)
        # Process totals include reporting after the loop. Tiny changes in its
        # internal formatting can contribute an extra allocation. Require a
        # consistent integer slope within two allocations per process delta;
        # keep both raw slopes rather than presenting that estimate as exact.
        estimate = round(sum(allocation_slopes) / len(allocation_slopes))
        for slope, a, b in zip(allocation_slopes, samples, samples[1:]):
            assert abs((slope - estimate) * (b["count"] - a["count"])) <= 2, (case, allocation_slopes)
        summary.append(dict(case=case, estimated_allocations_per_op=estimate,
                            raw_allocation_slopes=allocation_slopes,
                            allocated_bytes_per_op=byte_counts[0],
                            writer_calls_per_op=samples[0]["loop"]["writes"] / samples[0]["count"]))
    report = dict(binary=str(binary), sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                  rows=rows, summary=summary,
                  definitions="Loop bytes come from gcStats deltas, excluding fixtures and reporting, and must be identical per operation at 128/256/512 iterations. Estimated allocation counts are rounded whole-process runtime counter slopes at the same counts, allowing at most two allocations of reporting variation per process delta; raw slopes are retained. Bytes are cumulative runtime-accounted allocation sizes, not requested payload or peak RSS. These are diagnostics, not timing samples.")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    for row in summary:
        print(f"{row['case']}: ~{row['estimated_allocations_per_op']:g} allocations, "
              f"{row['allocated_bytes_per_op']:g} bytes, {row['writer_calls_per_op']:g} writes")


if __name__ == "__main__":
    main()
