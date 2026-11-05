#!/usr/bin/env python3
"""Collect separate Taro/Go allocation and scheduler diagnostics, not timings."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import compare

RECORDS = json.dumps([dict(id=i, message=f"record {i}") for i in range(20)], separators=(",", ":")).encode()
for route in ["stage/static", "stage/sleep", "stage/encode", "app"]:
    compare.PAYLOADS[route] = RECORDS


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, required=True)
    parser.add_argument("--endpoint", choices=list(compare.PAYLOADS), default="text")
    parser.add_argument("--connections", type=int, default=32)
    parser.add_argument("--seconds", type=int, default=3)
    parser.add_argument("--taro-variant", choices=["taro", "taro-metadata"], default="taro")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--out", type=Path, help="Separate ignored directory for this diagnostic")
    args = parser.parse_args()
    assert 1 <= args.connections <= 128 and 1 <= args.seconds <= 15
    assert 1 <= args.workers <= 8
    artifacts = args.artifacts.resolve()
    out = args.out.resolve() if args.out else artifacts / ("diagnostics-" + args.endpoint.replace("/", "-") + "-" + args.taro_variant)
    subprocess.run(["git", "check-ignore", "-q", str(out / "report.json")], cwd=compare.ROOT, check=True)
    out.mkdir(parents=True, exist_ok=True)
    rows = []
    for language in [args.taro_variant, "go"]:
        log = out / (language + "-server.log")
        server = compare.Server(language, artifacts, log, args.workers,
                                diagnostic_seconds=args.seconds + 4 if language.startswith("taro") else None)
        try:
            compare.request(server.port, args.endpoint)
            initial = compare.request(server.port, "stats") if language == "go" else None
            loaded = compare.load(server, artifacts, out, args.endpoint, args.connections, args.seconds, language + "-load")
            row = {"language": language, "load": loaded}
            if language == "go":
                final = compare.request(server.port, "stats")
                row["counters"] = {key: final[key] - initial[key] for key in initial}
                row["counter_requests"] = loaded["requests"]
                row["scope"] = "Snapshot deltas around load, with small stats-route overhead; Go runtime allocations only."
            else:
                try:
                    server.process.wait(timeout=args.seconds + 10)
                except subprocess.TimeoutExpired as error:
                    raise RuntimeError("diagnostic server did not drain and exit normally") from error
                assert server.process.returncode == 0, log.read_text()[-3000:]
                server.log.flush()
                text = log.read_text()
                row["runtime"] = {
                    name: {key: int(value) if value.isdigit() else value for key, value in re.findall(r"(\w+)=([^\s]+)", body)}
                    for name, body in re.findall(r"^  (tasks|queues|timers|gc|gc_phase_ns) (.*)$", text, re.M)
                }
                assert "gc" in row["runtime"] and "tasks" in row["runtime"], text[-3000:]
                gc = row["runtime"]["gc"]
                row["counters"] = {"allocations": gc["allocations"], "allocatedBytes": gc["allocated_bytes"], "collections": gc["collections"], "pauseNanos": row["runtime"]["gc_phase_ns"]["pause_total"]}
                row["counter_requests"] = loaded["requests"] + 2
                row["scope"] = "Whole bounded process, including startup, two validation requests and drain. Per-request counts approximate steady state. Managed allocations exclude native bookkeeping."
            rows.append(row)
        finally:
            server.close()
    identity = artifacts / "identities.json"
    if not identity.exists():
        identity = artifacts.parent / "build-identities.json"
    compare.save(out / "report.json", {"config": vars(args) | {"artifacts": str(artifacts), "out": str(out)}, "identities": json.loads(identity.read_text()), "notes": "Run separately from throughput tests. Runtime counter definitions differ; cumulative allocation is not RSS.", "rows": rows})
    print("Allocation and scheduler diagnostics saved to", out)


if __name__ == "__main__":
    main()
