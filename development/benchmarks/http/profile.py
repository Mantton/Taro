#!/usr/bin/env python3
"""Sample a prebuilt server separately from throughput measurements (macOS)."""
import argparse
import concurrent.futures
import json
from pathlib import Path
import subprocess
import time

import compare

RECORDS = json.dumps([dict(id=i, message=f"record {i}") for i in range(20)], separators=(",", ":")).encode()
for route in ["stage/static", "stage/sleep", "stage/encode", "app"]:
    compare.PAYLOADS[route] = RECORDS


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, required=True)
    parser.add_argument("--language", choices=compare.LANGUAGES + compare.TARO_VARIANTS, default="taro")
    parser.add_argument("--endpoint", choices=list(compare.PAYLOADS), default="text")
    parser.add_argument("--connections", type=int, default=32)
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--out", type=Path, help="Separate ignored directory for this profile")
    parser.add_argument("--profiler", choices=["sample", "time-profiler"], default="sample")
    args = parser.parse_args()
    assert 1 <= args.connections <= 128
    assert 1 <= args.workers <= 8
    artifacts = args.artifacts.resolve()
    out = args.out.resolve() if args.out else artifacts / ("profile-" + args.language)
    subprocess.run(["git", "check-ignore", "-q", str(out / "sample.txt")], cwd=compare.ROOT, check=True)
    out.mkdir(parents=True, exist_ok=True)
    compare.bounded.OUT = out
    server = compare.Server(args.language, artifacts, out / "server.log", args.workers)
    try:
        compare.request(server.port, args.endpoint)
        compare.load(server, artifacts, out, args.endpoint, args.connections, 5, "warmup")
        with concurrent.futures.ThreadPoolExecutor(max_workers=1) as pool:
            seconds = 15 if args.profiler == "time-profiler" else 8
            load = pool.submit(compare.load, server, artifacts, out, args.endpoint, args.connections, seconds, "profiled-load")
            time.sleep(1)
            command = (["sample", str(server.process.pid), "3", "1", "-file", out / "sample.txt"]
                       if args.profiler == "sample" else
                       ["xcrun", "xctrace", "record", "--template", "Time Profiler", "--attach", str(server.process.pid),
                        "--time-limit", "5s", "--output", out / "recording.trace", "--no-prompt"])
            compare.bounded.checked(command, "profiler-command", compare.bounded.environment(), seconds=30)
            result = load.result()
        compare.save(out / "metadata.json", {"language": args.language, "pid": server.process.pid, "endpoint": args.endpoint, "connections": args.connections, "workers": args.workers, "profiler": args.profiler, "note": "Profiling perturbs execution; exclude this run from throughput comparisons. sample includes blocked threads; Time Profiler records running CPU samples. Sample weights are statistical estimates, not exact function timings.", "profiled_load": result})
        print("Separate profile saved to", out)
    finally:
        server.close()


if __name__ == "__main__":
    main()
