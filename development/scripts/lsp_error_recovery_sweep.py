#!/usr/bin/env python3
"""Check every invalid language fixture with the editor's error-recovering analysis.

Each fixture is analyzed as a standalone script by one long-lived worker. The
sweep reports fixtures whose analysis panicked (the worker then falls back to
the strict check), failed, or returned no navigation facts. Results go to an
ignored directory; nothing is written into the checkout's tracked files.
"""

import argparse
import json
import os
from pathlib import Path
import select
import struct
import subprocess
import sys
import tempfile
import time

PROJECT_ROOT = Path(__file__).resolve().parents[2]
SCHEMA = 2
FRAME_LIMIT = 128 * 1024 * 1024


def read_exact(pipe, size, deadline):
    chunks = []
    while size:
        timeout = deadline - time.monotonic()
        if timeout <= 0 or not select.select([pipe], [], [], timeout)[0]:
            raise TimeoutError("analysis worker did not reply before the deadline")
        chunk = os.read(pipe.fileno(), size)
        if not chunk:
            raise EOFError("analysis worker exited")
        chunks.append(chunk)
        size -= len(chunk)
    return b"".join(chunks)


class Worker:
    def __init__(self, binary, sdk, log):
        self.log = log
        self.process = subprocess.Popen(
            [str(binary), "--worker", "--sdk", str(sdk)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=log,
        )
        self.revision = 0

    def analyze(self, script, timeout):
        self.revision += 1
        stamp = {"generation": 1, "revision": self.revision}
        inputs = {"Reset": {"root": str(script), "documents": {}}}
        request = {"schema": SCHEMA, "data": {"Analyze": {"stamp": stamp, "inputs": inputs}}}
        payload = json.dumps(request, separators=(",", ":")).encode()
        self.process.stdin.write(struct.pack(">I", len(payload)) + payload)
        self.process.stdin.flush()
        deadline = time.monotonic() + timeout
        size = struct.unpack(">I", read_exact(self.process.stdout, 4, deadline))[0]
        if not 0 < size <= FRAME_LIMIT:
            raise ValueError(f"invalid reply size {size}")
        return json.loads(read_exact(self.process.stdout, size, deadline))["data"]

    def close(self):
        self.process.kill()
        self.process.wait()


def classify(reply):
    finished = reply.get("Finished")
    if finished is None:
        return {"status": "no-result"}
    result = finished["result"]
    if "Err" in result:
        return {"status": "error-result", "error": result["Err"]}
    product = result["Ok"]
    occurrences = len(product["occurrences"])
    return {
        "status": "facts" if occurrences else "no-facts",
        "occurrences": occurrences,
        "diagnostics": [
            diagnostic["message"]
            for diagnostic in product["diagnostics"]
            if diagnostic["level"] == "Error"
        ],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bin", type=Path, required=True, help="taro-lsp executable")
    parser.add_argument("--sdk", type=Path, required=True, help="Taro SDK directory")
    parser.add_argument("--filter", default="", help="only fixtures whose name contains this")
    parser.add_argument("--timeout", type=float, default=60)
    parser.add_argument(
        "--output",
        type=Path,
        default=PROJECT_ROOT / "target" / "lsp-error-recovery" / "sweep.json",
    )
    args = parser.parse_args()

    fixtures = sorted(
        path.resolve()
        for path in (PROJECT_ROOT / "language_tests/source_files/invalid").rglob("*.tr")
        if args.filter in path.name
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    results = []
    with tempfile.TemporaryFile(dir=args.output.parent) as log:
        worker = Worker(args.bin, args.sdk, log)
        for index, fixture in enumerate(fixtures, 1):
            start = log.seek(0, os.SEEK_END)
            entry = {"fixture": str(fixture.relative_to(PROJECT_ROOT))}
            try:
                entry.update(classify(worker.analyze(fixture, args.timeout)))
            except (EOFError, TimeoutError, ValueError) as error:
                entry.update(status="worker-failed", error=str(error))
                worker.close()
                worker = Worker(args.bin, args.sdk, log)
            log.seek(start)
            stderr = log.read().decode(errors="replace")
            panics = [line for line in stderr.splitlines() if "panicked at" in line]
            if panics:
                # The worker recovered by falling back to the strict check.
                lines = stderr.strip().splitlines()
                entry["panic"] = lines[lines.index(panics[0]) + 1] if panics[0] != lines[-1] else ""
                entry["panic_at"] = panics[0].split("panicked at ", 1)[1]
            results.append(entry)
            print(f"[{index}/{len(fixtures)}] {entry['status']:<13} {entry['fixture']}"
                  + (f"  PANIC {entry['panic_at']}" if "panic" in entry else ""), flush=True)
        worker.close()

    args.output.write_text(json.dumps(results, indent=2) + "\n")
    summary = {}
    for entry in results:
        key = "panic" if "panic" in entry else entry["status"]
        summary[key] = summary.get(key, 0) + 1
    print(json.dumps(summary, indent=2))
    sites = {}
    for entry in results:
        if "panic" in entry:
            sites.setdefault(entry["panic_at"], []).append(entry["fixture"])
    for site, names in sorted(sites.items(), key=lambda item: -len(item[1])):
        print(f"{len(names):4}  {site}  e.g. {names[0]}")
    print(f"results: {args.output}")
    return 1 if sites or summary.get("worker-failed") else 0


if __name__ == "__main__":
    sys.exit(main())
