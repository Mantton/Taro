#!/usr/bin/env python3
"""Sample a Taro Monkey tree walker; summarize only its main-thread stack."""
import argparse
from collections import Counter
import gzip
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


def summarize(report, categories=None):
    stack = []
    active = False
    total = None
    categories = categories if categories is not None else {
        "gc": lambda f: "initiate_collection" in f,
        "allocator_including_gc": lambda f: any(x in f for x in ("runtime_alloc", "__gc__alloc", "__gc__buffer_new", "alloc_small", "try_cached_small_allocation")),
        "environment_constructor_including_allocation_and_gc": lambda f: "__enclosedBy__" in f,
        "dictionary_initialization": lambda f: "filledDictionarySlots" in f,
        "buffer_publication": lambda f: "__gc__buffer_publish" in f,
        "taro_hashing": lambda f: "__hash__" in f,
        "environment_lookup": lambda f: "__lookup__" in f,
    }
    inclusive, self_counts, exclusive = Counter(), Counter(), Counter()

    def finish(node):
        own = node["count"] - node["children"]
        assert own >= 0, node
        self_counts[node["function"]] += own
        for name in node["matched"]:
            inclusive[name] += own
        bucket = next((name for name in categories if name in node["matched"]), "other")
        exclusive[bucket] += own

    # Stream the large recursive call graph; retain only the current stack.
    for line in report:
        if "com.apple.main-thread" in line and "Thread_" in line:
            total = int(line.split()[0])
            active = True
            continue
        if not active:
            continue
        if "Thread_" in line or line.startswith("Total number in stack"):
            break
        m = re.match(r"^([ +!:|]*)(\d+) (.*?)  \(in ", line)
        if not m:
            continue
        depth, count, function = len(m[1]), int(m[2]), m[3]
        while stack and stack[-1]["depth"] >= depth:
            finish(stack.pop())
        matched = {name for name, test in categories.items() if test(function)}
        if stack:
            matched |= stack[-1]["matched"]
        node = dict(depth=depth, count=count, function=function, children=0, matched=matched)
        if stack:
            stack[-1]["children"] += count
        stack.append(node)
    while stack:
        finish(stack.pop())
    assert total and self_counts
    assert sum(self_counts.values()) == total, (sum(self_counts.values()), total)
    return dict(samples=total, inclusive_samples=dict(inclusive),
                inclusive_percent={k: 100*v/total for k, v in inclusive.items()},
                exclusive_priority_samples=dict(exclusive),
                top_self=[dict(function=k, samples=v, percent=100*v/total) for k, v in self_counts.most_common(35)],
                caveat="Statistical main-thread wall samples, including time blocked in syscalls. Inclusive categories overlap; recursive occurrences count once per stack. Exclusive buckets prioritize GC, allocation, construction, then named helpers. Inlined work belongs to its enclosing symbol.")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--binary", type=Path, required=True)
    p.add_argument("--input", type=Path, required=True)
    p.add_argument("--checksum", required=True)
    p.add_argument("--output-prefix", type=Path, required=True)
    args = p.parse_args()
    prefix = args.output_prefix
    raw = Path(str(prefix)+".sample.txt")
    output = Path(str(prefix)+".stdout.txt")
    before = os.getloadavg()
    with output.open("w") as log:
        process = subprocess.Popen([str(args.binary), str(args.input), "--engine", "eval"], env=dict(os.environ, TARO_WORKERS="1"), stdout=log, stderr=subprocess.STDOUT)
        try:
            time.sleep(.4)
            subprocess.run(["/usr/bin/sample", str(process.pid), "8", "1", "-file", str(raw)], check=True, timeout=20, capture_output=True)
            assert process.wait(timeout=90) == 0
        finally:
            if process.poll() is None:
                process.kill()
                process.wait()
    assert output.read_text().strip() == args.checksum, output.read_text()
    with raw.open() as report:
        summary = summarize(report)
    summary.update(binary=str(args.binary), input=str(args.input), checksum=args.checksum, load_before=before, load_after=os.getloadavg())
    Path(str(prefix)+".json").write_text(json.dumps(summary, indent=2)+"\n")
    with raw.open("rb") as report, gzip.open(str(raw)+".gz", "wb") as compressed:
        shutil.copyfileobj(report, compressed)
    raw.unlink()
    print(json.dumps({k: summary[k] for k in ("samples", "inclusive_percent", "exclusive_priority_samples")}, indent=2))


if __name__ == "__main__":
    main()
