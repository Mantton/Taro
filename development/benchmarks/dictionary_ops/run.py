#!/usr/bin/env python3
"""Run prebuilt fixtures serially; rotate language order and verify checksums."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import statistics
import subprocess
import time


def expected(case, count, entries):
    if case == "construct":
        return 0
    if case == "construct_insert":
        return count
    if case in ("first_insert", "insert_new"):
        return count * (count + 1) // 2
    if case == "miss":
        return -count
    if case == "hit":
        whole, tail = divmod(count, entries)
        return whole * entries * (entries + 1) // 2 + tail * (tail + 1) // 2
    return sum(1 + (j + ((count - 1 - j) // entries) * entries if j < count else j)
               for j in range(entries))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--taro", type=Path, required=True)
    p.add_argument("--go", type=Path, required=True)
    p.add_argument("--rust", type=Path, required=True)
    p.add_argument("--baseline", type=Path, help="Add an unchanged Taro binary for before/after comparison")
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--runs", type=int, default=5)
    p.add_argument("--smoke", action="store_true")
    args = p.parse_args()
    binaries = {name: getattr(args, name).resolve() for name in ("taro", "go", "rust")}
    if args.baseline:
        binaries = {"before": args.baseline.resolve(), "after": binaries["taro"],
                    "go": binaries["go"], "rust": binaries["rust"]}
    cases = [(c, 1) for c in ("construct", "construct_insert", "first_insert")]
    cases += [("insert_new", n) for n in (1, 16)]
    cases += [(c, n) for n in (1, 16) for c in ("overwrite", "hit", "miss")]
    env = dict(os.environ, TARO_WORKERS="1", GOMAXPROCS="1")
    # The caller must finish every build before running this script.
    for k in ("TARO_GC_STRESS", "TARO_RUNTIME_STATS", "TARO_GC_STATS", "GOGC", "GOMEMLIMIT"):
        env.pop(k, None)
    samples = []
    for case, entries in cases:
        count = (1025 if case in ("first_insert", "insert_new") else 31) if args.smoke else (1_000_000 if case in ("construct", "construct_insert", "first_insert", "insert_new") else 10_000_000)
        # Untimed process warm-up; still check it, and keep the main samples cold-process.
        for name, binary in binaries.items():
            warm = subprocess.run([str(binary), case, "31", str(entries)], env=env, capture_output=True, text=True, check=True, timeout=60)
            assert int(re.search(r"checksum=(-?\d+)", warm.stdout)[1]) == expected(case, 31, entries)
        for run in range(args.runs):
            names = list(binaries)
            if args.baseline:
                # Alternate the relative before/after order explicitly.
                if run % 2:
                    names.reverse()
            else:
                names = names[run % len(names):] + names[:run % len(names)]
                if run % 2:
                    names.reverse()
            for name in names:
                load = os.getloadavg()
                started = time.monotonic()
                process = subprocess.run(["/usr/bin/time", "-l", str(binaries[name]), case, str(count), str(entries)], env=env, capture_output=True, text=True, check=True, timeout=90)
                fields = dict(re.findall(r"(\w+)=([^\s]+)", process.stdout))
                assert int(fields["checksum"]) == expected(case, count, entries), (name, case, process.stdout)
                clocks = re.search(r"([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", process.stderr)
                def counter(label):
                    m = re.search(r"(\d+)\s+" + label, process.stderr)
                    return int(m[1]) if m else None
                sample = dict(language=name, case=case, entries=entries, iterations=count, run=run,
                              elapsed_ns=int(fields["elapsed_ns"]), ns_per_op=int(fields["elapsed_ns"])/count,
                              checksum=int(fields["checksum"]), load_before=load,
                              process_wall_seconds=time.monotonic()-started,
                              user_seconds=float(clocks[2]), system_seconds=float(clocks[3]),
                              instructions=counter("instructions retired"), cycles=counter("cycles elapsed"),
                              max_rss_bytes=counter("maximum resident set size"))
                samples.append(sample)
                print(f"{case}/{entries} {name} {sample['ns_per_op']:.2f} ns/op", flush=True)
        args.output.write_text(json.dumps(dict(host=platform.platform(), samples=samples), indent=2)+"\n")
    summary = []
    for case, entries in cases:
        row = dict(case=case, entries=entries)
        for name in binaries:
            values = [s["ns_per_op"] for s in samples if (s["case"], s["entries"], s["language"]) == (case, entries, name)]
            row[name] = dict(median_ns=statistics.median(values), min_ns=min(values), max_ns=max(values))
        summary.append(row)
    result = dict(host=platform.platform(), source_commit=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
                  binaries={n: dict(path=str(b), sha256=hashlib.sha256(b.read_bytes()).hexdigest()) for n, b in binaries.items()},
                  summary=summary, samples=samples)
    args.output.write_text(json.dumps(result, indent=2)+"\n")


if __name__ == "__main__":
    main()
