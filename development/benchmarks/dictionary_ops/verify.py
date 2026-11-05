#!/usr/bin/env python3
"""Focused GC-stress checks and separate Taro allocation-scaling probes."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

from run import expected


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--taro", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    cases = [(c, 1) for c in ("construct", "construct_insert", "first_insert")]
    cases += [("insert_new", n) for n in (1, 16)]
    cases += [(c, n) for n in (1, 16) for c in ("overwrite", "hit", "miss")]
    samples = []
    env = dict(os.environ, TARO_WORKERS="1", TARO_RUNTIME_STATS="1")
    for case, entries in cases:
        for count, stress in ((33, True), (1000, False), (10000, False)):
            config = dict(env, TARO_GC_STRESS="1" if stress else "0")
            run = subprocess.run([str(args.taro.resolve()), case, str(count), str(entries)], env=config, capture_output=True, text=True, check=True, timeout=60)
            checksum = int(re.search(r"checksum=(-?\d+)", run.stdout)[1])
            assert checksum == expected(case, count, entries), (case, count, run.stdout)
            stats = re.search(r"gc collections=(\d+) allocations=(\d+) frees=\d+ allocated_bytes=(\d+)", run.stderr)
            assert stats, run.stderr
            samples.append(dict(case=case, entries=entries, iterations=count, stress=stress, checksum=checksum,
                                collections=int(stats[1]), allocations=int(stats[2]), allocated_bytes=int(stats[3])))
    scaling = []
    for case, entries in cases:
        small, large = [s for s in samples if s["case"] == case and s["entries"] == entries and not s["stress"]]
        scaling.append(dict(case=case, entries=entries,
                            allocations_per_op=(large["allocations"]-small["allocations"])/9000,
                            bytes_per_op=(large["allocated_bytes"]-small["allocated_bytes"])/9000))
    result = dict(samples=samples, scaling=scaling,
                  caveat="Runtime counters include process startup/reporting; subtract 1000 from 10000 iterations. Batched-insertion counters also include untimed preparation and checksum reads: do not attribute their allocations to insertion alone.")
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(scaling, indent=2))


if __name__ == "__main__":
    main()
