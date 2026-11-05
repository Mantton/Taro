#!/usr/bin/env python3
"""Measure prebuilt JSON fixtures serially; save raw data outside Git.

Taro's existing cases run once; record cases and host references run in
rotating order for three rounds. Each process calibrates and takes 20 samples.
Only the small, unique-key ASCII record schema is compared across languages.
"""
import argparse
import ctypes
import ctypes.util
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import time


def observation():
    """Read aggregate CPU ticks on macOS without running a competing profiler."""
    library = ctypes.CDLL(ctypes.util.find_library("System"))
    library.mach_host_self.restype = ctypes.c_uint
    host = library.mach_host_self()

    def ticks():
        values = (ctypes.c_uint * 4)()
        count = ctypes.c_uint(4)
        if library.host_statistics(host, 3, values, ctypes.byref(count)):
            raise RuntimeError("cannot read CPU ticks")
        return list(values)

    before = ticks()
    # macOS may return a cached snapshot to consecutive unprivileged queries.
    # Retry a stationary counter rather than inventing an idle percentage.
    for _ in range(10):
        time.sleep(1)
        after = ticks()
        delta = [(b - a) % (1 << 32) for a, b in zip(before, after)]
        if sum(delta):
            break
    else:
        raise RuntimeError("CPU counters did not advance")
    return {"load": os.getloadavg(), "idle_pct": 100 * delta[2] / sum(delta)}


def quiet(value):
    return value["load"][0] <= 4 and value["idle_pct"] >= 70


def execute(command, env):
    """Bound wall time and process-tree RSS without altering runtime GC policy."""
    start = time.monotonic()
    with subprocess.Popen(command, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True, start_new_session=True) as child:
        try:
            while child.poll() is None:
                if time.monotonic() - start > 60:
                    raise RuntimeError(f"timeout: {command}")
                listing = subprocess.check_output(
                    ["ps", "-axo", "pid=,ppid=,rss="], text=True)
                processes = [tuple(map(int, line.split())) for line in listing.splitlines()]
                descendants = {child.pid}
                while True:
                    expanded = descendants | {pid for pid, parent, _ in processes if parent in descendants}
                    if expanded == descendants:
                        break
                    descendants = expanded
                if sum(rss for pid, _, rss in processes if pid in descendants) > 4 * 1024**2:
                    raise RuntimeError("benchmark process tree exceeds 4 GiB RSS")
                time.sleep(0.5)
            stdout, stderr = child.communicate()
            if child.returncode:
                raise RuntimeError(f"{command}: {stderr}\n{stdout}")
            return stdout
        except BaseException:
            import signal
            try:
                os.killpg(child.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            child.wait()
            raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for language in ("taro", "go", "rust"):
        parser.add_argument(f"--{language}", type=Path, required=True)
    parser.add_argument("--swift", type=Path, help="Optional Foundation JSONEncoder/JSONDecoder reference")
    parser.add_argument("--baseline", type=Path, help="Unchanged Taro binary for a before/after comparison")
    parser.add_argument("--encoding-only", action="store_true", help="Measure only the encoder cases")
    parser.add_argument("--filter", help="Case-insensitive substring of native/reference case names")
    parser.add_argument("--taro-filter", help="Additional native-only case-name substring")
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    binaries = {language: getattr(args, language).resolve() for language in ("taro", "go", "rust")}
    if args.swift:
        binaries["swift"] = args.swift.resolve()
    if args.rounds < 1:
        parser.error("--rounds must be positive")
    if args.baseline:
        binaries = {"baseline": args.baseline.resolve(), **binaries}
    native = [language for language in binaries if language in ("baseline", "taro")]
    identities = {language: hashlib.sha256(path.read_bytes()).hexdigest()
                  for language, path in binaries.items()}
    output = args.output.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    report = json.loads(output.read_text()) if output.exists() else {
        "identities": identities, "encoding_only": args.encoding_only, "filter": args.filter,
        "taro_filter": args.taro_filter, "rounds": args.rounds,
        "observations": [], "rows": [], "rejected": []}
    if report["identities"] != identities:
        raise RuntimeError("saved results belong to different binaries")
    if report.get("encoding_only", False) != args.encoding_only:
        raise RuntimeError("saved results use different case selection")
    if report.get("filter") != args.filter:
        raise RuntimeError("saved results use a different filter")
    if report.get("taro_filter") != args.taro_filter or report.get("rounds", 3) != args.rounds:
        raise RuntimeError("saved results use different native case selection or round count")

    def save():
        temporary = output.with_suffix(".tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(output)

    env = dict(os.environ, TARO_WORKERS="1", GOMAXPROCS="1")
    for key in ("TARO_GC_STRESS", "TARO_GC_PERCENT", "TARO_GC_MEMORY_LIMIT", "TARO_GC_TRACE",
                "TARO_RUNTIME_STATS", "TARO_RUNTIME_TRACE", "GOGC", "GOMEMLIMIT", "GODEBUG"):
        env.pop(key, None)
    for _ in range(3):
        value = observation()
        report["observations"].append(value)
        save()
        if not quiet(value):
            print("System is busy; saved results can be resumed.")
            return
        time.sleep(10)
    protocol = output.with_suffix(".protocol.jsonl")
    protocol.unlink(missing_ok=True)
    env.update(TARO_BENCH_ACTION="list", TARO_BENCH_PROTOCOL_PATH=str(protocol))
    execute([str(binaries["taro"])], env)
    cases = [json.loads(line) for line in protocol.read_text().splitlines()]
    if args.encoding_only:
        cases = [case for case in cases if "encode" in case["tags"]]
    if args.filter:
        cases = [case for case in cases if args.filter.lower() in case["name"].lower()]
    if args.taro_filter:
        cases = [case for case in cases if args.taro_filter.lower() in case["name"].lower()]
    if not cases:
        raise RuntimeError("no matching Taro benchmark cases")
    schedule = [(0, language, case["name"]) for case in cases
                if "codable" not in case["tags"] for language in native]
    records = [case["name"] for case in cases if "codable" in case["tags"]]
    references = [op + shape for op in ("decode", "encode") for shape in ("Person", "People128")]
    if args.encoding_only:
        references = [case for case in references if case.startswith("encode")]
    if args.filter:
        references = [case for case in references if args.filter.lower() in case.lower()]
    languages = list(binaries)
    for round_index in range(args.rounds):
        rotation = round_index % len(languages)
        for language in languages[rotation:] + languages[:rotation]:
            schedule.extend((round_index, language, case) for case in
                            (records if language in native else references))
    for round_index, language, case in schedule:
        if any((row["round"], row["language"], row["case"]) == (round_index, language, case)
               for row in report["rows"]):
            continue
        before = observation()
        if not quiet(before):
            report["observations"].append(before)
            save()
            print("System is busy; saved results can be resumed.")
            return
        if language in native:
            protocol.unlink(missing_ok=True)
            env.update(TARO_BENCH_ACTION="run", TARO_BENCH_CASE=case,
                       TARO_BENCH_WARMUP_NS="250000000", TARO_BENCH_MEASUREMENT_NS="1000000000",
                       TARO_BENCH_SAMPLES="20")
            execute([str(binaries[language])], env)
            data = [json.loads(line) for line in protocol.read_text().splitlines()]
            data = next(row for row in data if row["kind"] == "result")
            if data["status"] != "ok":
                raise RuntimeError(data)
        else:
            data = json.loads(execute([str(binaries[language]), case], env))
        if len(data["samples_ns_per_op"]) != 20:
            raise RuntimeError("missing samples")
        after = observation()
        row = {"round": round_index, "language": language, "case": case,
               "before": before, "after": after, "data": data}
        report["rows" if quiet(after) else "rejected"].append(row)
        save()
        if not quiet(after):
            print("Load rose during a sample; rejected it and saved progress.")
            return
        print(f"{round_index + 1} {language} {case}: "
              f"{statistics.median(data['samples_ns_per_op']) / 1000:.3f} us/op", flush=True)
    protocol.unlink(missing_ok=True)
    report["complete"] = True
    save()


if __name__ == "__main__":
    main()
