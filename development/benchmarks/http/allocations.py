#!/usr/bin/env python3
"""Attribute Taro server allocations to call stacks; counts only, never timings.

Builds the runtime with its alloc-profile feature, links the benchmark server
against a disposable SDK copy, drives it with wrk and writes a per-request
breakdown under the ignored --out directory.
"""
import argparse
import collections
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

import compare

sys.path.insert(0, str(compare.ROOT / "development/benchmarks/json/corpus"))
import run


def build(out, env, compiler=None):
    cargo = out / "cargo"
    run.checked(["cargo", "build", "-p", "taro-runtime", "--release", "--features", "alloc-profile", "--target-dir", cargo], "alloc-profile-runtime", env, seconds=500)
    with tempfile.TemporaryDirectory(prefix="taro-alloc-profile-", dir="/private/tmp") as directory:
        sdk = Path(directory) / "sdk"
        shutil.copytree(compare.ROOT / "dist", sdk, symlinks=True)
        if compiler:
            shutil.copy2(compiler, sdk / "bin/taro")
        runtime = sdk / "lib/taro/runtime/libtaro_runtime.a"
        shutil.copy2(cargo / "release/libtaro_runtime.a", runtime)
        build_env = dict(env, TARO_HOME=str(sdk))
        run.checked([sdk / "bin/taro", "runtime-manifest", runtime], "alloc-profile-manifest", build_env)
        # SDK builds link attached std artifacts, not the std sources: rebuild them
        # so the profile describes the working tree.
        bootstrap = Path(directory) / "bootstrap.tr"
        bootstrap.write_text("func main() {}\n")
        run.checked([sdk / "bin/taro", "check", bootstrap, "--std-path", compare.ROOT / "std", "--build-std"], "alloc-profile-std", build_env, seconds=500)
        run.checked([sdk / "bin/taro", "build", compare.HERE / "servers/taro.tr", "--release", "-O3", "-o", out / "taro-server"], "alloc-profile-server", build_env, seconds=180)
    shutil.rmtree(cargo)


def symbolize(binary, addresses):
    if not addresses:
        return {}
    text = subprocess.run(["atos", "-o", str(binary)], input="\n".join(addresses), capture_output=True, text=True, check=True, timeout=120).stdout
    names = text.splitlines()
    assert len(names) == len(addresses)
    return {address: name.split(" (in ")[0] for address, name in zip(addresses, names)}


def is_runtime_frame(name):
    return "taro_runtime" in name or name.startswith(("__gc__", "__rt__", "_Unwind", "__unw", "libunwind")) or "alloc_profile" in name


def analyse(path, binary, requests):
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    names = symbolize(binary, sorted({frame for row in rows for frame in row["frames"]}))
    for row in rows:
        row["names"] = [names[frame] for frame in row["frames"]]
        # The profiler and allocator frames are never the interesting attribution.
        row["names"] = [name for name in row["names"] if "alloc_profile" not in name and "__rust_alloc" not in name and "__rdl_" not in name and "_Unwind" not in name]
    managed = [row for row in rows if row["desc"] != "0x0"]
    native = [row for row in rows if row["desc"] == "0x0"]

    def table(key_of, selected, limit=60):
        counts = collections.Counter()
        bytes_ = collections.Counter()
        for row in selected:
            key = key_of(row)
            counts[key] += row["count"]
            bytes_[key] += row["count"] * row["size"]
        return [{"per_request": round(count / requests, 3), "bytes_per_request": round(bytes_[key] / requests, 1), "site": key} for key, count in counts.most_common(limit)]

    def first_generated(row):
        return next((name for name in row["names"] if not is_runtime_frame(name)), " < ".join(row["names"][:3]))

    def runtime_entry(row):
        return " < ".join(row["names"][:4])

    def inclusive(selected, limit=80):
        counts = collections.Counter()
        bytes_ = collections.Counter()
        for row in selected:
            for name in set(row["names"]):
                counts[name] += row["count"]
                bytes_[name] += row["count"] * row["size"]
        return [{"per_request": round(count / requests, 3), "bytes_per_request": round(bytes_[name] / requests, 1), "site": name} for name, count in counts.most_common(limit)]

    total = sum(row["count"] for row in managed)
    return {
        "requests": requests,
        "managed_per_request": round(total / requests, 2),
        "managed_bytes_per_request": round(sum(row["count"] * row["size"] for row in managed) / requests, 1),
        "native_per_request": round(sum(row["count"] for row in native) / requests, 2),
        "native_bytes_per_request": round(sum(row["count"] * row["size"] for row in native) / requests, 1),
        "managed_by_function": table(first_generated, managed),
        "managed_inclusive": inclusive(managed),
        "managed_by_descriptor": table(lambda row: f"{row['desc']} size={row['desc_size']} nodes={row['desc_nodes']} pointers={row['pointers']} request={row['size']}", managed, 40),
        "native_by_stack": table(runtime_entry, native),
        "native_inclusive": inclusive(native),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--artifacts", type=Path, required=True, help="Directory holding a built wrk, as used by compare.py")
    parser.add_argument("--connections", type=int, default=32)
    parser.add_argument("--seconds", type=int, default=5)
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--compiler", type=Path, help="Compiler to use instead of the installed SDK's")
    args = parser.parse_args()
    assert 1 <= args.connections <= 128 and 1 <= args.seconds <= 15
    out = args.out.resolve()
    subprocess.run(["git", "check-ignore", "-q", str(out / "report.json")], cwd=compare.ROOT, check=True)
    out.mkdir(parents=True, exist_ok=True)
    run.OUT = out
    env = dict(run.environment(), CARGO_BUILD_JOBS="1", CARGO_INCREMENTAL="0", CARGO_PROFILE_RELEASE_DEBUG="0")
    if not args.skip_build:
        build(out, env, args.compiler and args.compiler.resolve())
    artifacts = args.artifacts.resolve()
    report = {"notes": "Whole bounded process including startup and drain; unwinding makes throughput meaningless."}
    for endpoint in ["text", "json"]:
        raw = out / (endpoint + ".jsonl")
        raw.unlink(missing_ok=True)
        # compare.Server resolves its binary beside the artifacts directory and
        # inherits this environment; the report path is the only addition.
        os.environ["TARO_ALLOC_PROFILE"] = str(raw)
        server = compare.Server("taro", out / "unused", out / (endpoint + "-server.log"), 1, diagnostic_seconds=args.seconds + 4)
        try:
            compare.request(server.port, endpoint)
            loaded = compare.load(server, artifacts, out, endpoint, args.connections, args.seconds, endpoint + "-load")
            server.process.wait(timeout=args.seconds + 20)
            assert server.process.returncode == 0, (out / (endpoint + "-server.log")).read_text()[-3000:]
        finally:
            server.close()
        report[endpoint] = {"load": loaded, **analyse(raw, out / "taro-server", loaded["requests"] + 1)}
        compare.save(out / "report.json", report)
    print("Allocation breakdown saved to", out / "report.json")


if __name__ == "__main__":
    main()
