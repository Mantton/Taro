#!/usr/bin/env python3
"""Prepare pinned large documents and run prebuilt programs serially on macOS."""
import argparse, hashlib, importlib.util, json, math, os, re, shutil, signal, statistics, subprocess, sys, tempfile, time, urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
OUT = ROOT / "target/json-corpus"
compare_spec = importlib.util.spec_from_file_location(
    "compare", HERE.parent / "compare.py"
)
compare = importlib.util.module_from_spec(compare_spec)
compare_spec.loader.exec_module(compare)


def is_dom(case):
    return case["mode"] in {"dom"}


def save(path, value):
    temp = path.with_suffix(".tmp")
    temp.write_text(json.dumps(value, indent=2) + "\n")
    temp.replace(path)


def execute(command, label, env=None, seconds=180, timed=False):
    """File-backed logs avoid pipe deadlocks; bound wall time and tree RSS."""
    path = OUT / (label + ".log")
    start = time.monotonic()
    peak = 0
    failure = None
    argv = (["/usr/bin/time", "-l"] if timed else []) + list(map(str, command))
    with path.open("w") as log:
        child = subprocess.Popen(
            argv, env=env, stdout=log, stderr=subprocess.STDOUT, start_new_session=True
        )
        try:
            while child.poll() is None:
                rows = [
                    tuple(map(int, l.split()))
                    for l in subprocess.check_output(
                        ["ps", "-axo", "pid=,ppid=,rss="], text=True
                    ).splitlines()
                ]
                ids = {child.pid}
                while True:
                    expanded = ids | {pid for pid, parent, _ in rows if parent in ids}
                    if expanded == ids:
                        break
                    ids = expanded
                rss = sum(rss for pid, _, rss in rows if pid in ids) * 1024
                peak = max(peak, rss)
                if rss > 4 * 1024**3:
                    failure = "4 GiB process-tree RSS limit"
                    break
                if time.monotonic() - start > seconds:
                    failure = f"{seconds}s wall limit"
                    break
                time.sleep(0.25)
        finally:
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
            child.wait()
    text = path.read_text()
    match = re.search(r"^\s*(\d+)\s+maximum resident set size", text, re.M)
    if not failure and child.returncode:
        failure = f"exit {child.returncode}"
    usage = {}
    for name, pattern in [
        ("instructions_retired", r"(\d+)\s+instructions retired"),
        ("cycles_elapsed", r"(\d+)\s+cycles elapsed"),
        ("peak_footprint_bytes", r"(\d+)\s+peak memory footprint"),
    ]:
        value = re.search(pattern, text)
        if value:
            usage[name] = int(value[1])
    cpu = re.search(r"([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", text)
    if cpu:
        usage.update(
            real_seconds=float(cpu[1]),
            user_seconds=float(cpu[2]),
            system_seconds=float(cpu[3]),
        )
    return dict(
        ok=failure is None,
        failure=failure,
        log=str(path),
        wall_seconds=time.monotonic() - start,
        peak_rss_bytes=int(match[1]) if match else peak,
        process_usage=usage,
        text=text,
    )


def checked(command, label, env=None, seconds=180):
    result = execute(command, label, env, seconds)
    if not result["ok"]:
        raise RuntimeError(f"{label}: {result['failure']}\n{result['text'][-6000:]}")
    print(label, "passed", flush=True)
    return result


def environment():
    env = dict(os.environ, TARO_WORKERS="1", GOMAXPROCS="1")
    for name in [
        "TARO_GC_STRESS",
        "TARO_GC_TRACE",
        "TARO_GC_PERCENT",
        "TARO_GC_MEMORY_LIMIT",
        "TARO_RUNTIME_STATS",
        "TARO_RUNTIME_TRACE",
        "GOGC",
        "GOMEMLIMIT",
        "GODEBUG",
    ]:
        env.pop(name, None)
    return env


def prepare():
    manifest = json.loads((HERE / "fixtures.json").read_text())
    (OUT / "inputs").mkdir(parents=True, exist_ok=True)
    for item in manifest["files"] + [manifest["license_file"]]:
        dest = OUT / "inputs" / Path(item["path"]).name
        if not dest.exists():
            url = (
                manifest["repository"].replace(
                    "github.com", "raw.githubusercontent.com"
                )
                + "/"
                + manifest["revision"]
                + "/"
                + item["path"]
            )
            req = urllib.request.Request(
                url, headers={"User-Agent": "Taro JSON corpus benchmark"}
            )
            temp = dest.with_suffix(".part")
            size = 0
            with urllib.request.urlopen(req, timeout=30) as response, temp.open(
                "wb"
            ) as output:
                while block := response.read(1024 * 1024):
                    size += len(block)
                    if size > item["bytes"]:
                        raise RuntimeError("download exceeds pinned size")
                    output.write(block)
            temp.replace(dest)
        data = dest.read_bytes()
        if (
            len(data) != item["bytes"]
            or hashlib.sha256(data).hexdigest() != item["sha256"]
        ):
            raise RuntimeError(f"fixture identity changed: {dest}")
    checked([sys.executable, HERE / "oracle.py", OUT], "oracle", seconds=180)


def record_toolchain():
    """Keep host/toolchain provenance local beside the binary identities."""
    versions = {}
    for name, argv in {
        "go": ["go", "version"],
        "rust": ["rustc", "--version"],
        "swift": ["swiftc", "--version"],
        "os": ["sw_vers"],
        "cpu": ["sysctl", "-n", "machdep.cpu.brand_string"],
        "source_revision": ["git", "rev-parse", "HEAD"],
    }.items():
        versions[name] = subprocess.check_output(
            argv, text=True, stderr=subprocess.STDOUT, cwd=ROOT
        ).strip()
    versions["cpu_count"] = os.cpu_count()
    artifacts = [
        ROOT / "dist/bin/taro",
        ROOT / "dist/lib/taro/runtime/libtaro_runtime.a",
    ]
    artifacts += sorted((ROOT / "dist/lib/taro/std").glob("*/std.o"))
    versions["sdk"] = {
        str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in artifacts
    }
    save(OUT / "toolchain.json", versions)


def build():
    env = environment()
    checked(["go", "build", "-o", OUT / "go", HERE / "main.go"], "build-go", env)
    rust_env = dict(env, CARGO_BUILD_JOBS="1", RUSTFLAGS="-C debuginfo=1")
    target = ROOT / "target/json-diagnosis/rust-build"
    args = [
        "cargo",
        "build",
        "--offline",
        "--locked",
        "--release",
        "--manifest-path",
        HERE / "Cargo.toml",
        "--target-dir",
        target,
    ]
    checked(args, "build-rust", rust_env)
    shutil.copyfile(target / "release/json-corpus-reference", OUT / "rust")
    (OUT / "rust").chmod(0o755)
    checked(args + ["--features", "allocation-audit"], "build-rust-audit", rust_env)
    shutil.copyfile(target / "release/json-corpus-reference", OUT / "rust-audit")
    (OUT / "rust-audit").chmod(0o755)
    checked(
        [
            "swiftc",
            "-O",
            "-whole-module-optimization",
            "-swift-version",
            "6",
            "-module-cache-path",
            OUT / "swift-cache",
            HERE / "main.swift",
            "-o",
            OUT / "swift",
        ],
        "build-swift",
        env,
    )
    build_taro()


def build_taro():
    record_toolchain()
    env = environment()
    # Build benchmark overlays in a disposable SDK, never the installed dist.
    with tempfile.TemporaryDirectory(prefix="sdk-", dir=OUT) as directory:
        stage = Path(directory)
        sdk = stage / "sdk"
        std = stage / "std"
        shutil.copytree(ROOT / "dist", sdk, symlinks=True)
        (sdk / "std").unlink()
        shutil.copytree(ROOT / "std", std, ignore=shutil.ignore_patterns("target"))
        (sdk / "std").symlink_to(std)
        boot = stage / "boot.tr"
        boot.write_text("func main() {}\n")
        child_env = dict(env, TARO_HOME=str(sdk))
        checked(
            [sdk / "bin/taro", "check", boot, "--std-path", std, "--build-std"],
            "build-std",
            child_env,
        )
        checked(
            [
                sdk / "bin/taro",
                "build",
                HERE / "taro.tr",
                "--std-path",
                std,
                "--release",
                "-O3",
                "-o",
                OUT / "taro",
            ],
            "build-taro",
            child_env,
        )
    save(
        OUT / "identities.json",
        {
            n: hashlib.sha256((OUT / n).read_bytes()).hexdigest()
            for n in ["taro", "go", "swift", "rust", "rust-audit"]
        },
    )


def fields(line):
    return {
        k: (float(v) if k == "float_sum" else int(v) if v.isdecimal() else v)
        for k, v in re.findall(r"([a-z][a-z0-9_]*)=([^\s]+)", line)
    }


def identity():
    data = json.loads((OUT / "identities.json").read_text())
    for n, h in data.items():
        if hashlib.sha256((OUT / n).read_bytes()).hexdigest() != h:
            raise RuntimeError("binary changed: " + n)
    return data


def cases():
    names = [
        x["name"] for x in json.loads((HERE / "fixtures.json").read_text())["files"]
    ]
    result = [
        dict(language=l, mode="dom", dataset=n)
        for n in names
        for l in ["taro", "swift", "rust", "go"]
    ]
    for language in ["taro", "swift", "rust", "go"]:
        for mode in (
            ["typed", "typed-validated"]
            if language == "taro"
            else ["typed"]
        ):
            result.append(dict(language=language, mode=mode, dataset="canada"))
    return result


def key(case):
    return "/".join(case[k] for k in ["language", "mode", "dataset"])


def command(case, action, count=1, samples=1, binary=None):
    args = [
        OUT / (binary or case["language"]),
        action,
        case["mode"],
        OUT / "inputs" / (case["dataset"] + ".json"),
        str(count),
        str(samples),
    ]
    if case["language"] == "taro":
        args.append(str(expected(case).get("float_sum", 0)))
    return args


def expected(case):
    oracle = json.loads((OUT / "oracle.json").read_text())[case["dataset"]]
    return oracle if is_dom(case) else oracle["typed"]


def verify(case, text):
    prefix = "shape " if is_dom(case) else "typed "
    lines = [l for l in text.splitlines() if l.startswith(prefix)]
    if len(lines) != 1:
        raise RuntimeError("missing validation protocol: " + key(case))
    actual = fields(lines[0])
    want = expected(case)
    if "float_sum_checked" in actual:
        if actual.pop("float_sum_checked") != 1:
            raise RuntimeError("numeric checksum not checked")
        actual["float_sum"] = want["float_sum"]
    for field in actual:
        if field == "float_sum":
            if not math.isclose(
                actual[field], want[field], rel_tol=1e-11, abs_tol=1e-5
            ):
                raise RuntimeError(
                    f"numeric checksum mismatch: {actual[field]} != {want[field]}"
                )
        elif actual[field] != want[field]:
            raise RuntimeError(f"{key(case)} {field}: {actual[field]} != {want[field]}")
    required = (
        {
            "objects",
            "arrays",
            "strings",
            "numbers",
            "booleans",
            "nulls",
            "utf8_bytes",
            "depth",
            "top",
        }
        if is_dom(case)
        else {"features", "rings", "points", "coordinates", "float_sum"}
    )
    if set(actual) != required:
        raise RuntimeError("incomplete validation protocol")
    return actual


def check():
    path = OUT / "checks.json"
    ids = identity()
    report = (
        json.loads(path.read_text()) if path.exists() else dict(identities=ids, rows=[])
    )
    if report["identities"] != ids:
        old = report["identities"]
        report["rows"] = [
            r
            for r in report["rows"]
            if old.get(r["case"]["language"]) == ids[r["case"]["language"]]
        ]
        report["identities"] = ids
        save(path, report)
    for case in cases():
        if any(key(r["case"]) == key(case) for r in report["rows"]):
            continue
        label = "check-" + key(case).replace("/", "-")
        result = execute(command(case, "check"), label, environment(), timed=True)
        if result["ok"]:
            try:
                result["shape"] = verify(case, result["text"])
            except Exception as e:
                result.update(ok=False, failure=str(e))
        report["rows"].append(dict(case=case, **result))
        save(path, report)
        print(
            key(case),
            "validated" if result["ok"] else result["failure"],
            "peakMiB",
            round(result["peak_rss_bytes"] / 1024**2, 1),
            flush=True,
        )


def accepted():
    report = json.loads((OUT / "checks.json").read_text())
    if report["identities"] != identity():
        raise RuntimeError("stale checks")
    return [r["case"] for r in report["rows"] if r["ok"]]


def parse_run(case, text, count, samples):
    rows = [fields(l) for l in text.splitlines() if l.startswith("sample ")]
    if len(rows) != samples:
        raise RuntimeError("incomplete timing protocol")
    checksum = expected(case)["top" if is_dom(case) else "features"] * count
    if any(
        r["ops"] != count or r["checksum"] != checksum or r["ns"] <= 0 for r in rows
    ):
        raise RuntimeError("timing checksum mismatch")
    stats = [fields(l) for l in text.splitlines() if l.startswith("stats ")]
    if len(stats) != 1 or stats[0]["ops"] != count * samples:
        raise RuntimeError("incomplete stats protocol")
    return dict(samples_ns_per_op=[r["ns"] / count for r in rows], stats=stats[0])


def calibrate():
    ids = identity()
    path = OUT / "calibration.json"
    r = json.loads(path.read_text()) if path.exists() else dict(identities=ids, rows=[])
    if r["identities"] != ids:
        raise RuntimeError("stale calibration")
    for case in accepted():
        if any(key(x["case"]) == key(case) for x in r["rows"]):
            continue
        result = execute(
            command(case, "run"),
            "calibrate-" + key(case).replace("/", "-"),
            environment(),
            timed=True,
        )
        if result["ok"]:
            data = parse_run(case, result["text"], 1, 1)
            ns = data["samples_ns_per_op"][0]
            result.update(data=data, count=max(1, min(128, int(100_000_000 / ns))))
        r["rows"].append(dict(case=case, **result))
        save(path, r)
        print(
            "calibrated", key(case), result.get("count"), result["failure"], flush=True
        )


def measure():
    ids = identity()
    path = OUT / "timings.json"
    r = (
        json.loads(path.read_text())
        if path.exists()
        else dict(identities=ids, rows=[], rejected=[], observations=[])
    )
    if r["identities"] != ids:
        raise RuntimeError("stale timing binaries")
    calibration = json.loads((OUT / "calibration.json").read_text())
    assert calibration["identities"] == ids
    selected = {key(x["case"]): x for x in calibration["rows"] if x["ok"]}
    for _ in range(3):
        value = compare.observation()
        r["observations"].append(value)
        save(path, r)
        if not compare.quiet(value):
            print("busy; saved progress", flush=True)
            return
        time.sleep(5)
    # Rotate languages per dataset, then rotate Taro's three typed modes.
    languages = ["taro", "swift", "rust", "go"]
    all_cases = accepted()
    for ri in range(3):
        order = languages[ri:] + languages[:ri]
        for dataset in dict.fromkeys(c["dataset"] for c in all_cases):
            for phase in ["dom", "typed"]:
                for language in order:
                    group = [
                        c
                        for c in all_cases
                        if c["dataset"] == dataset
                        and c["language"] == language
                        and is_dom(c) == (phase == "dom")
                    ]
                    if group:
                        group = group[ri % len(group) :] + group[: ri % len(group)]
                    for case in group:
                        if key(case) not in selected or any(
                            x["round"] == ri and key(x["case"]) == key(case)
                            for x in r["rows"]
                        ):
                            continue
                        before = compare.observation()
                        if not compare.quiet(before):
                            r["observations"].append(before)
                            save(path, r)
                            print("busy; saved progress", flush=True)
                            return
                        count = selected[key(case)]["count"]
                        result = execute(
                            command(case, "run", count, 5),
                            f"round{ri}-" + key(case).replace("/", "-"),
                            environment(),
                            timed=True,
                        )
                        if result["ok"]:
                            result["data"] = parse_run(case, result["text"], count, 5)
                        after = compare.observation()
                        row = dict(
                            round=ri, case=case, before=before, after=after, **result
                        )
                        r["rows" if compare.quiet(after) else "rejected"].append(row)
                        save(path, r)
                        if not compare.quiet(after):
                            print("busy after run; rejected and saved", flush=True)
                            return
                        print(
                            ri,
                            key(case),
                            (
                                round(
                                    statistics.median(
                                        result["data"]["samples_ns_per_op"]
                                    )
                                    / 1e6,
                                    3,
                                )
                                if result["ok"]
                                else result["failure"]
                            ),
                            flush=True,
                        )
    r["complete"] = True
    save(path, r)


def audit():
    ids = identity()
    path = OUT / "audit.json"
    r = json.loads(path.read_text()) if path.exists() else dict(identities=ids, rows=[])
    if r["identities"] != ids:
        raise RuntimeError("stale audits")
    for case in accepted():
        if case["language"] == "swift":
            continue
        for count in [1, 2]:
            if any(
                key(x["case"]) == key(case) and x["count"] == count for x in r["rows"]
            ):
                continue
            env = environment()
            if case["language"] == "taro":
                env["TARO_RUNTIME_STATS"] = "1"
            result = execute(
                command(
                    case,
                    "audit",
                    count,
                    1,
                    "rust-audit" if case["language"] == "rust" else None,
                ),
                "audit-" + key(case).replace("/", "-") + f"-{count}",
                env,
                timed=True,
            )
            if result["ok"]:
                stats = next(
                    (
                        fields(l)
                        for l in result["text"].splitlines()
                        if l.startswith("stats ")
                    ),
                    None,
                )
                if not stats or stats["ops"] != count:
                    raise RuntimeError("bad audit protocol")
                result["stats"] = stats
                if case["language"] == "taro":
                    line = next(
                        l.strip()
                        for l in result["text"].splitlines()
                        if l.strip().startswith("gc collections=")
                    )
                    result["process_stats"] = fields(line)
            r["rows"].append(dict(case=case, count=count, **result))
            save(path, r)
            print("audit", key(case), count, result["failure"] or "passed", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "action",
        choices=[
            "prepare",
            "build",
            "build_taro",
            "check",
            "calibrate",
            "measure",
            "audit",
        ],
    )
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    if subprocess.run(
        ["git", "check-ignore", "-q", str(OUT / "report.json")], cwd=ROOT
    ).returncode:
        raise RuntimeError("generated output must be ignored")
    globals()[args.action]()
