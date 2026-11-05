#!/usr/bin/env python3
"""Compare prebuilt HTTP servers on macOS; generated output stays ignored.

See README.md for build commands, framework choices and measurement limits.
This uses wrk, not a Python request loop, for the timed load.
"""
import argparse
import concurrent.futures
import hashlib
import http.client
import json
import os
from pathlib import Path
import re
import signal
import socket
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE.parent / "json/corpus"))
import run as bounded

LANGUAGES = ["taro", "python", "go", "rust", "swift", "node", "bun"]
TARO_VARIANTS = ["taro-before", "taro-metadata", "taro-runtime"]
PAYLOADS = {"text": b"Hello, World!", "json": b'{"message":"Hello, World!"}', "json-static": b'{"message":"Hello, World!"}'}

def save(path, value):
    temporary = path.with_suffix(".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)

def process_rows():
    return [tuple(map(int, line.split())) for line in subprocess.check_output(["ps", "-axo", "pid=,ppid=,rss="], text=True).splitlines()]

def descendants(root, rows):
    ids = {root}
    while True:
        expanded = ids | {pid for pid, parent, _ in rows if parent in ids}
        if expanded == ids:
            return ids
        ids = expanded

def usage(helper, pid):
    try:
        return json.loads(subprocess.check_output([helper, str(pid)], text=True, stderr=subprocess.DEVNULL))
    except subprocess.CalledProcessError:
        return None

def tree_usage(helper, pid):
    values = [usage(helper, child) for child in descendants(pid, process_rows())]
    if not any(values):
        raise RuntimeError("server process counters unavailable")
    return {key: sum(value[key] for value in values if value) for key in ["user_ns", "system_ns", "instructions", "cycles", "rss", "footprint", "peak_footprint"]}

def request(port, endpoint):
    connection = http.client.HTTPConnection("127.0.0.1", port, timeout=10)
    try:
        connection.request("GET", "/" + endpoint)
        response = connection.getresponse()
        body = response.read()
        assert response.status == 200, (endpoint, response.status)
        if endpoint == "stats":
            return json.loads(body)
        assert body == PAYLOADS[endpoint], (endpoint, body[:100])
        expected = "text/plain" if endpoint == "text" else "application/json"
        assert response.getheader("Content-Type", "").split(";")[0] == expected
        assert not response.will_close, "all timed peers must permit keep-alive"
        # Verify a second exchange over the same physical connection.
        local = connection.sock.getsockname()
        connection.request("GET", "/" + endpoint)
        again = connection.getresponse()
        assert again.status == 200 and again.read() == PAYLOADS[endpoint]
        assert connection.sock.getsockname() == local
        return hashlib.sha256(body).hexdigest()
    finally:
        connection.close()

class Server:
    def __init__(self, language, artifacts, logs, workers, stress=False, diagnostic_seconds=None):
        self.language = language
        probe = socket.socket()
        probe.bind(("127.0.0.1", 0))
        self.port = probe.getsockname()[1]
        probe.close()
        env = bounded.environment()
        env.update(TARO_WORKERS=str(workers), GOMAXPROCS=str(workers), BENCH_WORKERS=str(workers), LOG_LEVEL="error")
        if stress:
            env["TARO_GC_STRESS"] = "1"
        if diagnostic_seconds is not None:
            assert language in ["taro", "taro-metadata"] and 1 <= diagnostic_seconds <= 30
            env["TARO_RUNTIME_STATS"] = "1"
        commands = {
            "taro": [artifacts.parent / "taro-server", str(self.port)],
            "taro-before": [artifacts.parent / "taro-before", str(self.port)],
            "taro-metadata": [artifacts.parent / "taro-metadata", str(self.port)],
            "taro-runtime": [artifacts.parent / "taro-runtime", str(self.port)],
            "go": [artifacts / "go-server", str(self.port)],
            "rust": [artifacts / "rust/target/release/http-comparison", str(self.port)],
            "swift": [artifacts / "swift/.build/release/Server", str(self.port)],
            "node": [artifacts / "node-runtime", artifacts / "node/server.mjs", str(self.port)],
            "bun": [artifacts / "bun-runtime", artifacts / "bun/server.js", str(self.port)],
            "python": [artifacts / "venv/bin/python", "-m", "uvicorn", "server:app", "--app-dir", artifacts / "python", "--host", "127.0.0.1", "--port", str(self.port), "--workers", str(workers), "--loop", "uvloop", "--http", "httptools", "--no-access-log", "--log-level", "warning", "--timeout-keep-alive", "30"],
        }
        self.command = list(map(str, commands[language]))
        if diagnostic_seconds is not None:
            self.command.append(str(diagnostic_seconds))
        self.log = logs.open("w")
        self.process = subprocess.Popen(self.command, env=env, stdout=self.log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            deadline = time.monotonic() + 15
            while True:
                if self.process.poll() is not None:
                    raise RuntimeError(f"{language} exited: {logs.read_text()[-3000:]}")
                try:
                    with socket.create_connection(("127.0.0.1", self.port), timeout=.1):
                        break
                except OSError:
                    if time.monotonic() >= deadline:
                        raise RuntimeError(f"{language} startup timeout")
                    time.sleep(.05)
        except BaseException:
            self.close()
            raise

    def close(self):
        if self.process.poll() is None:
            os.killpg(self.process.pid, signal.SIGTERM)
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(self.process.pid, signal.SIGKILL)
                self.process.wait()
        self.log.close()

def load(server, artifacts, out, endpoint, connections, seconds, label):
    path = out / (label + ".log")
    command = ["/usr/bin/time", "-l", artifacts / "wrk/wrk", "-t" + str(min(4, connections)), "-c" + str(connections), "-d" + str(seconds) + "s", "--timeout", "5s", "--latency", "-s", HERE / "report.lua", f"http://127.0.0.1:{server.port}/{endpoint}"]
    helper = str(artifacts / "process-usage")
    before = tree_usage(helper, server.process.pid)
    started = time.monotonic()
    peak = before["rss"]
    with path.open("w") as log:
        process = subprocess.Popen(list(map(str, command)), stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while process.poll() is None:
                rows = process_rows()
                server_ids = descendants(server.process.pid, rows)
                all_ids = server_ids | descendants(process.pid, rows)
                rss = sum(rss * 1024 for pid, _, rss in rows if pid in all_ids)
                peak = max(peak, sum(rss * 1024 for pid, _, rss in rows if pid in server_ids))
                if rss > 4 * 1024**3 or time.monotonic() - started > seconds + 15:
                    raise RuntimeError("HTTP load exceeded 4 GiB or wall-time guard")
                if server.process.poll() is not None:
                    raise RuntimeError("server exited during load")
                time.sleep(.2)
            if process.returncode:
                raise RuntimeError(path.read_text()[-2500:])
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
    after = tree_usage(helper, server.process.pid)
    text = path.read_text()
    data = json.loads(next(line for line in text.splitlines() if line.startswith('{"requests"')))
    assert data["requests"] > 0
    assert not any(data[name] for name in ["connect_errors", "read_errors", "write_errors", "status_errors", "timeouts"]), data
    cpu = re.search(r"([\d.]+) real\s+([\d.]+) user\s+([\d.]+) sys", text)
    client_cpu = float(cpu[2]) + float(cpu[3]) if cpu else None
    elapsed = data["duration_us"] / 1e6
    data.update(requests_per_second=data["requests"] / elapsed,
                server_cpu_seconds=sum(after[key] - before[key] for key in ["user_ns", "system_ns"]) / 1e9,
                server_instructions=after["instructions"] - before["instructions"],
                server_cycles=after["cycles"] - before["cycles"],
                peak_server_rss=peak, lifetime_peak_footprint=after["peak_footprint"],
                client_cpu_seconds=client_cpu,
                potential_client_limit=client_cpu is not None and client_cpu / elapsed >= min(4, connections) * .9)
    return data

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, default=ROOT / "target/crypto-http/references")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--rounds", type=int, default=3)
    parser.add_argument("--seconds", type=int, default=5)
    parser.add_argument("--warmup-seconds", type=int, default=5)
    parser.add_argument("--languages", default=",".join(LANGUAGES))
    parser.add_argument("--connections", default="1,32")
    parser.add_argument("--endpoints", default=",".join(PAYLOADS))
    parser.add_argument("--preflight-only", action="store_true")
    parser.add_argument("--gc-stress", action="store_true")
    args = parser.parse_args()
    assert sys.platform == "darwin", "process counters currently target macOS"
    assert 1 <= args.workers <= 8 and 1 <= args.rounds <= 10 and 1 <= args.seconds <= 30
    assert 1 <= args.warmup_seconds <= 30
    languages = args.languages.split(",")
    assert all(language in LANGUAGES + TARO_VARIANTS for language in languages)
    assert args.workers == 1 or not any(language in ["node", "bun"] for language in languages), "JS references run one process/event loop"
    connections = list(map(int, args.connections.split(",")))
    assert all(1 <= count <= 128 for count in connections)
    endpoints = args.endpoints.split(",")
    assert endpoints and all(endpoint in PAYLOADS for endpoint in endpoints)
    artifacts = args.artifacts.resolve()
    out = artifacts / "results"
    subprocess.run(["git", "check-ignore", "-q", str(out / "report.json")], cwd=ROOT, check=True)
    out.mkdir(exist_ok=True)
    helper = artifacts / "process-usage"
    assert helper.exists()
    report = {"config": vars(args) | {"artifacts": str(artifacts)}, "python_runtime": sys.version, "cpu_count": os.cpu_count(),
              "notes": "HTTP/1.1 loopback, keep-alive, no pipelining/TLS/compression. Worker settings limit Taro/Go/Tokio/Uvicorn; Swift limits NIO loops, not the separate Swift concurrency executor. CPU deltas are server process-tree counters; wrk CPU includes startup. GC counters for Go/Taro exclude differing runtime/native allocations and include tiny stats-query overhead.",
              "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in (HERE / "servers").rglob("*") if p.is_file()},
              "identities": json.loads((artifacts / "identities.json").read_text()) if (artifacts / "identities.json").exists() else {},
              "preflight": [], "quiet": [], "rows": []}
    previous = out / "report.json"
    if not args.preflight_only and previous.exists():
        saved = json.loads(previous.read_text())
        if saved.get("rows"):
            for key in ["workers", "rounds", "seconds", "warmup_seconds", "languages", "connections", "endpoints"]:
                assert saved["config"][key] == report["config"][key], "saved campaign configuration differs; use another artifacts directory"
            assert saved["identities"] == report["identities"] and saved["source_sha256"] == report["source_sha256"], "saved campaign artifacts differ"
            report["rows"] = saved["rows"]
            report["quiet"] = saved.get("quiet", [])
            report["preflight"] = saved.get("preflight", [])
    completed = {(row["language"], row["endpoint"], row["connections"], row["round"]) for row in report["rows"]}
    name = "preflight-stress.json" if args.gc_stress else "preflight.json"
    for language in languages:
        server = Server(language, artifacts, out / (language + "-preflight.log"), args.workers, args.gc_stress and language.startswith("taro"))
        try:
            for endpoint in endpoints:
                digest = request(server.port, endpoint)
                with concurrent.futures.ThreadPoolExecutor(max_workers=32) as pool:
                    list(pool.map(lambda _: request(server.port, endpoint), range(64)))
                report["preflight"].append({"language": language, "endpoint": endpoint, "sha256": digest})
            print(language, "payload/keep-alive/concurrency preflight passed", flush=True)
        finally:
            server.close()
    save(out / name, report)
    if args.preflight_only:
        return
    assert not args.gc_stress, "stress runs validate correctness; timings use default GC"
    for index in range(3):
        observed = bounded.compare.observation()
        report["quiet"].append(observed)
        save(out / "report.json", report)
        if not bounded.compare.quiet(observed):
            print("Timing deferred: system busy", flush=True)
            return
        if index < 2:
            time.sleep(30)
    for round_index in range(args.rounds):
        order = languages[round_index % len(languages):] + languages[:round_index % len(languages)]
        for endpoint in endpoints:
            for count in connections:
                for language in order:
                    if (language, endpoint, count, round_index) in completed:
                        continue
                    time.sleep(2)
                    observed = bounded.compare.observation()
                    # The trailing load average includes our earlier trials.
                    # Current idle must recover before starting the next one.
                    if observed["idle_pct"] < 70:
                        print("Timing paused; completed samples saved", flush=True)
                        return
                    label = f"{round_index}-{endpoint}-c{count}-{language}"
                    server = Server(language, artifacts, out / (label + "-server.log"), args.workers)
                    try:
                        request(server.port, endpoint)
                        load(server, artifacts, out, endpoint, count, args.warmup_seconds, label + "-warmup")
                        initial_gc = request(server.port, "stats") if language.startswith("taro") or language == "go" else None
                        data = load(server, artifacts, out, endpoint, count, args.seconds, label)
                        final_gc = request(server.port, "stats") if initial_gc else None
                        if initial_gc:
                            data["gc"] = {key: final_gc[key] - initial_gc[key] for key in initial_gc}
                        request(server.port, endpoint)
                        report["rows"].append({"language": language, "endpoint": endpoint, "connections": count, "round": round_index, "load": observed, **data})
                        save(out / "report.json", report)
                    finally:
                        server.close()
        print("round", round_index + 1, "complete", flush=True)
    print("HTTP framework comparison complete", flush=True)

if __name__ == "__main__":
    main()
