#!/usr/bin/env python3
"""Stress prebuilt HTTP servers the way framework benchmarks do, plus realistic cases.

See README.md. Results go to an ignored directory; a server that loses connections
or stops answering is reported as a result rather than treated as a harness failure.
"""
import argparse
import json
import os
from pathlib import Path
import selectors
import socket
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
PORT = 18080

# JSON and plaintext levels and the pipeline depth follow TechEmpower's tests.
SCENARIOS = {
    "json": [("/json", c, 1, False) for c in (16, 32, 64, 128, 256, 512)],
    "plaintext": [("/text", c, 16, False) for c in (256, 1024, 4096, 16000)],
    "app": [("/app", c, 1, False) for c in (64, 256, 1024)],
    "churn": [("/json", 64, 1, True)],
}


def commands(language, artifacts, taro):
    return {
        "taro": [taro, str(PORT)],
        "rust": [artifacts / "rust/target/release/http-comparison", str(PORT)],
        "go": [artifacts / "go-server", str(PORT)],
        "node": [artifacts / "node-runtime", HERE / "servers/node/server.mjs", str(PORT)],
    }[language]


class Server:
    def __init__(self, language, args):
        env = dict(os.environ, TARO_WORKERS=str(args.workers), GOMAXPROCS=str(args.workers),
                   BENCH_WORKERS=str(args.workers), BENCH_HOST=args.bind)
        if args.max_connections:
            env["BENCH_MAX_CONNECTIONS"] = str(args.max_connections)
        command = [str(part) for part in commands(language, args.artifacts, args.taro)]
        with args.out.with_name(f"{language}-server.log").open("a") as log:
            self.process = subprocess.Popen(command, env=env, stdout=log, stderr=log)
        deadline = time.monotonic() + 15
        while True:
            try:
                socket.create_connection(("127.0.0.1", PORT), timeout=.2).close()
                return
            except OSError:
                if self.process.poll() is not None or time.monotonic() > deadline:
                    raise RuntimeError(f"{language} did not start")
                time.sleep(.05)

    def usage(self):
        """Resident KiB and CPU seconds, or None once the process has gone."""
        result = subprocess.run(["ps", "-o", "rss=,time=", "-p", str(self.process.pid)], capture_output=True, text=True)
        fields = result.stdout.split()
        if len(fields) != 2:
            return None
        seconds = 0.0
        for part in fields[1].replace("-", ":").split(":"):
            seconds = seconds * 60 + float(part)
        return int(fields[0]), seconds

    def close(self):
        if self.process.poll() is None:
            self.process.kill()
        self.process.wait()


def start(language, args):
    """Start a server, allowing macOS time to recover network buffers after a heavy level."""
    for attempt in range(6):
        try:
            return Server(language, args)
        except RuntimeError:
            if attempt == 5:
                raise
            time.sleep(10)


def settle():
    """Wait for the client's closed ports, so one level can't starve the next of them."""
    deadline = time.monotonic() + 70
    while time.monotonic() < deadline:
        lines = subprocess.run(["netstat", "-an", "-p", "tcp"] if sys.platform == "darwin" else ["ss", "-tan"],
                               capture_output=True, text=True).stdout.splitlines()
        if sum("TIME" in line for line in lines) < 2000:
            return
        time.sleep(2)


def wrk(args, path, connections, depth, close, seconds):
    command = [str(args.artifacts / "wrk/wrk"), f"-t{min(connections, args.client_threads)}", f"-c{connections}",
               f"-d{seconds}s", "--timeout", "8", "--latency", "-s", str(HERE / "stress.lua"),
               "-H", "Connection: close" if close else "Connection: keep-alive",
               f"http://{args.host}:{PORT}{path}"]
    try:
        result = subprocess.run(command, env=dict(os.environ, STRESS_DEPTH=str(depth)), capture_output=True,
                                text=True, timeout=seconds + 60)
    except subprocess.TimeoutExpired:
        return {"requests": 0, "failed": "client timed out"}
    for line in result.stdout.splitlines():
        if line.startswith('{"requests"'):
            data = json.loads(line)
            data["rps"] = round(data["requests"] / (data["duration_us"] / 1e6))
            return data
    return {"requests": 0, "failed": (result.stderr or result.stdout)[-200:].strip()}


def measure(server, args, name, path, connections, depth, close, seconds):
    before = server.usage()
    data = wrk(args, path, connections, depth, close, seconds)
    after = server.usage()
    data.update(scenario=name, connections=connections, depth=depth)
    if before is None or after is None:
        data["crashed"] = True
    else:
        data.update(rss_mib=round(after[0] / 1024, 1), cores=round((after[1] - before[1]) / seconds, 2))
        if data["requests"]:
            data["cpu_us"] = round((after[1] - before[1]) * 1e6 / data["requests"], 1)
    return data


class IdleConnections:
    """Connections that do nothing, as a server's slow or quiet clients do."""

    def __init__(self, host, count):
        self.sockets = []
        selector = selectors.DefaultSelector()
        # Each batch fits the 128-entry accept queue macOS gives every server.
        for start in range(0, count, 100):
            pending = 0
            for _ in range(min(100, count - start)):
                sock = socket.socket()
                sock.setblocking(False)
                sock.connect_ex((host, PORT))
                selector.register(sock, selectors.EVENT_WRITE)
                pending += 1
            deadline = time.monotonic() + 5
            while pending and time.monotonic() < deadline:
                for key, _ in selector.select(.2):
                    selector.unregister(key.fileobj)
                    if key.fileobj.getsockopt(socket.SOL_SOCKET, socket.SO_ERROR) == 0:
                        self.sockets.append(key.fileobj)
                    else:
                        key.fileobj.close()
                    pending -= 1
            for key in list(selector.get_map().values()):
                selector.unregister(key.fileobj)
                key.fileobj.close()
        selector.close()

    def answered(self, seconds=15):
        """Send one request down every connection; count the ones answered."""
        selector = selectors.DefaultSelector()
        message = b"GET /json HTTP/1.1\r\nHost: x\r\n\r\n"
        for sock in self.sockets:
            try:
                sock.send(message)
                selector.register(sock, selectors.EVENT_READ)
            except OSError:
                pass
        answered = 0
        deadline = time.monotonic() + seconds
        while selector.get_map() and time.monotonic() < deadline:
            for key, _ in selector.select(.2):
                selector.unregister(key.fileobj)
                try:
                    answered += key.fileobj.recv(4096).startswith(b"HTTP/1.1 200")
                except OSError:
                    pass
        selector.close()
        return answered

    def close(self):
        for sock in self.sockets:
            sock.close()


def idle_case(server, args, seconds):
    settled = server.usage()
    idle = IdleConnections(args.host, args.idle)
    time.sleep(1)
    loaded = server.usage()
    data = measure(server, args, "idle", "/json", 32, 1, False, seconds)
    data.update(idle_open=len(idle.sockets), idle_answered=idle.answered())
    if settled and loaded and idle.sockets:
        data["kib_per_idle"] = round((loaded[0] - settled[0]) / len(idle.sockets), 1)
    idle.close()
    return data


def soak(server, args, emit):
    """Short rounds, so a slow decline or memory growth shows up as a trend."""
    settle()
    for round_number in range(args.soak_rounds):
        data = measure(server, args, "soak", "/app", 256, 1, False, 30)
        if data.get("failed"):
            raise RuntimeError(f"soak could not run: {data['failed']}")
        data["round"] = round_number
        emit(data)
        if data.get("crashed"):
            return


def line(language, data):
    if data.get("failed") and not data["requests"]:
        return f"{language:5} {data['scenario']:9} failed: {data['failed'][:90]}"
    errors = sum(data.get(key, 0) for key in ("connect_errors", "read_errors", "write_errors", "status_errors", "timeouts"))
    extra = "".join(f" {key} {data[key]}" for key in ("idle_open", "idle_answered", "kib_per_idle", "round", "crashed") if key in data)
    return (f"{language:5} {data['scenario']:9} c{data['connections']:<6} d{data['depth']:<3}"
            f"rps {data.get('rps', 0):>8} p50 {data.get('p50_us', 0):>8} p99 {data.get('p99_us', 0):>9} "
            f"err {errors:<7} rss {data.get('rss_mib', 0):>7} cores {data.get('cores', 0):>5}{extra}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, default=ROOT / "target/http-compare/references")
    parser.add_argument("--taro", type=Path, default=ROOT / "target/http-stress/taro-server")
    parser.add_argument("--languages", default="taro,rust,go,node")
    parser.add_argument("--scenarios", default="json,plaintext,app,churn,idle")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--client-threads", type=int, default=4)
    parser.add_argument("--seconds", type=int, default=8)
    parser.add_argument("--idle", type=int, default=10000)
    parser.add_argument("--soak-rounds", type=int, default=10)
    parser.add_argument("--max-connections", type=int, default=0, help="a limit for Taro; 0 keeps its default of none")
    parser.add_argument("--host", default="127.0.0.1", help="address the load generator connects to")
    parser.add_argument("--bind", default="127.0.0.1", help="address the server listens on")
    parser.add_argument("--out", type=Path, default=ROOT / "target/http-stress/results.jsonl")
    args = parser.parse_args()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("a") as results:
        for language in args.languages.split(","):
            def emit(data):
                results.write(json.dumps(dict(data, language=language)) + "\n")
                results.flush()
                print(line(language, data), flush=True)
            server = start(language, args)
            try:
                wrk(args, "/json", 8, 1, False, 3)
                for scenario in args.scenarios.split(","):
                    if scenario == "idle":
                        emit(idle_case(server, args, args.seconds))
                        settle()
                    elif scenario == "soak":
                        soak(server, args, emit)
                    else:
                        for path, connections, depth, close in SCENARIOS[scenario]:
                            emit(measure(server, args, scenario, path, connections, depth, close, args.seconds))
                            if server.process.poll() is not None:
                                emit({"requests": 0, "failed": f"server exited {server.process.returncode}",
                                      "scenario": scenario, "connections": connections, "depth": depth})
                                server.close()
                                server = start(language, args)
                            settle() if connections >= 1024 or close else time.sleep(2)
            finally:
                server.close()
            settle()


if __name__ == "__main__":
    main()
