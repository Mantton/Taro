#!/usr/bin/env python3
"""Measure the packaged Taro editor path on Iris without changing its files."""

import argparse
from collections import Counter
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import select
import signal
import subprocess
import sys
import threading
import time

from lsp_reclamation import rss


TIME_LIMIT = 2.0
LOCAL_FUNCTION = "func encodeDouble"


class Client:
    def __init__(self, process):
        self.process = process
        self.buffer = bytearray()
        self.next_id = 1

    def send(self, method, params, request=False):
        header = {"jsonrpc": "2.0", "method": method, "params": params}
        if request:
            header["id"] = self.next_id
            self.next_id += 1
        self.write(header)
        return header.get("id")

    def write(self, message):
        body = json.dumps(message, separators=(",", ":")).encode()
        self.process.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode() + body)
        self.process.stdin.flush()

    def receive(self, deadline):
        pipe = self.process.stdout
        while True:
            header_end = self.buffer.find(b"\r\n\r\n")
            if header_end >= 0:
                header = self.buffer[:header_end].decode()
                content_length = next(
                    int(line.split(":", 1)[1])
                    for line in header.split("\r\n")
                    if line.lower().startswith("content-length:")
                )
                body_start = header_end + 4
                end = body_start + content_length
                if end <= len(self.buffer):
                    message = json.loads(self.buffer[body_start:end])
                    del self.buffer[:end]
                    if message.get("method") == "client/registerCapability":
                        self.write({"jsonrpc": "2.0", "id": message["id"], "result": None})
                        continue
                    return message
            remaining = deadline - time.perf_counter()
            if remaining <= 0 or not select.select([pipe], [], [], remaining)[0]:
                return None
            data = os.read(pipe.fileno(), 65536)
            if not data:
                raise EOFError("language server exited during the release trace")
            self.buffer.extend(data)


def latest_child(parent):
    output = subprocess.check_output(["ps", "-axo", "pid=,ppid="], text=True)
    children = [
        int(pid)
        for pid, ppid in (line.split() for line in output.splitlines() if line.strip())
        if int(ppid) == parent
    ]
    if len(children) != 1:
        raise RuntimeError(f"expected one worker process and found {children}")
    return children[0]


def initialize(client, workspace):
    started = time.perf_counter()
    request = client.send("initialize", {
        "capabilities": {"workspace": {"didChangeWatchedFiles": {"dynamicRegistration": True}}},
        "workspaceFolders": [{"uri": workspace.as_uri(), "name": "Iris"}],
    }, request=True)
    result = client.receive(started + 5)
    if result is None or result.get("id") != request or "result" not in result:
        raise RuntimeError(f"initialize did not succeed: {result}")
    client.send("initialized", {})


def wait_for_diagnostics(client, uri, version, started, timeout):
    while (message := client.receive(started + timeout)) is not None:
        if is_diagnostics(message, uri, version):
            if not clean_diagnostics(message):
                raise RuntimeError(f"unexpected Iris diagnostics: {message['params']}")
            return (time.perf_counter() - started) * 1000
    return None


def is_diagnostics(message, uri, version):
    return (
        message.get("method") == "textDocument/publishDiagnostics"
        and message["params"].get("uri") == uri
        and message["params"].get("version") == version
    )


def clean_diagnostics(message):
    # This Iris fixture checks cleanly. The trace only renames a local,
    # changes its indentation or adds a valid top-level function.
    return message["params"].get("diagnostics") == []


def text_for(source, tag, header=False):
    prefix, function = source.split(LOCAL_FUNCTION, 1)
    block, rest = function.split("\n}\n", 1)
    name = "magnitude" if tag is None else f"magnitudeEdit{tag}"
    block = re.sub(r"\bmagnitude\b", name, block)
    if tag is not None:
        declaration_indent = " " * (4 + tag % 5)
        block = block.replace(f"\n    var {name} =", f"\n{declaration_indent}var {name} =", 1)
    edited = prefix + LOCAL_FUNCTION + block + "\n}\n" + rest
    if header:
        edited += "\nfunc lspReleaseProbe() -> int32 { 1 }\n"
    lines = edited.splitlines()
    definition = next(index for index, line in enumerate(lines) if f"var {name} " in line)
    usage = next(index for index, line in enumerate(lines) if f"if {name} " in line)
    column = len(lines[usage].split(name, 1)[0].encode("utf-16-le")) // 2
    declaration_column = len(lines[definition].split(name, 1)[0].encode("utf-16-le")) // 2
    return edited, {"line": usage, "character": column}, {
        "start": {"line": definition, "character": declaration_column},
        "end": {"line": definition, "character": declaration_column + len(name)},
    }


def edit_and_query(
    client, uri, version, text, position, expected_range, timeout=TIME_LIMIT,
):
    started = time.perf_counter()
    if text is not None:
        client.send("textDocument/didChange", {
            "textDocument": {"uri": uri, "version": version},
            "contentChanges": [{"text": text}],
        })
    params = {"textDocument": {"uri": uri}, "position": position}
    hover = client.send("textDocument/hover", params, request=True)
    definition = client.send("textDocument/definition", params, request=True)
    arrivals = {}
    wrong = []
    errors = []
    expected = 2 if text is None else 3
    while len(arrivals) + len(errors) + len(wrong) < expected:
        message = client.receive(started + timeout)
        if message is None:
            break
        elapsed = (time.perf_counter() - started) * 1000
        if text is not None and is_diagnostics(message, uri, version):
            if clean_diagnostics(message):
                arrivals["diagnostics_ms"] = elapsed
            else:
                wrong.append({
                    "request": "diagnostics_ms",
                    "answer": message["params"].get("diagnostics"),
                })
            continue
        identifier = message.get("id")
        if identifier not in (hover, definition):
            continue
        name = "hover_ms" if identifier == hover else "definition_ms"
        if "error" in message:
            errors.append({"request": name, "error": message["error"]})
            continue
        result = message.get("result")
        if identifier == hover:
            correct = (result or {}).get("contents", {}).get("value") == "double"
        else:
            value = result or {}
            correct = (
                value.get("uri") == uri
                and value.get("range") == expected_range
            )
        if correct:
            arrivals[name] = elapsed
        else:
            wrong.append({"request": name, "answer": result})
    return {
        "version": version,
        "hover_ms": arrivals.get("hover_ms"),
        "definition_ms": arrivals.get("definition_ms"),
        "diagnostics_ms": arrivals.get("diagnostics_ms"),
        "incorrect": wrong,
        "errors": errors,
    }


def summarize(samples, field):
    times = [sample[field] for sample in samples]
    timely = sum(time_ms is not None and time_ms <= 1000 * TIME_LIMIT for time_ms in times)
    scored = sorted(time_ms if time_ms is not None else 1000 * TIME_LIMIT for time_ms in times)
    p95 = scored[math.ceil(len(scored) * 0.95) - 1]
    return {"samples": len(times), "timely": timely, "p95_ms": round(p95, 3)}


def resident_bytes(server, worker):
    return {"server_bytes": rss(server), "worker_bytes": rss(worker)}


def read_analysis_trace(pipe, uri, modes):
    for line in pipe:
        if match := re.fullmatch(rb"taro-lsp analysis (\d+) (Body|Package) (.*)\n", line):
            if match[3].decode() == uri:
                modes[int(match[1])] = match[2].decode()
        else:
            sys.stderr.buffer.write(line)


def run(args):
    workspace = args.iris.resolve()
    main = workspace / "src/main.tr"
    original = main.read_text()
    uri = main.as_uri()
    analysis_modes = {}
    with subprocess.Popen(
        [args.bin.resolve(), "--bundle", args.bundle.resolve()],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env={**os.environ, "TARO_LSP_TRACE_ANALYSIS": "1"},
    ) as process:
        client = Client(process)
        trace_reader = threading.Thread(
            target=read_analysis_trace, args=(process.stderr, uri, analysis_modes), daemon=True,
        )
        trace_reader.start()
        try:
            initialize(client, workspace)
            started = time.perf_counter()
            client.send("textDocument/didOpen", {
                "textDocument": {"uri": uri, "languageId": "taro", "version": 1, "text": original},
            })
            cold = wait_for_diagnostics(client, uri, 1, started, 35)
            if cold is None:
                raise TimeoutError("the cold workspace never published diagnostics")
            child = latest_child(process.pid)
            warmup = edit_and_query(client, uri, 2, *text_for(original, 0))
            samples = []
            quiescent = []
            for edit, version in enumerate(range(3, args.edits + 3), 1):
                restore = edit % 16 == 0 or edit == args.edits
                tag = None if restore else version
                samples.append(edit_and_query(client, uri, version, *text_for(original, tag)))
                if restore:
                    quiescent.append({"edit": edit, **resident_bytes(process.pid, child)})
                if args.progress_every and edit % args.progress_every == 0:
                    print(f"Iris warm edits completed {edit}/{args.edits}", file=sys.stderr, flush=True)
            last_version = args.edits + 3
            header = edit_and_query(client, uri, last_version, *text_for(original, 10_001, header=True))
            resident = resident_bytes(process.pid, child)
            if latest_child(process.pid) != child:
                raise AssertionError("worker changed during the normal edit trace")
            client.send("textDocument/didClose", {"textDocument": {"uri": uri}})
            reopen_start = time.perf_counter()
            client.send("textDocument/didOpen", {
                "textDocument": {
                    "uri": uri, "languageId": "taro", "version": last_version + 1, "text": original,
                },
            })
            reopen = wait_for_diagnostics(client, uri, last_version + 1, reopen_start, 35)
            recovery = []
            for attempt in range(args.recoveries):
                retiring = latest_child(process.pid)
                os.kill(retiring, signal.SIGKILL)
                recovery_version = last_version + 2 + attempt
                recovery_started = time.perf_counter()
                text, point, definition_range = text_for(original, 10_002 + attempt)
                recovery_request = edit_and_query(
                    client, uri, recovery_version, text, point, definition_range, timeout=35,
                )
                final = recovery_request
                if final["hover_ms"] is None or final["definition_ms"] is None:
                    final = edit_and_query(
                        client, uri, recovery_version, None, point, definition_range,
                        timeout=35,
                    )
                recovery.append({
                    "first_queries": recovery_request,
                    "current_queries": final,
                    "elapsed_ms": (time.perf_counter() - recovery_started) * 1000,
                    "worker_replaced": latest_child(process.pid) != retiring,
                })
            burst_started = time.perf_counter()
            burst_version = last_version + len(recovery) + 2
            for index in range(31):
                text, _, _ = text_for(original, 20_000 + index)
                client.send("textDocument/didChange", {
                    "textDocument": {"uri": uri, "version": burst_version + index},
                    "contentChanges": [{"text": text}],
                })
            burst = edit_and_query(
                client, uri, burst_version + 31, *text_for(original, 20_031),
            )
            burst["total_elapsed_ms"] = (time.perf_counter() - burst_started) * 1000
            warm = {field: summarize(samples, field) for field in ("hover_ms", "definition_ms", "diagnostics_ms")}
            incorrect = sum(len(sample["incorrect"]) for sample in samples)
            incorrect += sum(
                len(sample["incorrect"])
                for sample in [warmup, header, burst]
            )
            for attempt in recovery:
                first = attempt["first_queries"]
                final = attempt["current_queries"]
                incorrect += len(first["incorrect"])
                if final is not first:
                    incorrect += len(final["incorrect"])
            peak_rss = max(point["server_bytes"] + point["worker_bytes"] for point in quiescent)
            result = {
                "system": platform.platform(),
                "machine": platform.machine(),
                "workspace": str(workspace),
                "bundle_identity": (args.bundle / "bundle.toml").read_text(),
                "source_sha256": hashlib.sha256(original.encode()).hexdigest(),
                "cold_diagnostics_ms": cold,
                "warm_reopen_diagnostics_ms": reopen,
                "warmup": warmup,
                "warm": warm,
                "incorrect": incorrect,
                "resident": resident,
                "restored_revision_rss": quiescent,
                "header_edit": header,
                "recovery": recovery,
                "coalesced_burst": burst,
                "gates": {
                    "hover_and_definition_p95_under_200_ms": all(
                        warm[field]["p95_ms"] <= 200 for field in ("hover_ms", "definition_ms")
                    ),
                    "hover_and_definition_99_percent_within_2_seconds": all(
                        warm[field]["timely"] / len(samples) >= 0.99
                        for field in ("hover_ms", "definition_ms")
                    ),
                    "no_incorrect_answers": incorrect == 0,
                    "combined_sampled_rss_under_1_gib": peak_rss < 1024 ** 3,
                    "recovery_within_2_seconds": bool(recovery) and all(
                        attempt["worker_replaced"]
                        and attempt["first_queries"]["diagnostics_ms"] is not None
                        and attempt["current_queries"]["hover_ms"] is not None
                        and attempt["current_queries"]["definition_ms"] is not None
                        and attempt["elapsed_ms"] <= 2_000
                        for attempt in recovery
                    ),
                },
                "samples": samples,
            }
        finally:
            try:
                shutdown = client.send("shutdown", None, request=True)
                while (message := client.receive(time.perf_counter() + 2)) is not None:
                    if message.get("id") == shutdown:
                        break
                client.send("exit", None)
                process.wait(timeout=3)
            except (OSError, EOFError, subprocess.TimeoutExpired):
                process.kill()
                process.wait()
            trace_reader.join()
    result["warm_analysis_modes"] = dict(Counter(
        analysis_modes.get(sample["version"], "unobserved") for sample in samples
    ))
    result["gates"]["all_warm_iris_edits_used_body_checks"] = (
        result["warm_analysis_modes"] == {"Body": len(samples)}
    )
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bin", type=Path, required=True)
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--iris", type=Path, default=Path("showcase/adex_iris"))
    parser.add_argument("--edits", type=int, default=32)
    parser.add_argument("--recoveries", type=int, default=0)
    parser.add_argument("--progress-every", type=int, default=0)
    args = parser.parse_args()
    if args.edits < 1 or args.recoveries < 0 or args.progress_every < 0:
        parser.error("the release trace needs at least one edit and a nonnegative recovery count")
    print(json.dumps(run(args), indent=2))


if __name__ == "__main__":
    main()
