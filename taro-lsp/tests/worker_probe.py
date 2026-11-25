"""Pipe-driven child used by the Rust supervisor tests."""

import json
import struct
import sys
import time


def read():
    header = sys.stdin.buffer.read(4)
    if not header:
        return None
    length = struct.unpack(">I", header)[0]
    return json.loads(sys.stdin.buffer.read(length))["data"]


def send(reply):
    payload = json.dumps({"schema": 1, "data": reply}).encode()
    sys.stdout.buffer.write(struct.pack(">I", len(payload)) + payload)
    sys.stdout.buffer.flush()


documents = {}
while message := read():
    if "Cancel" in message:
        continue
    request = message["Analyze"]
    stamp = request["stamp"]
    inputs = request["inputs"]
    if "Reset" in inputs:
        documents = inputs["Reset"]["documents"]
    else:
        for path, text in inputs["Delta"].items():
            if text is None:
                documents.pop(path, None)
            else:
                documents[path] = text
    text = "\n".join(documents.values())
    if stamp["generation"] == 1:
        if "force crash" in text:
            sys.exit(17)
        if "force hang" in text:
            time.sleep(60)
        if "delay reply" in text:
            time.sleep(0.08)
    product = {
        "revision": stamp["revision"],
        "complete": True,
        "syntax_uncertainty": "None",
        "declarations": [],
        "bodies": [],
        "occurrences": [],
        "missing_members": [],
        "diagnostics": [{
            "source": None, "body_range": None, "level": "Info", "message": text,
            "code": None, "notes": [], "suggestion": None,
        }],
    }
    send({"Finished": {"stamp": stamp, "result": {"Ok": product}}})
