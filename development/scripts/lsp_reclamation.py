#!/usr/bin/env python3
"""Replay edits in the original Taro analysis worker and sample resident memory."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import select
import struct
import subprocess
import tempfile
import time


def read_exact(pipe, size, deadline):
    remaining = size
    chunks = []
    while remaining:
        timeout = deadline - time.monotonic()
        if timeout <= 0 or not select.select([pipe], [], [], timeout)[0]:
            raise TimeoutError("analysis worker did not reply before the deadline")
        chunk = os.read(pipe.fileno(), remaining)
        if not chunk:
            raise EOFError("analysis worker exited during editing")
        chunks.append(chunk)
        remaining -= len(chunk)
    return b"".join(chunks)


def analyze(worker, revision, inputs):
    stamp = {"generation": 1, "revision": revision}
    request = {"schema": 1, "data": {"Analyze": {"stamp": stamp, "inputs": inputs}}}
    payload = json.dumps(request, separators=(",", ":")).encode()
    worker.stdin.write(struct.pack(">I", len(payload)) + payload)
    worker.stdin.flush()
    deadline = time.monotonic() + 30
    size = struct.unpack(">I", read_exact(worker.stdout, 4, deadline))[0]
    if not 0 < size <= 128 * 1024 * 1024:
        raise ValueError(f"invalid reply size {size}")
    frame = json.loads(read_exact(worker.stdout, size, deadline))
    if frame["schema"] != 1:
        raise ValueError("analysis worker protocol version mismatch")
    result = frame["data"]["Finished"]
    if result["stamp"] != stamp:
        raise AssertionError(f"worker reply used an unexpected stamp {result['stamp']}")
    outcome = result["result"]
    if "Ok" not in outcome or not outcome["Ok"]["complete"]:
        raise AssertionError(f"analysis failed on revision {revision} with {outcome}")
    answer = outcome["Ok"]
    del answer["revision"]
    return answer, size


def rss(pid):
    output = subprocess.check_output(
        ["ps", "-o", "rss=", "-p", str(pid)],
        text=True,
    )
    return int(output.strip()) * 1024


def answer_digest(answer):
    return hashlib.blake2b(json.dumps(answer, sort_keys=True).encode()).digest()


def source(tag):
    return (
        f'const LABELS: [[string; 2]; 1] = [["name{tag}", "sample"]]\n'
        'const BYTES: [uint8; 4] = #embedBytes("../asset.bin")\n'
        f"func choose(_ label: int32) -> int32 {{ label }}\n"
        f"func choose(_ alternate{tag}: bool) -> int32 {{ 0 }}\n"
        f"func focus() -> int32 {{ local{tag} := 7; choose(local{tag}) }}\n"
    )


def replay(binary, target, edits, sample_every, measure_rss):
    with tempfile.TemporaryDirectory(prefix="taro-lsp-reclamation-") as temporary:
        root = Path(temporary).resolve()
        (root / "src").mkdir()
        main = str(root / "src/main.tr")
        asset = root / "asset.bin"
        initial = source(0)
        asset.write_bytes(bytes(4))
        documents = {main: initial}

        with subprocess.Popen(
            [binary, "--worker", "--target-facts", target],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
        ) as worker:
            try:
                old_reply, largest_reply = analyze(
                    worker, 1, {"Reset": {"root": str(root), "documents": documents}},
                )
                expected = answer_digest(old_reply)
                transient = None
                samples = []
                start = time.monotonic()
                restorations = 0
                for edit in range(1, edits + 1):
                    revision = edit + 1
                    restore = edit % sample_every == 0 or edit == edits
                    text = initial if restore else source(edit)
                    if restore or edit % 3 == 0:
                        asset.write_bytes((0 if restore else edit).to_bytes(4, "little"))
                        documents = {main: text}
                        update = {"Reset": {"root": str(root), "documents": documents}}
                        transient = None
                    else:
                        delta = {main: text}
                        if transient:
                            delta[transient] = None
                        transient = str(root / f"src/temporary{edit}.tr")
                        delta[transient] = f"func helper{edit}() -> int32 {{ {edit} }}"
                        update = {"Delta": delta}
                    answer, encoded_size = analyze(worker, revision, update)
                    largest_reply = max(largest_reply, encoded_size)
                    if restore:
                        if answer_digest(answer) != expected:
                            raise AssertionError(f"restored workspace changed its answer on edit {edit}")
                        restorations += 1
                        if old_reply is not None:
                            if old_reply != answer:
                                raise AssertionError("retained reply changed after an edit")
                            old_reply = None
                        if measure_rss:
                            samples.append(
                                {"edit": edit, "worker_rss": rss(worker.pid), "driver_rss": rss(os.getpid())},
                            )
                if worker.poll() is not None:
                    raise RuntimeError("the original analysis worker stopped")
                return {
                    "worker_pid": worker.pid,
                    "edits": edits,
                    "restored_revisions": restorations,
                    "seconds": time.monotonic() - start,
                    "max_reply_bytes": largest_reply,
                    "resident_memory": samples,
                }
            finally:
                worker.kill()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bin", type=Path, required=True)
    parser.add_argument("--target-facts", type=Path, required=True)
    parser.add_argument("--edits", type=int, default=10_000)
    parser.add_argument("--sample-every", type=int, default=500)
    parser.add_argument("--rss", action="store_true")
    args = parser.parse_args()
    if not 0 < args.edits < 2**31 or args.sample_every < 1:
        parser.error("the edit count and sampling interval must be positive")
    result = replay(
        args.bin.resolve(), args.target_facts.resolve(), args.edits, args.sample_every, args.rss,
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
