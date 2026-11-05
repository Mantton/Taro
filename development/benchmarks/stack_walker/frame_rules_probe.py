#!/usr/bin/env python3
"""Audit LLVM frame recipes without changing Taro's compiler or runtime.

Run with LLVM 22's llc/llvm-readobj/llvm-dwarfdump/llvm-objdump on PATH:
  python3 development/benchmarks/stack_walker/frame_rules_probe.py --output /tmp/frames.json

The fixed cases approximate Taro's entry allocas and collecting calls. The
realigned and dynamic cases are adversarial LLVM cases, not claims that Taro
currently emits these layouts. This is a code-generation probe, not a collector
implementation, correctness proof, or performance benchmark. Objects are deleted
on exit; the output retains the IR, machine assembly, stack maps and unwind data.
Optional --object coverage audits expect ARM64 Mach-O objects and their adjacent
.pcmeta.o sidecars; the standalone fixtures cover all four target combinations.

Root locations and caller recovery are separate contracts. In particular,
LLVM's stack-size field can be UINT64_MAX and does not specify saved-register
locations: https://llvm.org/docs/StackMaps.html#stack-map-format
"""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


IR = r"""
declare void @observe(ptr)
declare void @llvm.experimental.stackmap(i64, i32, ...)

define void @fixed_small() #0 {
  %slot = alloca i64, align 8
  store volatile i64 1, ptr %slot
  call void (i64, i32, ...) @llvm.experimental.stackmap(i64 1, i32 0, ptr %slot)
  call void @observe(ptr %slot)
  ret void
}

define void @fixed_large() #0 {
  %slot = alloca [128 x i64], align 16
  store volatile i64 2, ptr %slot
  call void (i64, i32, ...) @llvm.experimental.stackmap(i64 2, i32 0, ptr %slot)
  call void @observe(ptr %slot)
  ret void
}

define void @realigned() #0 {
  %slot = alloca [8 x i64], align 64
  store volatile i64 3, ptr %slot
  call void (i64, i32, ...) @llvm.experimental.stackmap(i64 3, i32 0, ptr %slot)
  call void @observe(ptr %slot)
  ret void
}

define void @dynamic(i64 %size) #0 {
  %slot = alloca i64, align 8
  %buffer = alloca i8, i64 %size, align 16
  store volatile i64 4, ptr %slot
  call void (i64, i32, ...) @llvm.experimental.stackmap(i64 4, i32 0, ptr %slot)
  call void @observe(ptr %buffer)
  call void @observe(ptr %slot)
  ret void
}

attributes #0 = { noinline uwtable(sync) "disable-tail-calls"="true" "frame-pointer"="FP_POLICY" }
"""

TARGETS = (
    "aarch64-apple-darwin",
    "aarch64-unknown-linux-gnu",
    "x86_64-unknown-linux-gnu",
    "x86_64-apple-darwin",
)


def run(*command):
    return subprocess.check_output(command, text=True, stderr=subprocess.STDOUT, timeout=30)


def object_audit(path):
    text = run("llvm-objdump", "--unwind-info", str(path))
    if "file format mach-o arm64" not in text:
        raise ValueError("--object coverage audits currently require ARM64 Mach-O objects")
    encodings = re.findall(r"compact encoding:\s+(0x[0-9a-fA-F]+)", text)
    modes = Counter(f"0x{int(value, 16) & 0x0F000000:08x}" for value in encodings)
    result = {
        "path": str(path),
        "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "compact_unwind_entries": len(encodings),
        "compact_unwind_modes": dict(sorted(modes.items())),
    }
    metadata = path.with_name(path.stem + ".pcmeta.o")
    if metadata.exists():
        # These undefined symbols are the sidecar's mapped functions, plus its
        # registration call. Resolve by address: aliases need not have the same
        # spelling in the native unwind section and the metadata sidecar.
        names = set(run("llvm-nm", "--undefined-only", "-j", str(metadata)).split())
        names.discard("___gc__pc_metadata_register")
        symbols = {}
        for line in run("llvm-nm", "--defined-only", str(path)).splitlines():
            parts = line.split()
            if len(parts) == 3:
                symbols[parts[2]] = int(parts[0], 16)
        entries = {
            int(address, 16): int(encoding, 16) & 0x0F000000
            for address, encoding in re.findall(
                r"start:\s+0x([0-9a-f]+)[^\n]*\n\s+length:[^\n]*\n"
                r"\s+compact encoding:\s+0x([0-9a-f]+)", text
            )
        }
        assert names.issubset(symbols), "sidecar references unknown object symbols"
        assert all(symbols[name] in entries for name in names), "mapped function lacks an unwind entry"
        mapped_modes = Counter(f"0x{entries[symbols[name]]:08x}" for name in names)
        result.update({
            "metadata_sha256": hashlib.sha256(metadata.read_bytes()).hexdigest(),
            "mapped_functions": len(names),
            "mapped_compact_unwind_modes": dict(sorted(mapped_modes.items())),
            "mapped_dwarf_functions": sorted(name for name in names if entries[symbols[name]] == 0x03000000),
        })
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--object", type=Path, action="append", default=[],
                        help="ARM64 Mach-O object with optional adjacent .pcmeta.o sidecar")
    args = parser.parse_args()
    result = {
        "kind": "static code-generation investigation; no runtime change or timings",
        "llvm_version": run("llc", "--version").splitlines()[:3],
        "fixture_ir": IR,
        "cases": [],
        "existing_objects": [object_audit(path) for path in args.object],
    }
    with tempfile.TemporaryDirectory(prefix="monkey-frame-rules-") as temp:
        directory = Path(temp)
        for target in TARGETS:
            for level in (0, 3):
                for policy in ("none", "all"):
                    source = directory / "probe.ll"
                    source.write_text(IR.replace("FP_POLICY", policy))
                    obj = directory / "probe.o"
                    assembly = directory / "probe.s"
                    options = [f"-mtriple={target}", f"-O{level}"]
                    run("llc", *options, "-filetype=obj", str(source), "-o", str(obj))
                    run("llc", *options, "-filetype=asm", str(source), "-o", str(assembly))
                    maps = run("llvm-readobj", "--stackmap", str(obj)).replace(str(obj), "probe.o")
                    sizes = [int(size) for size in re.findall(r"stack size:\s+(\d+)", maps)]
                    assert len(sizes) == 4, maps
                    assert sizes[-1] == 2**64 - 1, "dynamic alloca must be reported unknown"
                    result["cases"].append({
                        "target": target,
                        "codegen_optimization": level,
                        "frame_pointer_policy": policy,
                        "stack_sizes": dict(zip(("fixed_small", "fixed_large", "realigned", "dynamic"), sizes)),
                        "assembly": assembly.read_text(),
                        "stack_maps": maps,
                        "eh_frame": run("llvm-dwarfdump", "--eh-frame", str(obj)).replace(str(obj), "probe.o"),
                    })
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"configurations": len(result["cases"]), "functions": 4 * len(result["cases"]),
                      "objects_audited": len(result["existing_objects"]), "output": str(args.output)}))


if __name__ == "__main__":
    main()
