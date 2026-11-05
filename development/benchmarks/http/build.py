#!/usr/bin/env python3
"""Build comparison programs in ignored storage with serial memory guards."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE.parent / "json/corpus"))
import run

WRK_REVISION = "a211dd5a7050b1f9e8a9870b95513060e72ac4a0"

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path, default=ROOT / "target/crypto-http/references")
    parser.add_argument("--python", default="3.15.2")
    parser.add_argument("--openssl", default="/opt/homebrew/opt/openssl@3")
    args = parser.parse_args()
    out = args.artifacts.resolve()
    subprocess.run(["git", "check-ignore", "-q", str(out / "identities.json")], cwd=ROOT, check=True)
    out.mkdir(parents=True, exist_ok=True)
    run.OUT = out
    env = dict(run.environment(), CARGO_BUILD_JOBS="1", CARGO_INCREMENTAL="0", CARGO_PROFILE_RELEASE_DEBUG="0", RUSTFLAGS="-C debuginfo=0", GOCACHE=str(out / "go-cache"), UV_CACHE_DIR=str(out / "uv-cache"))
    for name in ["rust", "swift", "python", "node", "bun"]:
        shutil.copytree(HERE / "servers" / name, out / name, dirs_exist_ok=True)
    for name in ["node", "bun"]:
        executable = shutil.which(name)
        if executable is None:
            raise RuntimeError(f"{name} is required for the JS comparison")
        destination = out / (name + "-runtime")
        destination.unlink(missing_ok=True)
        destination.symlink_to(Path(executable).resolve())
    run.checked([ROOT / "dist/bin/taro", "build", HERE / "servers/taro.tr", "--release", "-O3", "-o", out.parent / "taro-server"], "taro-build", dict(env, TARO_HOME=str(ROOT / "dist")), seconds=180)
    run.checked(["cc", "-O2", HERE / "process_usage.c", "-o", out / "process-usage"], "process-usage-build", env, seconds=30)
    run.checked([out / "process-usage", "--self-test"], "counter-units-check", env, seconds=10)
    run.checked(["go", "build", "-trimpath", "-o", out / "go-server", HERE / "servers/go/main.go"], "go-build", env, seconds=180)
    run.checked(["cargo", "build", "--release", "--manifest-path", out / "rust/Cargo.toml"], "rust-build", env, seconds=360)
    if not (out / "venv/bin/python").exists():
        run.checked(["uv", "venv", "--python", args.python, out / "venv"], "python-env", env, seconds=60)
    run.checked(["uv", "pip", "install", "--python", out / "venv/bin/python", "-r", out / "python/requirements.txt"], "python-deps", env, seconds=180)
    if not (out / "wrk/.git").exists():
        run.checked(["git", "clone", "https://github.com/wg/wrk.git", out / "wrk"], "wrk-fetch", env, seconds=120)
    run.checked(["git", "-C", out / "wrk", "checkout", "--detach", WRK_REVISION], "wrk-pin", env, seconds=60)
    run.checked(["make", "-C", out / "wrk", "-j1", "WITH_OPENSSL=" + args.openssl], "wrk-build", env, seconds=240)
    run.checked(["swift", "build", "--package-path", out / "swift", "-c", "release", "-j", "1"], "swift-build", env, seconds=1200)
    binaries = {"taro": out.parent / "taro-server", "go": out / "go-server", "rust": out / "rust/target/release/http-comparison", "swift": out / "swift/.build/release/Server", "wrk": out / "wrk/wrk", "usage": out / "process-usage", "node": out / "node-runtime", "bun": out / "bun-runtime"}
    cargo = tomllib.loads((out / "rust/Cargo.lock").read_text())
    info = {
        "git_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "binary_sha256": {name: hashlib.sha256(path.read_bytes()).hexdigest() for name, path in binaries.items()},
        "toolchains": {name: subprocess.check_output(command, text=True, stderr=subprocess.STDOUT).strip() for name, command in {"go": ["go", "version"], "rust": ["rustc", "--version"], "swift": ["swift", "--version"], "python": [str(out / "venv/bin/python"), "--version"], "node": [out / "node-runtime", "--version"], "bun": [out / "bun-runtime", "--version"]}.items()},
        "rust_packages": {p["name"]: p["version"] for p in cargo["package"] if p["name"] in ["axum", "tokio", "hyper", "serde", "serde_json"]},
        "swift_packages": json.loads((out / "swift/Package.resolved").read_text()),
        "python_packages": subprocess.check_output([out / "venv/bin/python", "-c", "import importlib.metadata as m,json; print(json.dumps({n:m.version(n) for n in ['starlette','uvicorn','uvloop','httptools']}))"], text=True).strip(),
        "taro_compiler_sha256": hashlib.sha256((ROOT / "dist/bin/taro").read_bytes()).hexdigest(),
        "taro_runtime_sha256": hashlib.sha256((ROOT / "dist/lib/taro/runtime/libtaro_runtime.a").read_bytes()).hexdigest(),
        "wrk_revision": WRK_REVISION,
        "machine": subprocess.check_output(["sysctl", "-n", "machdep.cpu.brand_string"], text=True).strip(),
        "cpu_count": os.cpu_count(),
    }
    (out / "identities.json").write_text(json.dumps(info, indent=2) + "\n")
    print("Reference build and artifact identities complete", flush=True)

if __name__ == "__main__":
    main()
