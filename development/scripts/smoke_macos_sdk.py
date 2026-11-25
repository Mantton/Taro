#!/usr/bin/env python3
"""Exercise an extracted macOS SDK using the system linker and its own std."""

import argparse
import subprocess
import tarfile
import tempfile
import time
from pathlib import Path
from urllib.parse import unquote, urlparse

import disk_guard
from build_dist import verify_macos_linkage
from lsp_release_gate import Client, initialize, wait_for_diagnostics


def request(client, method, params):
    request_id = client.send(method, params, request=True)
    deadline = time.perf_counter() + 35
    while (reply := client.receive(deadline)) is not None:
        if reply.get("id") == request_id:
            if "error" in reply:
                raise RuntimeError(reply["error"])
            return reply["result"]
    raise TimeoutError(method)


def open_document(client, path):
    text = path.read_text()
    client.send("textDocument/didOpen", {"textDocument": {
        "uri": path.as_uri(), "languageId": "taro", "version": 1, "text": text,
    }})
    return text


def definition(client, path, text, prefix):
    offset = text.index(prefix + "readToString") + len(prefix)
    line = text.count("\n", 0, offset)
    column = len(text[text.rfind("\n", 0, offset) + 1:offset].encode("utf-16-le")) // 2
    result = request(client, "textDocument/definition", {
        "textDocument": {"uri": path.as_uri()},
        "position": {"line": line, "character": column},
    })
    if not result:
        raise RuntimeError(f"no definition for {prefix}readToString")
    return Path(unquote(urlparse(result["uri"]).path))


def verify_editor(sdk, app, source, env):
    with subprocess.Popen(
        [sdk / "bin/taro-lsp"], cwd=app, env=env,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
    ) as server:
        try:
            client = Client(server)
            initialize(client, app)
            started = time.perf_counter()
            text = open_document(client, source)
            if wait_for_diagnostics(client, source.as_uri(), 1, started, 30) is None:
                raise TimeoutError("SDK diagnostics")
            fs = definition(client, source, text, "std::fs::")
            if fs != sdk / "std/src/fs/fs.tr":
                raise RuntimeError(f"definition left the installed SDK: {fs}")
            text = open_document(client, fs)
            io = definition(client, fs, text, "std::io::")
            if io != sdk / "std/src/io/io.tr":
                raise RuntimeError(f"definition left the installed SDK: {io}")
            request(client, "shutdown", None)
            client.send("exit", None)
            if server.wait(timeout=5):
                raise RuntimeError("SDK language server shut down unsuccessfully")
        finally:
            if server.poll() is None:
                server.kill()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path)
    parser.add_argument("--developer-dir", type=Path, help="Select an Apple developer tools installation.")
    args = parser.parse_args()
    disk_guard.enforce()

    scratch = Path(__file__).resolve().parents[2] / "target"
    scratch.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="sdk-smoke-", dir=scratch) as temporary:
        root = Path(temporary)
        stage = root / "extract"
        stage.mkdir()
        with tarfile.open(args.archive, "r:gz") as archive:
            if not all(item.isfile() or item.isdir() for item in archive.getmembers()):
                raise ValueError("SDK archive must contain only regular files and directories")
            archive.extractall(stage, filter="data")
        (extracted,) = stage.iterdir()
        sdk = root / "Relocated Taro SDK"
        extracted.rename(sdk)
        app = root / "project"
        (app / "src").mkdir(parents=True)
        (root / "tmp").mkdir()
        env = {
            "PATH": "/usr/bin:/bin:/usr/sbin:/sbin",
            "TMPDIR": str(root / "tmp"),
            "TARO_LSP_CACHE_DIR": str(root / "lsp-cache"),
        }
        if args.developer_dir:
            env["DEVELOPER_DIR"] = str(args.developer_dir.resolve())
        taro = sdk / "bin/taro"
        verify_macos_linkage(taro)
        verify_macos_linkage(sdk / "bin/taro-lsp")
        for binary in (taro, sdk / "bin/taro-lsp"):
            subprocess.run([binary, "--version"], cwd=app, env=env, check=True)
        hello = root / "hello.tr"
        hello.write_text('func main() { print("Hello from the relocated SDK") }\n')
        run = subprocess.run([taro, "run", hello], cwd=app, env=env, check=True,
                             stdout=subprocess.PIPE, text=True)
        if run.stdout.strip() != "Hello from the relocated SDK":
            raise RuntimeError(f"unexpected output: {run.stdout}")
        executable = root / "hello"
        subprocess.run([taro, "build", hello, "-o", executable], cwd=app, env=env, check=True)
        verify_macos_linkage(executable)

        source = app / "src/main.tr"
        source.write_text('func main() { _ = std::fs::readToString("") }\n')
        verify_editor(sdk, app, source, env)

        (sdk / "lib/taro/runtime/libtaro_runtime.a").unlink()
        missing = subprocess.run([taro, "run", hello], cwd=app, env=env,
                                 capture_output=True, text=True)
        if missing.returncode == 0 or "runtime archive missing from the Taro SDK" not in missing.stderr:
            raise RuntimeError(f"expected SDK runtime diagnostic: {missing.stderr}")
        print("macOS SDK relocation, native linking, std navigation and missing-runtime checks passed")


if __name__ == "__main__":
    main()
