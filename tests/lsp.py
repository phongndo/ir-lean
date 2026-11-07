#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Starts each language server the way an editor would, opens real files, and fails if a server crashes,
doesn't answer, or reports an error in a file.

The proofs need their generated modules, so run `tests/proofs.sh build/ir-lean --generate build/generated`
first.

usage: tests/lsp.py
"""

import concurrent.futures
import glob
import hashlib
import json
import os
import queue
import subprocess
import sys
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# CI doesn't keep this, so every server runs there.
RESULTS = os.path.join(ROOT, "build", "result-cache")
# How long a server may take on one file. Lean checks the whole file, and clangd parses LLVM's headers.
TIMEOUT = 600
# How long a server may take to send diagnostics after it has answered.
SETTLE = 30

PYTHON_INPUTS = ["tests/*.py", "pyproject.toml", "uv.lock"]
# Each server, the language it's told a file is in, the files it opens, and what it reads to answer.
SERVERS = [
    (
        ["clangd"],
        "cpp",
        ["src/Emitter.cpp", "src/main.cpp", "src/Emitter.h"],
        ["src/*", "build/compile_commands.json", ".clang-tidy", ".clang-format"],
    ),
    (
        ["clangd"],
        "c",
        ["tests/real/memory.c", "tests/real/zlib_harness.c"],
        ["tests/real/*.c", "tests/real/compile_flags.txt", ".clang-tidy", ".clang-format"],
    ),
    (
        ["lake", "serve"],
        "lean",
        ["IRLean/Mem.lean", "tests/proofs/Popcount.lean", "tests/proofs/Adler32.lean"],
        [
            "IRLean.lean",
            "IRLean/*.lean",
            "tests/proofs/*.lean",
            "build/generated/*.lean",
            "build/generated/*/*.lean",
            "lakefile.toml",
            "lake-manifest.json",
            "lean-toolchain",
        ],
    ),
    (
        ["uv", "run", "--quiet", "ty", "server"],
        "python",
        ["tests/differential.py", "tests/fuzz.py"],
        PYTHON_INPUTS,
    ),
    (["uv", "run", "--quiet", "ruff", "server"], "python", ["tests/lsp.py"], PYTHON_INPUTS),
    (["bash-language-server", "start"], "shellscript", ["tests/proofs.sh"], ["tests/*.sh"]),
    (["nixd"], "nix", ["flake.nix", "nix/shell.nix"], ["*.nix", "nix/*.nix", "flake.lock"]),
    (["neocmakelsp", "stdio"], "cmake", ["CMakeLists.txt"], ["CMakeLists.txt", ".gersemirc"]),
    (["taplo", "lsp", "stdio"], "toml", ["pyproject.toml", "lakefile.toml"], ["*.toml"]),
    (["yaml-language-server", "--stdio"], "yaml", [".github/workflows/ci.yml"], [".github/*/*.yml"]),
    (["rumdl", "server", "--stdio"], "markdown", ["README.md"], ["*.md", "docs/*.md", ".rumdl.toml"]),
]


class Server:
    def __init__(self, command):
        self.process = subprocess.Popen(
            command, cwd=ROOT, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL
        )
        self.next_id = 0
        self.pulls_diagnostics = False
        self.answers = {}
        self.diagnostics = {}
        self.events = queue.Queue()
        threading.Thread(target=self.read, daemon=True).start()

    def write(self, message):
        body = json.dumps({"jsonrpc": "2.0", **message}).encode()
        assert self.process.stdin
        self.process.stdin.write(b"Content-Length: %d\r\n\r\n%s" % (len(body), body))
        self.process.stdin.flush()

    def read(self):
        stream = self.process.stdout
        assert stream
        while True:
            length = 0
            while line := stream.readline():
                if line in (b"\r\n", b"\n"):
                    break
                if line.lower().startswith(b"content-length:"):
                    length = int(line.split(b":")[1])
            if not length:
                self.events.put("closed")
                return
            self.handle(json.loads(stream.read(length)))

    def handle(self, message):
        method = message.get("method")
        if method is None:
            self.answers[message["id"]] = message
        elif "id" in message:
            # A request from the server. An editor's settings are all defaults here.
            count = len(message.get("params", {}).get("items", []))
            result = [None] * count if method == "workspace/configuration" else None
            self.write({"id": message["id"], "result": result})
        elif method == "textDocument/publishDiagnostics":
            self.diagnostics[message["params"]["uri"]] = message["params"]["diagnostics"]
        self.events.put("message")

    def wait_until(self, done, seconds):
        deadline = time.monotonic() + seconds
        while not done():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                return False
            try:
                if self.events.get(timeout=remaining) == "closed":
                    return done()
            except queue.Empty:
                return False
        return True

    def request(self, method, params):
        self.next_id += 1
        request_id = self.next_id
        self.write({"id": request_id, "method": method, "params": params})
        if not self.wait_until(lambda: request_id in self.answers, TIMEOUT):
            raise RuntimeError(f"no answer to {method}")
        return self.answers[request_id]

    def notify(self, method, params):
        self.write({"method": method, "params": params})

    def stop(self):
        try:
            self.request("shutdown", None)
            self.notify("exit", None)
            self.process.wait(timeout=1)
        except (RuntimeError, OSError, subprocess.TimeoutExpired):
            pass
        self.process.kill()


def check_file(server, language, path):
    """Returns the errors the server reports in a file."""
    full = os.path.join(ROOT, path)
    uri = "file://" + full
    with open(full, encoding="utf-8") as f:
        text = f.read()
    document = {"uri": uri, "languageId": language, "version": 1, "text": text}
    server.notify("textDocument/didOpen", {"textDocument": document})
    if language == "lean":
        answer = server.request("textDocument/waitForDiagnostics", {"uri": uri, "version": 1})
    else:
        answer = server.request("textDocument/documentSymbol", {"textDocument": {"uri": uri}})
    # A server doesn't have to support this request, as long as it answers.
    if "error" in answer and answer["error"].get("code") != -32601:
        return [f"request failed: {answer['error'].get('message')}"]
    # Some servers wait to be asked for diagnostics, and others send them when they're ready.
    if server.pulls_diagnostics:
        answer = server.request("textDocument/diagnostic", {"textDocument": {"uri": uri}})
        if "error" in answer:
            return [f"{path}: can't get diagnostics: {answer['error'].get('message')}"]
        found = answer["result"]["items"]
    elif server.wait_until(lambda: uri in server.diagnostics, SETTLE):
        found = server.diagnostics[uri]
    else:
        return [f"{path}: no diagnostics"]
    return [
        f"{path}:{d['range']['start']['line'] + 1}: {d['message'].splitlines()[0]}"
        for d in found
        if d.get("severity") == 1
    ]


def check_server(command, language, paths):
    """Returns what's wrong with a language server."""
    server = Server(command)
    try:
        answer = server.request(
            "initialize",
            {
                "processId": os.getpid(),
                "rootUri": "file://" + ROOT,
                "workspaceFolders": [{"uri": "file://" + ROOT, "name": "ir-lean"}],
                "capabilities": {
                    "textDocument": {
                        "publishDiagnostics": {},
                        "diagnostic": {},
                        "documentSymbol": {"hierarchicalDocumentSymbolSupport": True},
                    },
                    "workspace": {"configuration": True},
                },
            },
        )
        if "result" not in answer or not answer["result"].get("capabilities"):
            return [f"bad answer to initialize: {str(answer)[:200]}"]
        server.pulls_diagnostics = "diagnosticProvider" in answer["result"]["capabilities"]
        server.notify("initialized", {})
        problems = []
        for path in paths:
            problems += check_file(server, language, path)
            if server.process.poll() is not None:
                problems.append(f"crashed on {path}")
                break
        return problems
    except (RuntimeError, OSError) as e:
        return [str(e)]
    finally:
        server.stop()


def server_key(command, language, inputs):
    """A hash of what the server's answer depends on: its version, through its place in the Nix store, this
    script, and what it reads."""
    key = hashlib.sha256(f"{os.environ.get('PATH')}\0{command}\0{language}\0".encode())
    paths = [os.path.abspath(__file__)]
    for pattern in inputs:
        paths += sorted(glob.glob(pattern, root_dir=ROOT))
    for path in paths:
        with open(os.path.join(ROOT, path), "rb") as f:
            key.update(f"{path} {os.fstat(f.fileno()).st_size}\n".encode() + f.read())
    return key.hexdigest()


def timed_check(server):
    """Returns what's wrong with a server and how long it took to find out. A server that had nothing to say
    about these inputs before doesn't run again."""
    command, language, paths, inputs = server
    start = time.monotonic()
    passed = os.path.join(RESULTS, f"lsp-{server_key(command, language, inputs)}")
    if os.path.exists(passed):
        return [], time.monotonic() - start
    problems = check_server(command, language, paths)
    if not problems:
        os.makedirs(RESULTS, exist_ok=True)
        with open(passed, "w"):
            pass
    return problems, time.monotonic() - start


def main():
    failed = False
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(SERVERS)) as pool:
        for (command, language, paths, _), (problems, took) in zip(
            SERVERS, pool.map(timed_check, SERVERS), strict=True
        ):
            name = " ".join(c for c in command if c not in ("uv", "run", "--quiet"))
            print(f"{'FAIL' if problems else 'ok  '}  {name} ({language}, {len(paths)} files, {took:.0f} s)")
            for problem in problems[:10]:
                print(f"        {problem}")
            failed = failed or bool(problems)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
