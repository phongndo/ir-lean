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

import json
import os
import queue
import subprocess
import sys
import threading
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
# How long a server may take on one file. Lean checks the whole file, and clangd parses LLVM's headers.
TIMEOUT = 600
# How long a server may take to send diagnostics after it has answered.
SETTLE = 30

SERVERS = [
    (["clangd"], "cpp", ["src/Emitter.cpp", "src/main.cpp", "src/Emitter.h"]),
    (["clangd"], "c", ["tests/real/memory.c", "tests/real/zlib_harness.c"]),
    (
        ["lake", "serve"],
        "lean",
        ["IRLean/Mem.lean", "tests/proofs/Popcount.lean", "tests/proofs/Adler32.lean"],
    ),
    (["uv", "run", "--quiet", "ty", "server"], "python", ["tests/differential.py", "tests/fuzz.py"]),
    (["uv", "run", "--quiet", "ruff", "server"], "python", ["tests/lsp.py"]),
    (["bash-language-server", "start"], "shellscript", ["tests/proofs.sh"]),
    (["nixd"], "nix", ["flake.nix", "nix/shell.nix"]),
    (["neocmakelsp", "stdio"], "cmake", ["CMakeLists.txt"]),
    (["taplo", "lsp", "stdio"], "toml", ["pyproject.toml", "lakefile.toml"]),
    (["yaml-language-server", "--stdio"], "yaml", [".github/workflows/ci.yml"]),
    (["rumdl", "server", "--stdio"], "markdown", ["README.md"]),
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
            self.process.wait(timeout=10)
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


def main():
    failed = False
    for command, language, paths in SERVERS:
        start = time.monotonic()
        problems = check_server(command, language, paths)
        name = " ".join(c for c in command if c not in ("uv", "run", "--quiet"))
        took = time.monotonic() - start
        print(f"{'FAIL' if problems else 'ok  '}  {name} ({language}, {len(paths)} files, {took:.0f} s)")
        for problem in problems[:10]:
            print(f"        {problem}")
        failed = failed or bool(problems)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
