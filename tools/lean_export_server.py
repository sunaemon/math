"""Persistent, version-synchronized Lean evidence exporter over a local socket."""

from __future__ import annotations

import argparse
import contextlib
import fcntl
import hashlib
import json
import os
import queue
import shutil
import socket
import struct
import subprocess
import tempfile
import threading
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "polish-space"
RUNTIME = Path(tempfile.gettempdir()) / f"math-lean-export-{os.getuid()}"
SOCKET = RUNTIME / (hashlib.sha256(str(ROOT).encode()).hexdigest()[:16] + ".sock")


def implementation_hash():
    return hashlib.sha256(Path(__file__).read_bytes() + (ROOT / "tools/lean_export.py").read_bytes()).hexdigest()


IMPLEMENTATION_HASH = implementation_hash()


def read_exact(stream, length):
    chunks = []
    while length:
        chunk = stream.read(length)
        if not chunk:
            raise EOFError("Lean export connection closed")
        chunks.append(chunk)
        length -= len(chunk)
    return b"".join(chunks)


def send_frame(stream, value):
    data = json.dumps(value, ensure_ascii=False).encode()
    stream.write(struct.pack("!Q", len(data)) + data)
    stream.flush()


def receive_frame(stream):
    length = struct.unpack("!Q", read_exact(stream, 8))[0]
    return json.loads(read_exact(stream, length))


def library_stamp():
    """Check compiled inputs, including transitive package and server artifacts."""
    roots = [PROJECT / ".lake/build/lib/lean", *PROJECT.glob(".lake/packages/*/.lake/build/lib/lean")]
    entries = []
    stack = [str(p) for p in roots if p.exists()]
    while stack:
        with os.scandir(stack.pop()) as children:
            for entry in children:
                if entry.is_dir(follow_symlinks=False):
                    stack.append(entry.path)
                elif ".olean" in entry.name:
                    stat = entry.stat()
                    entries.append((entry.path, stat.st_mtime_ns, stat.st_size, stat.st_ctime_ns))
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.lean", "lakefile.toml"):
        path = PROJECT / name
        if path.exists():
            stat = path.stat()
            entries.append((str(path), stat.st_mtime_ns, stat.st_size, stat.st_ctime_ns))
    digest = hashlib.sha256()
    for entry in sorted(entries):
        digest.update(repr(entry).encode())
    return digest.hexdigest()


class BuildChangedError(RuntimeError):
    """Evidence was produced while compiled dependencies changed."""


class LeanServer:
    def __init__(self):
        resources = contextlib.ExitStack()
        self.resources = resources
        ready = False
        try:
            self.directory = resources.enter_context(tempfile.TemporaryDirectory(prefix="book-lean-server-"))
            lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
            with tempfile.TemporaryFile() as log:
                self.process = subprocess.Popen(
                    [lake, "env", "lean", "--server"],
                    cwd=PROJECT,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=log,
                )
            self.resources.callback(self.process.stdin.close)
            self.resources.callback(self.process.stdout.close)
            self.resources.callback(stop_process, self.process)
            self.messages = queue.Queue()
            self.request_id = 0
            self.documents = {}
            self.version = 0
            self.stamp = library_stamp()
            threading.Thread(target=self._read, daemon=True).start()
            self._request(
                "initialize",
                {
                    "processId": os.getpid(),
                    "rootUri": PROJECT.as_uri(),
                    "capabilities": {"textDocument": {"publishDiagnostics": {"versionSupport": True}}},
                },
            )
            self._send("initialized", {})
            ready = True
        finally:
            if not ready:
                self.resources.close()

    def _read(self):
        try:
            while True:
                headers = {}
                while True:
                    line = self.process.stdout.readline()
                    if not line:
                        raise EOFError("Lean language server exited")
                    if line == b"\r\n":
                        break
                    key, value = line.decode().split(":", 1)
                    headers[key.lower()] = value.strip()
                self.messages.put(json.loads(read_exact(self.process.stdout, int(headers["content-length"]))))
        except (OSError, EOFError, ValueError, KeyError) as error:
            self.messages.put({"transport_error": error})

    def _write(self, message):
        data = json.dumps(message, ensure_ascii=False).encode()
        self.process.stdin.write(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
        self.process.stdin.flush()

    def _send(self, method, params, request_id=None):
        message = {"jsonrpc": "2.0", "method": method, "params": params}
        if request_id is not None:
            message["id"] = request_id
        self._write(message)

    def _request(self, method, params, *, uri=None, version=None, timeout=600):
        self.request_id += 1
        request_id = self.request_id
        self._send(method, params, request_id)
        diagnostics = []
        deadline = time.monotonic() + timeout
        while True:
            message = self.messages.get(timeout=max(0, deadline - time.monotonic()))
            if "transport_error" in message:
                raise RuntimeError("Lean server transport failed") from message["transport_error"]
            if "method" in message and "id" in message:
                # Server requests have an independent ID space; they are not
                # responses to our waitForDiagnostics request.
                method = message["method"]
                if method == "workspace/configuration":
                    result = [None] * len(message.get("params", {}).get("items", []))
                elif method in {
                    "client/registerCapability",
                    "workspace/inlayHint/refresh",
                    "workspace/semanticTokens/refresh",
                    "window/workDoneProgress/create",
                }:
                    result = None
                else:
                    self._write(
                        {
                            "jsonrpc": "2.0",
                            "id": message["id"],
                            "error": {"code": -32601, "message": "Unsupported client method"},
                        }
                    )
                    continue
                self._write({"jsonrpc": "2.0", "id": message["id"], "result": result})
                continue
            if message.get("method") == "textDocument/publishDiagnostics":
                notification = message["params"]
                if notification.get("uri") == uri and notification.get("version") == version:
                    if notification.get("isIncremental", False):
                        raise RuntimeError("Unexpected incremental diagnostics")
                    diagnostics = notification["diagnostics"]
            if message.get("id") == request_id and "method" not in message:
                if "error" in message:
                    raise RuntimeError(f"Lean server request failed: {message['error']}")
                return diagnostics

    def reload_dependencies(self, stamp):
        for uri, _ in self.documents.values():
            self._send("textDocument/didClose", {"textDocument": {"uri": uri}})
        self.documents.clear()
        self.stamp = stamp

    def export(self, source):
        from lean_export import parse_export_result

        before = library_stamp()
        if before != self.stamp:
            self.reload_dependencies(before)
        self.version += 1
        version = self.version
        imports = "\n".join(line for line in source.splitlines() if line.startswith("import "))
        key = hashlib.sha256(imports.encode()).hexdigest()[:16]
        if key not in self.documents:
            if len(self.documents) >= 4:
                old = next(iter(self.documents))
                uri, _ = self.documents.pop(old)
                self._send("textDocument/didClose", {"textDocument": {"uri": uri}})
            path = Path(self.directory) / (key + ".lean")
            path.write_text("")
            uri = path.as_uri()
            self._send(
                "textDocument/didOpen",
                {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "lean4",
                        "version": version,
                        "text": source,
                    },
                    "dependencyBuildMode": "never",
                },
            )
        else:
            uri, _ = self.documents[key]
            self._send(
                "textDocument/didChange",
                {
                    "textDocument": {"uri": uri, "version": version},
                    "contentChanges": [{"text": source}],
                },
            )
        self.documents[key] = (uri, version)
        diagnostics = self._request(
            "textDocument/waitForDiagnostics", {"uri": uri, "version": version}, uri=uri, version=version
        )
        after = library_stamp()
        if after != before:
            self.reload_dependencies(after)
            raise BuildChangedError("Lean build changed during export; discard this evidence")
        output = []
        failed = False
        for diagnostic in diagnostics:
            severity = diagnostic.get("severity", 1)
            message = diagnostic["message"]
            if severity <= 2:
                output.append(("error: " if severity == 1 else "warning: ") + message)
                failed = True
            else:
                output.append(message)
        return parse_export_result(subprocess.CompletedProcess([], int(failed), "\n".join(output), ""))

    def close(self):
        if self.process.poll() is None:
            try:
                self._request("shutdown", None, timeout=5)
                self._write({"jsonrpc": "2.0", "method": "exit"})
                self.process.wait(timeout=5)
            except (OSError, RuntimeError, queue.Empty, subprocess.TimeoutExpired):
                pass  # ExitStack supplies a bounded terminate/kill fallback.
        self.resources.close()


def stop_process(process):
    if process.poll() is None:
        process.terminate()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()


def request(value):
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as client:
        client.settimeout(600)
        client.connect(str(SOCKET))
        with client.makefile("rwb") as stream:
            send_frame(stream, value)
            response = receive_frame(stream)
    if "error" in response:
        exception = ValueError if response.get("kind") == "ValueError" else RuntimeError
        raise exception(response["error"])
    return response["result"]


def export_if_running(source):
    try:
        return request({"op": "export", "source": source, "implementationHash": implementation_hash()})
    except (FileNotFoundError, ConnectionRefusedError):
        return None


def serve():
    SOCKET.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    if SOCKET.parent.is_symlink() or SOCKET.parent.stat().st_uid != os.getuid() or SOCKET.parent.stat().st_mode & 0o077:
        raise RuntimeError("Lean export runtime directory must be private to this user")
    with open(SOCKET.with_suffix(".lock"), "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        SOCKET.unlink(missing_ok=True)
        server = None
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as listener:
            listener.bind(str(SOCKET))
            os.chmod(SOCKET, 0o600)
            listener.listen()
            print(f"Lean export daemon listening: {SOCKET}", flush=True)
            try:
                while True:
                    connection, _ = listener.accept()
                    # Buffered stream close may flush again after a cancelled
                    # client disconnects. Catch that exit-time error as well as
                    # failures inside the request, preserving the warm server.
                    with (
                        contextlib.suppress(BrokenPipeError, ConnectionResetError),
                        connection,
                        connection.makefile("rwb") as stream,
                    ):
                        try:
                            message = receive_frame(stream)
                            if message["op"] == "stop":
                                send_frame(stream, {"result": "stopped"})
                                break
                            if message["op"] == "status":
                                result = {"pid": os.getpid(), "leanPid": server.process.pid if server else None}
                            elif message["op"] == "export":
                                if message.get("implementationHash") != IMPLEMENTATION_HASH:
                                    raise RuntimeError("Lean export daemon code changed; restart the daemon")
                                if server is not None and server.process.poll() is not None:
                                    server.close()
                                    server = None
                                if server is None:
                                    server = LeanServer()
                                result = server.export(message["source"])
                            else:
                                raise ValueError("Unknown daemon operation")
                            send_frame(stream, {"result": result})
                        except (BrokenPipeError, ConnectionResetError, EOFError):
                            continue
                        except (OSError, ValueError, RuntimeError, queue.Empty, KeyError) as error:
                            if not isinstance(error, (ValueError, BuildChangedError)) and server is not None:
                                server.close()
                                server = None
                            with contextlib.suppress(BrokenPipeError):
                                send_frame(stream, {"error": str(error), "kind": type(error).__name__})
            finally:
                if server is not None:
                    server.close()
                SOCKET.unlink(missing_ok=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=["serve", "status", "stop"])
    args = parser.parse_args()
    if args.operation == "serve":
        serve()
    else:
        print(json.dumps(request({"op": args.operation})))
