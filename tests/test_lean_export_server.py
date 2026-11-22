"""Persistent Lean checks must reject stale, failed, and warning-bearing evidence."""

import contextlib
import importlib.util
import queue
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import MagicMock, patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
SPEC = importlib.util.spec_from_file_location("tested_lean_server", ROOT / "tools/lean_export_server.py")
server_module = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(server_module)


def probe(value):
    return (
        f'import Lean\nopen Lean\nrun_cmd logInfo "SORT_PILOT {{\\"declaration\\":\\"probe\\",\\"value\\":{value}}}"\n'
    )


class LeanExportServerTests(unittest.TestCase):
    def test_warm_versions_do_not_retain_declarations_errors_or_warnings(self):
        import check_sort_pilot

        with contextlib.closing(server_module.LeanServer()) as server:
            first = "import Lean\ndef oldProbe : Nat := 7\n" + probe(1).split("import Lean\n", 1)[1]
            self.assertEqual(server.export(first)["probe"]["value"], 1)
            self.assertEqual(server.export(probe(2))["probe"]["value"], 2)
            with self.assertRaises(ValueError):
                server.export("import Lean\n#check oldProbe\n" + probe(3).split("import Lean\n", 1)[1])
            with self.assertRaises(ValueError):
                server.export("import Lean\nexample : False := by trivial\n")
            with self.assertRaises(ValueError):
                server.export(
                    "import Lean\nset_option linter.unusedVariables true\ndef ignored (x : Nat) : Nat := 0\n"
                    + probe(4).split("import Lean\n", 1)[1]
                )
            with patch.dict("os.environ", {"BOOK_LEAN_EXPORT_BACKEND": "subprocess"}):
                expected = check_sort_pilot.export(probe(5))
            self.assertEqual(server.export(probe(5)), expected)
            pid = server.process.pid
            version = server.version
            with patch.object(server_module, "library_stamp", return_value="changed"):
                self.assertEqual(server.export(probe(6))["probe"]["value"], 6)
            self.assertEqual(server.process.pid, pid)
            self.assertGreater(server.version, version)

    def test_server_requests_and_other_versions_cannot_finish_a_check(self):
        server = server_module.LeanServer.__new__(server_module.LeanServer)
        server.request_id = 0
        server.messages = queue.Queue()
        server.messages.put({"id": 1, "method": "workspace/inlayHint/refresh"})
        for version, message in [(1, "stale"), (2, "current")]:
            server.messages.put(
                {
                    "method": "textDocument/publishDiagnostics",
                    "params": {
                        "uri": "file:///probe.lean",
                        "version": version,
                        "diagnostics": [{"message": message}],
                    },
                }
            )
        server.messages.put({"id": 1, "result": {}})
        with patch.object(server, "_send"), patch.object(server, "_write") as reply:
            result = server._request("textDocument/waitForDiagnostics", {}, uri="file:///probe.lean", version=2)
        self.assertEqual(result, [{"message": "current"}])
        reply.assert_called_once_with({"jsonrpc": "2.0", "id": 1, "result": None})

    def test_open_never_builds_and_mid_check_changes_discard_evidence(self):
        server = server_module.LeanServer.__new__(server_module.LeanServer)
        server.documents = {}
        server.version = 0
        server.stamp = "before"
        diagnostics = [{"severity": 3, "message": 'SORT_PILOT {"declaration":"probe","value":1}'}]
        with (
            tempfile.TemporaryDirectory() as directory,
            patch.object(server_module, "library_stamp", side_effect=["before", "after"]),
            patch.object(server, "_send") as send,
            patch.object(server, "_request", return_value=diagnostics),
        ):
            server.directory = directory
            with self.assertRaisesRegex(RuntimeError, "changed during export"):
                server.export(probe(1))
        self.assertEqual(send.call_args_list[0].args[0], "textDocument/didOpen")
        self.assertEqual(send.call_args_list[0].args[1]["dependencyBuildMode"], "never")
        self.assertEqual(send.call_args_list[-1].args[0], "textDocument/didClose")

    def test_cancelled_client_stream_close_does_not_stop_daemon(self):
        broken = MagicMock()
        broken.makefile.return_value.__exit__.side_effect = BrokenPipeError("cancelled client")
        following = MagicMock()
        listener = MagicMock()
        listener.accept.side_effect = [(broken, None), (following, None)]
        with (
            tempfile.TemporaryDirectory() as directory,
            patch.object(server_module, "SOCKET", Path(directory) / "test.sock"),
            patch.object(server_module.socket, "socket") as socket_factory,
            patch.object(server_module, "receive_frame", side_effect=[{"op": "status"}, {"op": "stop"}]),
            patch.object(server_module, "send_frame") as send,
            patch.object(server_module.os, "chmod"),
            patch("builtins.print"),
        ):
            socket_factory.return_value.__enter__.return_value = listener
            server_module.serve()
        self.assertEqual(listener.accept.call_count, 2)
        self.assertEqual(send.call_count, 2)
        self.assertEqual(send.call_args.args[1], {"result": "stopped"})

    def test_stamp_detects_transitive_compiled_artifact_changes(self):
        with tempfile.TemporaryDirectory() as directory, patch.object(server_module, "PROJECT", Path(directory)):
            package = Path(directory) / ".lake/packages/dependency/.lake/build/lib/lean/Nested"
            package.mkdir(parents=True)
            artifact = package / "Proof.olean.server"
            artifact.write_text("old")
            before = server_module.library_stamp()
            artifact.write_text("new")
            self.assertNotEqual(server_module.library_stamp(), before)
            before = server_module.library_stamp()
            artifact.unlink()
            self.assertNotEqual(server_module.library_stamp(), before)


if __name__ == "__main__":
    unittest.main()
