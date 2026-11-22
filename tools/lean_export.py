"""Shared Lean evidence transport for chapter checks and legacy clients.

BOOK_LEAN_EXPORT is the current wire prefix. SORT_PILOT remains accepted only
for clients which have not migrated; no sort vocabulary is imported here.
"""

import json
import os
import re
import shutil
import subprocess
import tempfile
from contextlib import contextmanager
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIXES = ("BOOK_LEAN_EXPORT ", "SORT_PILOT ")


_CACHE = None


@contextmanager
def cached_probes(cache):
    global _CACHE
    previous = _CACHE
    _CACHE = cache
    try:
        yield cache
    finally:
        _CACHE = previous


def cache_active():
    return _CACHE is not None


def cache_provenance():
    return dict(_CACHE.last) if _CACHE is not None and _CACHE.last else None


def export(source: str) -> dict:
    if _CACHE is not None:
        return _CACHE.run(source, lambda: export_uncached(source))
    return export_uncached(source)


def export_uncached(source: str) -> dict:
    backend = os.environ.get("BOOK_LEAN_EXPORT_BACKEND", "auto")
    if backend not in {"auto", "server", "subprocess"}:
        raise ValueError("Unknown BOOK_LEAN_EXPORT_BACKEND")
    if backend != "subprocess":
        from lean_export_server import export_if_running

        try:
            result = export_if_running(source)
        except PermissionError as error:
            if backend == "server":
                raise RuntimeError("This sandbox cannot access the Lean export daemon socket") from error
            result = None
        if result is not None:
            return result
        if backend == "server":
            raise RuntimeError("Lean export daemon is not running; start tools/lean_export_server.py serve")
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    with tempfile.TemporaryDirectory(prefix="book-lean-export-") as directory:
        path = Path(directory) / "Export.lean"
        path.write_text(source)
        result = subprocess.run(
            [lake, "env", "lean", str(path)], cwd=ROOT / "polish-space", capture_output=True, text=True, check=False
        )
    return parse_export_result(result)


def parse_export_result(result) -> dict:
    if result.returncode or re.search(r"\bwarning:", result.stdout + result.stderr):
        diagnostics = "\n".join(
            line for line in (result.stdout + result.stderr).splitlines() if not line.startswith(PREFIXES)
        )
        if re.search(
            r"object file .* of module .* does not exist|Imports are out of date and must be rebuilt", diagnostics
        ):
            raise RuntimeError(
                "Lean dependency unavailable; finish the Lake build before inspecting expressions:\n" + diagnostics
            )
        raise ValueError("Lean adapter/export failed:\n" + diagnostics)
    records = {}
    for line in result.stdout.splitlines():
        if line.startswith(PREFIXES):
            record = json.loads(line.split(" ", 1)[1])
            records[record["declaration"]] = record
    if not records:
        raise ValueError("Lean produced no evidence")
    return records
