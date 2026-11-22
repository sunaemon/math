"""Content-addressed, disposable storage for fully validated chapter renders."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import sys
import tempfile
from pathlib import Path


def fingerprint(paths: list[Path], context: str = "") -> str:
    digest = hashlib.sha256(context.encode())
    for path in sorted(set(paths)):
        name = str(path.resolve()).encode()
        content = path.read_bytes()
        digest.update(len(name).to_bytes(8, "big"))
        digest.update(name)
        digest.update(len(content).to_bytes(8, "big"))
        digest.update(content)
    return digest.hexdigest()


def toolchain_fingerprint(po4a: str) -> str:
    tools = ["perl", "pandoc", "msgattrib", "msgcat", "msgcmp", "msgfmt", "msggrep", "msginit", "msgmerge", po4a]
    paths = [Path(sys.executable), *Path(__file__).parent.glob("*translation*.py")]
    paths.append(Path(__file__).with_name("book_manifest.py"))
    for name in tools:
        resolved = shutil.which(name)
        if not resolved:
            raise OSError(f"translation tool not found: {name}")
        paths.append(Path(resolved))
    # Include po4a and repo-local Perl modules, including compiled extensions.
    libraries = [Path(value) for value in os.environ.get("PERL5LIB", "").split(os.pathsep) if value]
    resolved_po4a = Path(shutil.which(po4a) or po4a).resolve()
    libraries.append(resolved_po4a.parent / "lib")
    for directory in libraries:
        if directory.is_dir():
            paths.extend(path for path in directory.rglob("*") if path.is_file())
    environment = {key: value for key, value in os.environ.items() if key.startswith(("PERL", "LC_"))}
    environment["LANG"] = os.environ.get("LANG", "")
    return fingerprint(paths, sys.version + json.dumps(environment, sort_keys=True))


class RenderCache:
    def __init__(self, directory: Path, common: str):
        self.directory = directory
        self.common = common

    def key(self, paths: list[Path], context: str) -> str:
        return fingerprint(paths, self.common + context)

    def read(self, key: str) -> bytes | None:
        try:
            entry = json.loads((self.directory / f"{key}.json").read_text())
            if not isinstance(entry, dict) or entry.get("key") != key or not isinstance(entry.get("render"), str):
                return None
            content = entry["render"].encode()
            if entry.get("sha256") != hashlib.sha256(content).hexdigest():
                return None
            return content
        except (OSError, UnicodeError, ValueError, TypeError):
            return None

    def write(self, key: str, content: bytes) -> None:
        self.directory.mkdir(parents=True, exist_ok=True)
        entry = {"key": key, "render": content.decode(), "sha256": hashlib.sha256(content).hexdigest()}
        descriptor, name = tempfile.mkstemp(prefix=".render-", dir=self.directory)
        temporary = Path(name)
        try:
            with os.fdopen(descriptor, "w") as stream:
                json.dump(entry, stream, ensure_ascii=False)
            temporary.replace(self.directory / f"{key}.json")
        finally:
            temporary.unlink(missing_ok=True)
