"""Reuse successful Lean probes against the exact transitive compiled environment.

This is an execution cache, never an interpretation-review cache. Imported module
changes invalidate dependent probes, including changes to typeclass instances and
notation that cannot safely be tracked by referenced declaration names alone.
"""

import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

SCHEMA = 1
MODULE = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")
ARTIFACTS = (".ilean", ".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig")


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False).encode()).hexdigest()


def atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(value, stream, ensure_ascii=False, separators=(",", ":"))
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def read_json(path):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return None


class Environment:
    def __init__(self, project, cache_dir, *, roots=None, toolchain=None):
        self.project = Path(project).resolve()
        self.cache_dir = Path(cache_dir)
        self.memo_path = self.cache_dir / "file-digests.json"
        self.memo = read_json(self.memo_path) or {}
        if not isinstance(self.memo, dict):
            self.memo = {}
        if roots is None:
            lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")

            def lake_output(*args):
                return subprocess.check_output([lake, "env", *args], cwd=self.project, text=True).strip()

            toolchain = Path(lake_output("lean", "--print-prefix"))
            roots = [Path(p) for p in lake_output("printenv", "LEAN_PATH").split(os.pathsep) if p]
            roots.append(toolchain / "lib/lean")
        self.roots = [Path(p).resolve() for p in roots]
        self.toolchain = Path(toolchain) if toolchain else None

    def file(self, path):
        if not path.is_file():
            return None
        stat = path.stat()
        stamp = [stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns]
        previous = self.memo.get(str(path), {})
        if (
            not isinstance(previous, dict)
            or previous.get("stamp") != stamp
            or not isinstance(previous.get("hash"), str)
        ):
            previous = {"stamp": stamp, "hash": hashlib.sha256(path.read_bytes()).hexdigest()}
            self.memo[str(path)] = previous
        return previous["hash"]

    def snapshot(self, imports):
        files, modules = {}, {}
        pending = list(imports)
        while pending:
            name = pending.pop()
            if name in modules:
                continue
            if not MODULE.fullmatch(name):
                raise ValueError(f"Invalid dependency module: {name}")
            relative = Path(*name.split("."))
            base = next(
                (root / relative for root in self.roots if (root / relative).with_suffix(".olean").is_file()), None
            )
            if base is None:
                raise RuntimeError(f"Missing compiled dependency: {name}; build the selected Lean modules first")
            metadata_path = Path(str(base) + ".ilean")
            metadata_hash = self.file(metadata_path)
            if metadata_hash is None:
                raise RuntimeError(f"Missing dependency inventory: {metadata_path}")
            memo = self.memo[str(metadata_path)]
            if not isinstance(memo.get("imports"), list) or memo.get("importsHash") != digest(memo["imports"]):
                data = json.loads(metadata_path.read_text())
                memo["imports"] = [entry[0] for entry in data["directImports"]]
                memo["importsHash"] = digest(memo["imports"])
            dependencies = memo["imports"]
            modules[name] = dependencies
            pending.extend(dependencies)
            for suffix in ARTIFACTS:
                path = Path(str(base) + suffix)
                files[str(path)] = self.file(path)
            # Also detect edits during validation, before someone rebuilds the
            # corresponding olean. Source hashes never replace compiled hashes.
            owner = base
            while owner.parent != owner and owner.name != ".lake":
                owner = owner.parent
            if owner.name == ".lake":
                for prefix in (owner.parent, owner.parent / "lean"):
                    path = (prefix / relative).with_suffix(".lean")
                    if path.exists():
                        files[str(path)] = self.file(path)
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.lean", "lakefile.toml"):
            path = self.project / name
            files[str(path)] = self.file(path)
        for root in self.roots:
            for path in sorted(root.glob("*.so")):
                files[str(path)] = self.file(path)
        if self.toolchain:
            path = self.toolchain / "bin/lean"
            files[str(path)] = self.file(path)
            for path in sorted((self.toolchain / "lib/lean").glob("*.so")):
                files[str(path)] = self.file(path)
        atomic_json(self.memo_path, self.memo)
        return {
            "schemaVersion": SCHEMA,
            "imports": list(imports),
            "modules": modules,
            "files": files,
            "fingerprint": digest(files),
        }


class ProbeCache:
    def __init__(self, directory, environment, *, force=False):
        self.directory = Path(directory)
        self.environment = environment
        self.force = force
        self.hits = self.executed = 0
        self.keys = set()
        self.requests = []
        self.last = None
        self.implementation = hashlib.sha256(
            Path(__file__).read_bytes()
            + Path(__file__).with_name("lean_export.py").read_bytes()
            + Path(__file__).with_name("lean_export_server.py").read_bytes()
        ).hexdigest()

    def run(self, source, execute):
        imports = re.findall(r"^import ([A-Za-z_][A-Za-z_0-9.]*)\s*$", source, re.MULTILINE)
        if set(imports) != set(self.environment["imports"]):
            raise ValueError("Probe imports differ from the recorded dependency environment")
        key = digest([SCHEMA, self.implementation, self.environment["fingerprint"], source])
        self.keys.add(key)
        path = self.directory / key[:2] / (key + ".json")
        cached = None if self.force else read_json(path)
        if (
            isinstance(cached, dict)
            and cached.get("key") == key
            and isinstance(cached.get("result"), dict)
            and cached["result"]
            and cached.get("resultHash") == digest(cached["result"])
        ):
            self.hits += 1
            self.record(key, source, "reused")
            return cached["result"]
        self.executed += 1
        result = execute()
        if not isinstance(result, dict) or not result:
            raise ValueError("No successful Lean evidence to cache")
        atomic_json(path, {"key": key, "resultHash": digest(result), "result": result})
        self.record(key, source, "executed")
        return result

    def record(self, key, source, mode):
        self.last = {"probeKey": key, "inputHash": hashlib.sha256(source.encode()).hexdigest(), "mode": mode}
        self.requests.append(self.last)

    def statistics(self):
        return {
            "reusedProbes": self.hits,
            "executedProbes": self.executed,
            "distinctProbes": len(self.keys),
            "forced": self.force,
            "environmentHash": self.environment["fingerprint"],
        }
