"""Line protocol to the persistent Haskell correspondence core.

Transport only: no interpretation fallback or duplicated lowering rules.
"""

import atexit
import hashlib
import json
import subprocess
import threading
from collections.abc import Mapping
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
_process = None
_lock = threading.Lock()


def close():
    global _process
    with _lock:
        if _process is not None:
            _process.stdin.close()
            try:
                _process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                _process.terminate()
                _process.wait()
            _process.stdout.close()
            _process = None


atexit.register(close)


def request(payload):
    global _process
    with _lock:
        if _process is None:
            _process = subprocess.Popen(
                [str(ROOT / "build/book-filter"), "chapter-correspondence"],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                text=True,
                encoding="utf-8",
            )
        if _process.poll() is not None:
            raise RuntimeError("Haskell correspondence worker exited unexpectedly")
        _process.stdin.write(json.dumps(payload, ensure_ascii=False) + "\n")
        _process.stdin.flush()
        line = _process.stdout.readline()
        if not line:
            raise RuntimeError("Haskell correspondence worker closed its response stream")
        result = json.loads(line)
        if "error" in result:
            raise ValueError(result["error"])
        return result


def lower_macro(name, arguments):
    return request({"action": "lowerMacro", "name": name, "arguments": arguments})["term"]


class NativeMacros(Mapping):
    """Read-only registry of operations owned by the Haskell core."""

    def __init__(self):
        self._entries = None

    def _load(self):
        if self._entries is None:
            self._entries = {
                name: (arity, lambda args, name=name: lower_macro(name, args))
                for name, arity in request({"action": "macros"})["macros"]
            }
        return self._entries

    def __getitem__(self, key):
        return self._load()[key]

    def __iter__(self):
        return iter(self._load())

    def __len__(self):
        return len(self._load())


def helper_name(name):
    """Stable wire identity for the generated helper, independent of its body."""
    return "openContext_" + hashlib.sha256(name.encode()).hexdigest()[:16]


def definition_payload(row, records, name):
    context = row["context"]
    payload = {
        "action": "expressionDefinition",
        "term": row["lean"],
        "name": name,
        "binders": records[context]["binders"] if context else [],
    }
    if context and "@" in context:
        declaration, path = context.split("@", 1)
        payload["proof"] = {"declaration": declaration, "path": path, "helper": helper_name(name)}
    return payload


def expression_definition(row, records, name):
    return request(definition_payload(row, records, name))["source"]


@lru_cache(maxsize=16)
def prelude(action, imports="", opens=""):
    return request({"action": action, "imports": imports, "opens": opens})["source"]


def operator_probe(reference_term, reference_context, term, context, mappings, records, suffix):
    response = request(
        {
            "action": "operatorProbe",
            "suffix": suffix,
            "mappings": mappings,
            "reference": definition_payload(
                {"lean": reference_term, "context": reference_context}, records, "OperatorProbe.reference" + suffix
            ),
            "expression": definition_payload(
                {"lean": term, "context": context}, records, "OperatorProbe.expression" + suffix
            ),
        }
    )
    return response["mappings"], response["source"]


def structural(operation, node):
    """Temporary adapter to native recognizers; results remain unreviewed candidates."""
    return json.loads(_structural(operation, json.dumps(node, ensure_ascii=False, sort_keys=True)))


@lru_cache(maxsize=8192)
def _structural(operation, encoded):
    return json.dumps(
        request({"action": "structural", "operation": operation, "node": json.loads(encoded)})["result"],
        ensure_ascii=False,
    )


def semantic_translation(
    tree,
    variables,
    occupied,
    first_marker=0,
    *,
    constants=None,
    root=True,
    conventions=None,
    records=None,
    standalone=False,
    resolve_context=False,
):
    """Both renderings of one AST, cached together; no semantic rules in Python."""
    if resolve_context:
        return semantic_translation_batch(
            [
                {
                    "tree": tree,
                    "variables": variables,
                    "firstMarker": first_marker,
                    "root": root,
                    "standalone": standalone,
                }
            ],
            occupied,
            constants=constants,
            conventions=conventions,
            records=records,
        )[0]
    payload = {
        "tree": tree,
        "variables": variables,
        "occupied": sorted(occupied),
        "firstMarker": first_marker,
        "constants": constants or {},
        "root": root,
        "standalone": standalone,
        "conventions": conventions or {},
        "records": {
            name: {
                "binders": [
                    {"name": binder["name"], "type": binder.get("type", "")}
                    for binder in records[name].get("binders", [])
                ]
            }
            for name in records or {}
        },
    }
    return json.loads(_semantic_translation(json.dumps(payload, ensure_ascii=False, sort_keys=True)))


@lru_cache(maxsize=8192)
def _semantic_translation(encoded):
    result = request({"action": "translateBatch", "expressions": [json.loads(encoded)]})["results"][0]
    return json.dumps(result, ensure_ascii=False)


def semantic_translation_batch(expressions, occupied, *, constants=None, conventions=None, records=None):
    """Transport a chapter's expression jobs with one shared source environment."""
    payload = {
        "action": "translateBatch",
        "environment": {
            "constants": constants or {},
            "conventions": conventions or {},
            "occupied": sorted(occupied),
            "standalone": True,
            "resolveContext": True,
            "records": {
                name: {
                    "binders": [
                        {
                            key: binder[key]
                            for key in ("name", "type", "instance", "value", "originalName")
                            if key in binder
                        }
                        for binder in record.get("binders", [])
                    ]
                }
                for name, record in (records or {}).items()
            },
        },
        "expressions": expressions,
    }
    return json.loads(_semantic_translation_batch(json.dumps(payload, ensure_ascii=False, sort_keys=True)))


@lru_cache(maxsize=16)
def _semantic_translation_batch(encoded):
    return json.dumps(request(json.loads(encoded))["results"], ensure_ascii=False)


def prepare_chapter(text, scopes, records, parsed=None):
    """Send source and original signatures once; Haskell owns all preparation."""
    payload = {
        "action": "prepareChapter",
        "text": text,
        "scopes": list(scopes),
        "records": {
            name: {key: value for key, value in record.items() if key in {"binders", "declarationType"}}
            for name, record in records.items()
        },
    }
    if parsed is not None:
        payload["parsed"] = parsed
    return json.loads(_prepare_chapter(json.dumps(payload, ensure_ascii=False, sort_keys=True)))


@lru_cache(maxsize=16)
def _prepare_chapter(encoded):
    return json.dumps(request(json.loads(encoded)), ensure_ascii=False)


def analyze_chapter(text, scopes, records, *, constants, conventions, parsed=None, interpret=True, include_ast=False):
    """One source-level transaction for preparation and both Lean renderings."""
    payload = {
        "action": "analyzeChapter",
        "text": text,
        "scopes": list(scopes),
        "records": {
            name: {key: value for key, value in record.items() if key in {"binders", "declarationType"}}
            for name, record in records.items()
        },
        "constants": constants,
        "conventions": conventions,
        "occupied": sorted({binder["name"] for record in records.values() for binder in record.get("binders", [])}),
        "interpret": interpret,
    }
    if parsed is not None:
        payload["parsed"] = parsed
    if include_ast:
        payload["includeAST"] = True
    return json.loads(_analyze_chapter(json.dumps(payload, ensure_ascii=False, sort_keys=True)))


@lru_cache(maxsize=16)
def _analyze_chapter(encoded):
    return json.dumps(request(json.loads(encoded)), ensure_ascii=False)
