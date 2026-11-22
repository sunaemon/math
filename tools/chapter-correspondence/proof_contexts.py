"""Inspect proof-local contexts without granting reviewed correspondence status.

Paths identify nodes in the elaborated proof body, whose fingerprint must be
reviewed before a context can be used as correspondence evidence. Let values
are retained; they are not replaced by arbitrary parameters.
"""

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from lean_export import export

sys.path.insert(0, str(Path(__file__).resolve().parent))
from chapter_config import load_chapter
from native import request


def __getattr__(name):
    # Preserve the inspection prelude API without starting a worker at import.
    if name in {"LEAN", "LEAN_BODY"}:
        body = request({"action": "proofPrelude"})["source"]
        return load_chapter().imports() + body if name == "LEAN" else body
    raise AttributeError(name)


def inspection_source_many(requests, *, imports=None):
    """Transport source-owned context requests to the native generator."""
    return request(
        {
            "action": "inspectContexts",
            "imports": load_chapter().imports() if imports is None else imports,
            "requests": list(requests),
        }
    )["source"]


def inspection_source(declaration, local_name, *, imports=None):
    # Names are encoded as Lean strings, never injected as command syntax.
    return inspection_source_many([(declaration, local_name)], imports=imports)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--chapter", default="polish-spaces")
    parser.add_argument("declaration")
    parser.add_argument("local_name")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    records = export(inspection_source(args.declaration, args.local_name, imports=load_chapter(args.chapter).imports()))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(records, ensure_ascii=False, indent=2) + "\n")
    print(f"{sum('@' in key for key in records)} local contexts; evidence: {args.output}")


def expression_from_context(declaration, path, term, name):
    """Ask Haskell to generate replay inside original kernel binders and lets."""
    from native import helper_name

    return request(
        {
            "action": "contextExpression",
            "declaration": declaration,
            "path": path,
            "term": term,
            "name": name,
            "helper": helper_name(name),
        }
    )["source"]


if __name__ == "__main__":
    main()
