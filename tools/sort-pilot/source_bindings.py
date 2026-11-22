"""Explicit Markdown scope/binder links. No prose inference or sort vocabulary."""

import copy
import hashlib
import json
import re

BLOCK = re.compile(r"<!--\s*lean-correspondence\s*(\{.*?\})\s*-->", re.DOTALL)
END = re.compile(r"<!--\s*lean-correspondence-end:\s*([\w-]+)\s*-->")


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("Duplicate annotation key: " + key)
        result[key] = value
    return result


def annotation(text, scope):
    matches = []
    for match in BLOCK.finditer(text):
        data = json.loads(match[1], object_pairs_hook=unique_object)
        if not isinstance(data, dict):
            raise TypeError("Correspondence annotation must be an object")
        if data.get("scope") == scope:
            matches.append((match, data))
    if len(matches) != 1:
        raise ValueError("Expected exactly one declaration block for scope " + scope)
    start, data = matches[0]
    ends = [m for m in END.finditer(text) if m[1] == scope]
    if len(ends) != 1 or ends[0].start() < start.end():
        raise ValueError("Missing, duplicate or misplaced scope end: " + scope)
    end = ends[0]
    if BLOCK.search(text, start.end(), end.start()) or END.search(text, start.end(), end.start()):
        raise ValueError("Nested correspondence scopes are not supported by this pilot")
    if set(data) != {"scope", "lean", "bindings"}:
        raise ValueError("Expected scope, lean and bindings only")
    if not isinstance(data["lean"], dict) or not isinstance(data["bindings"], dict):
        raise TypeError("Lean aliases and bindings must be objects")
    if not all(isinstance(k, str) and isinstance(v, str) for k, v in data["lean"].items()):
        raise ValueError("Lean aliases must name declarations")
    return data, start, end


def annotation_hash(data):
    return hashlib.sha256(json.dumps(data, sort_keys=True, ensure_ascii=False).encode()).hexdigest()


def resolve(manifest, text, records):
    if "sourceScope" not in manifest:
        return manifest
    if "bindings" in manifest:
        raise ValueError("Source bindings must not be duplicated in the sidecar")
    result = copy.deepcopy(manifest)
    data, start, end = annotation(text, manifest["sourceScope"])
    a = text.index(manifest["startAnchor"])
    b = text.index(manifest["endAnchor"], a)
    if not (start.end() <= a < end.start() < b):
        raise ValueError("The declared scope must enclose the reviewed proposition and proof")
    if text[start.end() : a].strip() or text[end.end() : b].strip():
        raise ValueError("Scope markers must exactly delimit the reviewed passage")
    result["bindings"] = []
    seen = set()
    for identity, spec in data["bindings"].items():
        if not re.fullmatch(r"[a-z][a-z0-9-]*", identity) or not isinstance(spec, list) or len(spec) != 2:
            raise ValueError("A binding must be id: [TeX symbol, alias.binder]")
        symbol, target = spec
        if not isinstance(symbol, str) or not isinstance(target, str) or symbol in seen:
            raise ValueError("Ambiguous or invalid source symbol: " + str(symbol))
        seen.add(symbol)
        alias, name = target.rsplit(".", 1)
        declaration = data["lean"].get(alias)
        if declaration not in records:
            raise ValueError("Unknown Lean declaration alias: " + alias)
        binders = records[declaration]["binders"]
        slots = [i for i, binder in enumerate(binders) if binder["name"] == name]
        if len(slots) != 1:
            raise ValueError("Missing or ambiguous Lean binder: " + target)
        slot = slots[0]
        result["bindings"].append(
            {
                "id": data["scope"] + "/" + identity,
                "symbol": symbol,
                "declaration": declaration,
                "leanName": name,
                "slot": slot,
                "leanType": binders[slot]["type"],
                "scope": data["scope"],
                "scopeStart": start.end(),
                "scopeEnd": end.start(),
            }
        )
    # Premise and application types are also derived, not duplicated in reviewed metadata.
    for group, declaration in [
        ("assumptions", result["coverage"]["proof"]),
        ("boundArguments", result["coverage"]["boundDeclaration"]),
    ]:
        binders = {b["name"]: b["type"] for b in records[declaration]["binders"]}
        for entry in result["coverage"][group]:
            if "leanType" in entry:
                raise ValueError("Do not handwrite types in source-owned correspondence metadata")
            if entry["binder"] not in binders:
                raise ValueError("Unknown evidence binder: " + entry["binder"])
            entry["leanType"] = binders[entry["binder"]]
    result["actualAnnotationHash"] = annotation_hash(data)
    return result
