"""Generate unreviewed correspondence drafts from fresh booklink source matches.

No source, translation or review file is modified. Equal spellings are candidate
identities, not proof that the prose and Lean variables have the same meaning.
"""

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

import check as chapter
from booklink_sourcemap import SourceCache, build_sourcemap


def qualified_names(entry, declarations):
    lean = entry["lean"]
    name, line = lean.get("declName"), lean.get("declLine")
    if not name or line is None:
        return []
    return sorted(
        full
        for full, span in declarations.items()
        if (full == name or full.endswith("." + name)) and span[0] <= line - 1 <= span[2]
    )


def binding_draft(variables, declaration, record):
    bindings, suggestions = {}, []
    for symbol in sorted({variable["symbol"] for variable in variables}):
        options = [
            {
                "target": declaration + "/" + binder["name"],
                "leanType": binder["type"],
                "instance": binder["instance"],
                "binderIndex": index,
            }
            for index, binder in enumerate(record["binders"])
            if binder["name"] == symbol
        ]
        suggestions.append(
            {
                "symbol": symbol,
                "status": "candidate" if len(options) == 1 else "unresolved",
                "options": options,
                "occurrences": [
                    {"formulaIndex": v["formulaIndex"], "start": v["sourceStart"], "end": v["sourceEnd"]}
                    for v in variables
                    if v["symbol"] == symbol and "formulaIndex" in v
                ],
                "reason": "Exact spelling only; scope and meaning require review",
            }
        )
        if len(options) == 1:
            bindings[f"var-{len(bindings)}"] = {"symbol": symbol, "target": options[0]["target"]}
    return bindings, suggestions


def generate():
    config = chapter.CONFIG
    text = config.source.read_text()
    entries, source_cache = [], SourceCache()
    for module in config.modules:
        relative = Path(*module.split("."))
        lean_file = (chapter.ROOT / config.project / "lean" / relative).with_suffix(".lean")
        if not lean_file.exists():
            continue
        inventory = (chapter.ROOT / config.project / ".lake/build/lib/lean" / relative).with_suffix(".ilean")
        declarations = json.loads(inventory.read_text())["decls"]
        for entry in build_sourcemap(chapter.ROOT, lean_file, cache=source_cache)["entries"]:
            # Include failed matches as well: their booklink still identifies
            # the selected chapter even when no exact source span was found.
            source = chapter.ROOT / config.project / "src" / entry["booklink"].get("source", "")
            if source.resolve() != config.source.resolve():
                continue
            entry["declarationCandidates"] = qualified_names(entry, declarations)
            entries.append(entry)
    names = {name for entry in entries for name in entry["declarationCandidates"]}
    records = chapter.evidence(names)
    occurrences = chapter.occurrences(text)
    parsed = chapter.syntax([row["book"] for row in occurrences])
    if len(parsed) != len(occurrences):
        raise ValueError("Parser lost source formulas")
    formulas = []
    for row, syntax in zip(occurrences, parsed, strict=True):
        variables = []
        status = "unresolved"
        if row["closed"] and syntax["roundtrip"] and not syntax.get("problems"):
            tree, end = chapter.located(syntax["tree"])
            if end == len(row["book"]):
                variables, _ = chapter.leaves(tree)
                status = "parsed"
        formulas.append(dict(row, variables=variables, syntaxStatus=status))
    candidates = []
    for index, entry in enumerate(entries):
        match, names = entry["match"], entry["declarationCandidates"]
        item = {
            "id": f"{config.name}-booklink-{index}",
            "reviewStatus": "unreviewed",
            "booklink": entry,
            "status": "unresolved",
            "metadataDraft": None,
        }
        if match["status"] == "matched" and len(names) == 1:
            declaration = names[0]
            rows = [
                row
                for row in formulas
                if match["startOffset"] <= row["bodyStart"]
                and row["bodyStart"] + len(row["book"]) <= match["endOffset"]
            ]
            variables = [
                dict(
                    variable,
                    formulaIndex=row["index"],
                    sourceStart=row["bodyStart"] + variable["start"],
                    sourceEnd=row["bodyStart"] + variable["end"],
                )
                for row in rows
                for variable in row["variables"]
            ]
            bindings, suggestions = binding_draft(variables, declaration, records[declaration])
            item.update(
                status="candidate",
                sourceSpan={"start": match["startOffset"], "end": match["endOffset"]},
                formulas=[{k: row[k] for k in ("index", "bodyStart", "book", "syntaxStatus")} for row in rows],
                bindingSuggestions=suggestions,
                metadataDraft={"scope": item["id"], "context": {"declaration": declaration}, "bindings": bindings},
                reason="Review the span, lexical binders and proof-local contexts before inserting scope markers",
            )
        else:
            item["reason"] = "Booklink span or qualified declaration is unresolved or ambiguous"
        candidates.append(item)
    return {
        "schemaVersion": 1,
        "offsetConvention": "zero-based Unicode character offsets, half-open; lines one-based",
        "chapter": config.name,
        "source": str(config.source.relative_to(chapter.ROOT)),
        "sourceHash": hashlib.sha256(text.encode()).hexdigest(),
        "configurationHash": config.fingerprint,
        "reviewStatus": "unreviewed",
        "candidates": candidates,
        "leanEvidence": records,
        "summary": {
            "booklinks": len(candidates),
            "candidateScopes": sum(c["status"] == "candidate" for c in candidates),
            "unresolved": sum(c["status"] == "unresolved" for c in candidates),
            "bindingDrafts": sum(len(c["metadataDraft"]["bindings"]) for c in candidates if c["metadataDraft"]),
        },
        "meaning": "Drafts only. No source edit, interpretation approval, or complete proof-context correspondence.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--chapter", default="polish-spaces")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    chapter.configure(args.chapter)
    subprocess.run(["make", "build/book-filter"], cwd=chapter.ROOT, check=True)
    subprocess.run(
        [
            "make",
            "validate-lean",
            "LEAN_PROJECTS=" + chapter.CONFIG.project,
            "LEAN_MODULES=" + " ".join(chapter.CONFIG.modules),
        ],
        cwd=chapter.ROOT,
        check=True,
    )
    result = generate()
    output = args.output or chapter.ROOT / "build/chapter-correspondence" / args.chapter / "candidates.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(result["summary"], ensure_ascii=False))
    print("Unreviewed candidates:", output)


if __name__ == "__main__":
    main()
