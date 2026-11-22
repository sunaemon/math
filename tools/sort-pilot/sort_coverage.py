"""Bounded lexical coverage and a readable evidence report, not a prose prover."""

import json
import re
from collections import Counter
from html import escape

MATH = re.compile(r"\$\$(.*?)\$\$|\$([^$]+)\$", re.DOTALL)
TOKEN = re.compile(r"\\[A-Za-z]+|[A-Za-z]")
OPERATORS = {r"\in", r"\ne", r"\IncludedIn", r"\varnothing", r"\le", r"\check"}


def inventory(selected, source, start, bindings):
    formulas, occurrences, unknown = [], [], []
    identities = {b["symbol"]: b for b in bindings}
    for match in MATH.finditer(selected):
        content = match.group(1) if match.group(1) is not None else match.group(2)
        offset = start + match.start(1 if match.group(1) is not None else 2)
        formulas.append(content)
        # Preserve offsets while removing the two operator labels used in this passage.
        cleaned = re.sub(r"\\mathrm\{(?:rank|Ord)\}", lambda m: " " * len(m[0]), content)
        for token in TOKEN.finditer(cleaned):
            symbol = token[0]
            if symbol in OPERATORS:
                continue
            pos = offset + token.start()
            record = {"symbol": symbol, "offset": pos, "line": source.count("\n", 0, pos) + 1}
            binding = identities.get(symbol)
            if binding and binding["scopeStart"] <= pos < binding["scopeEnd"]:
                record["id"] = binding["id"]
            occurrences.append(record)
            if "id" not in record:
                unknown.append(record)
    return formulas, occurrences, unknown


def check_coverage(manifest, selected, source, records):
    coverage = manifest.get("coverage")
    if not coverage:
        return [], None
    findings = []

    def issue(kind, detail):
        findings.append({"kind": kind, "detail": detail})

    formulas, occurrences, unknown = inventory(selected, source, source.index(selected), manifest["bindings"])
    if Counter(formulas) != Counter(e["book"] for e in manifest["expressions"]):
        issue("formula-coverage", "Every dollar-delimited formula occurrence must have exactly one mapping.")
    symbols = {x["symbol"] for x in occurrences}
    mapped = [b["symbol"] for b in manifest["bindings"]]
    if symbols != set(mapped) or len(mapped) != len(set(mapped)):
        issue("variable-coverage", "Missing, duplicate, or unused variable mapping.")
    if unknown:
        issue("unsupported-token", json.dumps(unknown, ensure_ascii=False))
    for binding in manifest["bindings"]:
        record = records.get(binding["declaration"], {})
        slot = binding["slot"]
        binders = record.get("binders", [])
        if (
            not isinstance(slot, int)
            or slot >= len(binders)
            or slot < 0
            or binders[slot]["name"] != binding["leanName"]
        ):
            issue("binder-identity", binding["symbol"])
        if binding["declaration"] not in manifest["leanFingerprints"]:
            issue("unpinned-evidence", binding["declaration"])
    for name in [coverage["proof"], *coverage["support"], *(e["lean"] for e in manifest["expressions"])]:
        if name not in records or name not in manifest["leanFingerprints"]:
            issue("unpinned-evidence", name)
    proof = records.get(coverage["proof"], {}).get("binders", [])
    expected = [b for b in proof if b["name"].startswith("h")]
    assumptions = coverage["assumptions"]
    if [b["name"] for b in expected] != [a["binder"] for a in assumptions]:
        issue("assumption-coverage", "Every proof hypothesis must be traced to a source premise or local restriction.")
    for assumption in assumptions:
        if assumption["source"] not in selected:
            issue("missing-premise", assumption["source"])
        if not any(b["name"] == assumption["binder"] and b["type"] == assumption["leanType"] for b in expected):
            issue("assumption-type", assumption["binder"])
    bound = records.get(coverage["boundDeclaration"], {}).get("binders", [])
    if [(b["name"], b["type"]) for b in bound] != [(a["binder"], a["leanType"]) for a in coverage["boundArguments"]]:
        issue("argument-coverage", "Every ordinal_valuation_mem_ground argument must be accounted for.")
    return findings, {
        "formulas": len(formulas),
        "variables": len(symbols),
        "occurrences": occurrences,
        "assumptions": len(assumptions),
        "boundArguments": len(bound),
        "unknownTokens": unknown,
    }


def render_report(manifest, source, selected, records, findings, destination, formula_report=None):
    _, counts = check_coverage(manifest, selected, source, records)
    esc = lambda x: escape(str(x))

    def table(headers, rows):
        return (
            "<table><tr>"
            + "".join(f"<th>{esc(x)}</th>" for x in headers)
            + "</tr>"
            + "".join("<tr>" + "".join(f"<td><pre>{esc(x)}</pre></td>" for x in row) + "</tr>" for row in rows)
            + "</table>"
        )

    html = '<!doctype html><meta charset="utf-8"><title>Ordinal preservation correspondence</title>'
    html += "<style>body{font:16px system-ui;max-width:1400px;margin:2em auto;padding:1em}td,th{border:1px solid #aaa;padding:.5em;text-align:left;vertical-align:top}table{border-collapse:collapse;width:100%}pre{white-space:pre-wrap;overflow-wrap:anywhere;margin:0}h2{margin-top:2em}</style>"
    html += "<h1>Ordinal preservation: complete bounded correspondence</h1>"
    html += (
        '<p><a href="../../'
        + esc(manifest["source"])
        + '">English source</a> · <a href="../../tools/sort-pilot/case-forcing.json">Reviewed formula evidence</a> · <a href="../../tools/sort-pilot/Correspondences.lean">Checked Lean adapters</a></p>'
    )
    html += (
        "<p><b>"
        + ("PASS" if not findings else "FAIL")
        + "</b>: lexical coverage, evidence freshness, binder identities, and elaborated Lean proofs. "
    )
    html += "This does not mechanically establish that the prose means the selected Lean statement. Formula interpretations and the choice of Lean target are reviewed annotations. Explicit source scopes and variable identities are checked; types and binder positions come from Lean. No separate sorts are used.</p>"
    html += "<p>Scope: one entire proposition and proof; dollar-delimited mathematics only. Unsupported tokens fail closed. Variables spelled only in prose and general TeX syntax are outside this lexer. Ord and rank are operators, not variables. Lean adapters use universe 0; library declarations remain universe-polymorphic.</p>"
    html += (
        "<pre>"
        + esc(json.dumps({k: v for k, v in counts.items() if k != "occurrences"}, ensure_ascii=False, indent=2))
        + "</pre>"
    )
    html += "<h2>Findings</h2><pre>" + esc(json.dumps(findings, ensure_ascii=False, indent=2)) + "</pre>"
    html += "<h2>Source, with line numbers</h2><pre>"
    start = source.count("\n", 0, source.index(selected)) + 1
    html += esc("\n".join(f"{start + i}: {line}" for i, line in enumerate(selected.splitlines()))) + "</pre>"
    html += "<h2>Variables: source identity and Lean binder</h2>"
    html += table(
        [
            "Symbol / declaration ID",
            "Lean binder (type inferred)",
            "Explicit scope",
            "Every source occurrence (line:offset)",
        ],
        [
            [
                b["symbol"] + " / " + b["id"],
                b["declaration"] + " / " + b["leanName"] + " : " + b["leanType"],
                b["scope"],
                ", ".join(f"{x['line']}:{x['offset']}" for x in counts["occurrences"] if x.get("id") == b["id"]),
            ]
            for b in manifest["bindings"]
        ],
    )
    if formula_report is not None:
        html += "<h2>Formula type coverage (separate from mapping coverage)</h2>"
        html += "<p>All formula occurrences are enumerated from the source. A declaration link alone does not establish an expression type. Checked means the displayed Lean interpretation elaborates; it does not establish the truth of a proposition or equivalence with prose. Unresolved entries stay in the denominator.</p>"
        html += (
            "<pre>"
            + esc(
                json.dumps({k: v for k, v in formula_report.items() if k != "formulas"}, ensure_ascii=False, indent=2)
            )
            + "</pre>"
        )
        html += table(
            ["Source line / formula", "Status", "Lean expression", "Inferred type / unresolved reason"],
            [
                [
                    str(r["line"]) + " / " + r["book"],
                    r["status"],
                    r.get("term", ""),
                    r.get("inferredType", r.get("reason", "")),
                ]
                for r in formula_report["formulas"]
            ],
        )
    html += "<h2>Every formula: reviewed interpretation backed by checked declarations</h2>"
    html += table(
        ["Source formula", "Lean declaration", "Interpretation / conversion"],
        [[e["book"], e["lean"], e["interpretation"]] for e in manifest["expressions"]],
    )
    html += "<h2>All hypotheses of the source-proof adapter</h2>"
    html += table(
        ["Source", "Binder and checked type", "Origin"],
        [[a["source"], a["binder"] + " : " + a["leanType"], a["origin"]] for a in manifest["coverage"]["assumptions"]],
    )
    html += "<h2>All arguments of ordinal_valuation_mem_ground</h2>"
    html += table(
        ["Binder / checked type", "Instantiation in the proof"],
        [[a["binder"] + " : " + a["leanType"], a["argument"]] for a in manifest["coverage"]["boundArguments"]],
    )
    html += "<h2>Checked signatures</h2>"
    html += table(
        ["Declaration", "Binders", "Result"],
        [
            [n, "\n".join(b["name"] + " : " + b["type"] for b in records[n]["binders"]), records[n]["result"]]
            for n in manifest["leanFingerprints"]
            if n in records
        ],
    )
    destination.write_text(html + "\n")
    return counts
