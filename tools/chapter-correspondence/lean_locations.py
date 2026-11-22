"""Cache original Lean InfoTree ranges and ask the native core to match them.

No text search and no function-head-only matching. Unmatched expressions retain
an explicit unavailable result instead of widening to a theorem/proof range.
"""

import hashlib
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

import check as chapter
from viewer import read_artifact, viewer_report


def original_index(source, module, query, environment_hash):
    driver = chapter.ROOT / "tools/lean_source_ranges.lean"
    raw = source.read_bytes()
    key = hashlib.sha256(
        driver.read_bytes()
        + str(source).encode()
        + module.encode()
        + raw
        + json.dumps(query, sort_keys=True).encode()
        + environment_hash.encode()
    ).hexdigest()
    directory = chapter.ROOT / "build/chapter-correspondence/source-ranges"
    directory.mkdir(parents=True, exist_ok=True)
    cached = directory / (key + ".json")
    result = read_artifact(cached)
    if not result:
        with tempfile.TemporaryDirectory(prefix="source-ranges-", dir=directory) as tmp:
            query_file = Path(tmp) / "query.json"
            output = Path(tmp) / "output.json"
            query_file.write_text(json.dumps(query, ensure_ascii=False))
            lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
            process = subprocess.run(
                [lake, "env", "lean", "--run", str(driver), str(source), module, str(query_file), str(output)],
                cwd=chapter.ROOT / chapter.CONFIG.project,
                check=False,
                capture_output=True,
                text=True,
                timeout=180,
            )
            if process.returncode:
                raise ValueError("Original Lean source indexing failed:\n" + process.stdout + process.stderr)
            result = json.loads(output.read_text())
            output.replace(cached)
    # Lean's syntax positions are UTF-8 byte offsets; source rendering uses
    # UTF-16. Convert from the original bytes, not from pretty-printed Lean.
    positions = sorted({point for row in result["ranges"] for point in (row["startByte"], row["endByte"])})
    offsets = {}
    cursor = 0
    utf16 = 0
    line = 1
    for point in positions:
        text = raw[cursor:point].decode("utf-8")
        utf16 += len(text.encode("utf-16-le")) // 2
        line += text.count("\n")
        offsets[point] = utf16, line
        cursor = point
    source_hash = hashlib.sha256(raw).hexdigest()
    return [
        dict(
            row,
            source=str(source.relative_to(chapter.ROOT)),
            sourceHash=source_hash,
            startOffset=offsets[row["startByte"]][0],
            endOffset=offsets[row["endByte"]][0],
            startLine=offsets[row["startByte"]][1],
        )
        for row in result["ranges"]
    ]


def lean_locations(source):
    report = viewer_report(source, include_ast=False)
    if report["status"] != "current":
        return dict(report, ranges=[])
    directory = chapter.ROOT / report["report"]
    formulas = read_artifact(directory.with_name("formulas.json"))
    operators = read_artifact(directory.with_name("operators.json"))

    # Transport only the fields consumed by the matcher; declaration bodies and
    # proof traces are large and are not location evidence.
    def context_fields(row):
        return {key: row[key] for key in ("index", "start", "end", "context") if key in row}

    compact_formulas = {
        "leanEvidence": {key: {"binders": row["binders"]} for key, row in formulas["leanEvidence"].items()},
        "formulas": [
            dict(
                context_fields(row),
                expressionFragments=[context_fields(part) for part in row.get("expressionFragments", [])],
            )
            for row in formulas["formulas"]
        ],
    }
    query = chapter.request({"action": "leanSourceTargets", "formulas": compact_formulas, "operators": operators})
    ranges = []
    dependency_hash = read_artifact(directory.with_name("dependencies.json"))["fingerprint"]
    files = []
    for module in chapter.CONFIG.modules:
        file = chapter.ROOT / chapter.CONFIG.project / "lean" / (module.replace(".", "/") + ".lean")
        files.append(str(file))
        ranges.extend(
            original_index(
                file, module, {key: query[key] for key in ("declarations", "heads", "variables")}, dependency_hash
            )
        )
    matched = chapter.request({"action": "leanSourceRanges", "targets": query["targets"], "ranges": ranges})["ranges"]
    hashes = {row["source"]: row["sourceHash"] for row in ranges}
    for row in matched:
        row["sourceHash"] = hashes[row["source"]]
    # Re-check the source/review/dependency snapshot after the potentially long
    # indexing step. A changed input cannot keep a current highlight result.
    current = viewer_report(source, include_ast=False)
    if current["status"] != "current" or current["report"] != report["report"]:
        return dict(current, ranges=[])
    return {
        "status": "current",
        "source": report["source"],
        "ranges": matched,
        "matchedFormulas": len({row["formulaIndex"] for row in matched}),
        "_cacheInputs": [*report.get("_cacheInputs", []), *files, str(chapter.ROOT / "tools/lean_source_ranges.lean")],
    }
