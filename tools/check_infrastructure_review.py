#!/usr/bin/env python3
"""Check that every numbered infrastructure-review finding has a disposition.

The JSON register is edited after checking implementation evidence. This tool
checks completeness and identity only; it does not judge the fixes or evidence.
"""

import argparse
import json
import re
from pathlib import Path

REVIEW = Path("reviews/infrastructure-9d6e65df.md")
REGISTER = Path("reviews/infrastructure-9d6e65df-status.json")


def findings(text):
    batch = None
    result = []
    for number, line in enumerate(text.splitlines(), 1):
        heading = re.match(r"# 付録: バッチ (\w+)$", line)
        if heading:
            batch = heading[1]
        if batch in {"F1", "F2", "D1"}:
            finding = re.match(r"#{2,3} (\d+)\.", line)
            key = f"{batch}-{finding[1]}" if finding else None
        elif batch == "T1":
            finding = re.match(r"### ([A-D]-\d+)\.", line)
            key = f"T1-{finding[1]}" if finding else None
        else:
            finding = re.match(r"### ((?:P[12]|V[12]|B1|X1)-\d+)[.（ ]", line)
            key = finding[1] if finding else None
        if key:
            result.append({"id": key, "title": line.lstrip("# "), "reviewLine": number})
    for key in ("M-2", "M-3", "M-4", "M-5"):
        for number, line in enumerate(text.splitlines(), 1):
            if line.startswith(f"- **{key}"):
                result.append({"id": key, "title": line.removeprefix("- "), "reviewLine": number})
                break
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--initialize", action="store_true")
    parser.add_argument("--complete", action="store_true")
    args = parser.parse_args()
    expected = findings(REVIEW.read_text(encoding="utf-8"))
    if args.initialize:
        if REGISTER.exists():
            parser.error("register already exists; refusing to overwrite dispositions")
        rows = [{**item, "status": "pending", "reason": "", "evidence": []} for item in expected]
        REGISTER.write_text(json.dumps(rows, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    rows = json.loads(REGISTER.read_text(encoding="utf-8"))
    if [row["id"] for row in rows] != [item["id"] for item in expected]:
        parser.error("register identifiers or order differ from review findings")
    if len(expected) != 182:
        parser.error(f"expected 182 findings, found {len(expected)}")
    pending = []
    for row, item in zip(rows, expected, strict=True):
        if any(row[key] != item[key] for key in item):
            parser.error(f"review identity changed: {item['id']}")
        if row["status"] not in {"pending", "fixed", "no-change"}:
            parser.error(f"invalid status: {row['id']}")
        if row["status"] == "pending":
            pending.append(row["id"])
        elif not row["reason"] or not row["evidence"]:
            parser.error(f"completed finding lacks reason/evidence: {row['id']}")
    print(f"{len(rows)} findings; {len(rows) - len(pending)} assessed; {len(pending)} pending")
    if args.complete and pending:
        parser.error("unresolved findings: " + ", ".join(pending))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
