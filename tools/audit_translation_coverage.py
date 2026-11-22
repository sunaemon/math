#!/usr/bin/env python3
"""Audit Japanese correspondence without counting widened PO bands as coverage.

Keep each canonical statement/proof paragraph as a separate unit. Project its
location and every genuine gap for navigation, but inherit coverage only from
exact canonical links. Check complete proof-environment alignment separately.

This is a report command: gaps do not fail it unless --strict is selected.
Exit codes: 0 report written, 1 strict coverage failure, 2 execution failure.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

import booklink_audit as audit
import booklink_coverage as coverage
import booklink_sourcemap as booklinks
import project_translation_sourcemap as projection


def translated_span(chapter, start, end):
    a, b, kind = chapter.project_span(start, end)
    return {
        "startOffset": a,
        "endOffset": b,
        "startLine": chapter.target_text.count("\n", 0, a) + 1,
        "endLine": chapter.target_text.count("\n", 0, b) + 1,
        "projection": kind,
    }


def audit_chapter(chapter, entries):
    """Return canonical coverage units with Japanese locations, never broadened status."""
    exact = [e for e in entries if e.get("match", {}).get("status") == "matched"]
    spans = audit.intervals(exact)
    proofs = audit.proof_ranges(chapter.source_text)
    resolver = coverage.ScopeResolver(chapter.source_text, str(chapter.source))
    units = []
    for unit in coverage.units_for_source(chapter.source, spans):
        if unit.structural:
            continue
        # Comments can precede a proof opener inside the same paragraph.
        visible = chapter.source_text[unit.start_offset : unit.end_offset]
        visible = re.sub(r"<!--.*?-->", lambda m: " " * len(m[0]), visible, flags=re.DOTALL)
        token = re.search(r"\S", visible)
        start = unit.start_offset + (token.start() if token else 0)
        kind = (
            "statement"
            if unit.kind == "statement"
            else ("proof" if any(a <= start < b for a, b in proofs) else "prose")
        )
        effective = coverage.merge_intervals([*spans, *resolver.skipped_spans(unit.start_offset, unit.end_offset)])
        gaps = [
            {
                "canonicalStartOffset": a,
                "canonicalEndOffset": b,
                "text": chapter.source_text[a:b],
                "translation": translated_span(chapter, a, b),
            }
            for a, b in coverage.complement(unit.start_offset, unit.end_offset, effective)
            if unit.status in {"partial", "uncovered"} and coverage.is_substantive_gap(chapter.source_text[a:b])
        ]
        units.append(
            {
                "kind": kind,
                "status": unit.status,
                "canonicalLine": unit.start_line,
                "translation": translated_span(chapter, unit.start_offset, unit.end_offset),
                "gaps": gaps,
            }
        )

    # Nested proof blocks belong to their containing proof. Distinct top-level
    # proofs must neither collapse to one target proof nor cross its boundary.
    def top(ranges):
        return [(a, b) for a, b in ranges if not any(c <= a and b <= d and (a, b) != (c, d) for c, d in ranges)]

    source_proofs = top(proofs)
    target_proofs = top(audit.proof_ranges(chapter.target_text))
    alignment, issues, seen = [], [], {}
    for a, b in source_proofs:
        span = translated_span(chapter, a, b)
        targets = [(c, d) for c, d in target_proofs if c < span["endOffset"] and span["startOffset"] < d]
        record = {"canonicalLine": chapter.source_text.count("\n", 0, a) + 1, "translation": span}
        alignment.append(record)
        if len(targets) != 1:
            issues.append({**record, "reason": "proof does not map to exactly one translated proof"})
        elif targets[0] in seen:
            issues.append(
                {
                    **record,
                    "reason": "distinct canonical proofs share one translated proof",
                    "otherCanonicalLine": seen[targets[0]],
                }
            )
        else:
            seen[targets[0]] = record["canonicalLine"]
    for a, b in target_proofs:
        if (a, b) not in seen:
            issues.append(
                {
                    "translation": {"startLine": chapter.target_text.count("\n", 0, a) + 1},
                    "reason": "translated proof has no unique canonical counterpart",
                }
            )
    return {"units": units, "proofAlignment": alignment, "alignmentIssues": issues}


def main(argv: list[str] | None = None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--out", type=Path, default=Path("build/translation-coverage-audit"))
    parser.add_argument("--strict", action="store_true", help="fail when coverage gaps or alignment issues remain")
    args = parser.parse_args(argv)
    args.repo_root = args.repo_root.resolve()
    if not args.out.is_absolute():
        args.out = args.repo_root / args.out
    try:
        return generate_report(args)
    except (OSError, UnicodeError, ValueError) as error:
        print(f"translation coverage audit failed: {error}", file=sys.stderr)
        return 2


def generate_report(args):
    root = args.repo_root
    sources = root / "polish-space/src/polish-space-book.json"
    targets = root / "polish-space-ja/src/polish-space-book-ja.json"
    chapters = projection.load_projections(sources, targets, root / "polish-space-ja/l10n/ja")
    lean = sorted((root / "polish-space/lean").rglob("*.lean"))
    coverage.check_decl_target_multiplicity(lean)
    source_map = booklinks.build_combined_sourcemap(root, lean)
    by_source = defaultdict(list)
    for entry in source_map["entries"]:
        by_source[entry["match"].get("source")].append(entry)
    reports, canonical_chapters, canonical_gaps, exemptions = [], [], [], []
    for chapter in chapters.values():
        report = audit_chapter(chapter, by_source[str(chapter.source)])
        baseline, gaps = audit.scan_source(chapter.source, root, by_source[str(chapter.source)], exemptions)
        canonical_chapters.append({"baseline": baseline})
        canonical_gaps.extend(gaps)
        reports.append(
            {
                "source": str(chapter.source.relative_to(root)),
                "translation": str(chapter.target.relative_to(root)),
                **report,
            }
        )
    summary = {
        kind: dict(Counter(u["status"] for c in reports for u in c["units"] if u["kind"] == kind))
        for kind in ("statement", "proof", "prose")
    }
    issues = sum(len(c["alignmentIssues"]) for c in reports)
    gaps = sum(u["status"] in {"partial", "uncovered"} for c in reports for u in c["units"])
    stale_reviews = audit.apply_reviews(
        canonical_gaps, audit.read_reviews(root / "polish-space/coverage-review.json"), root
    )
    scope = audit.review_scope(exemptions, audit.read_reviews(root / "polish-space/coverage-scope-review.json"))
    reviewed = audit.reviewed_coverage(audit.summarize(canonical_chapters, canonical_gaps, scope), scope)
    result = {
        "summary": summary,
        "reviewedCoverage": reviewed,
        "staleReviews": stale_reviews,
        "staleScopeReviews": scope["staleReviews"],
        "alignmentIssues": issues,
        "proofEnvironments": sum(len(c["proofAlignment"]) for c in reports),
        "chapters": reports,
    }
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "report.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    lines = [
        "# 日本語版のLean対応監査",
        "",
        "英語の各主張・証明段落・通常本文を集計単位として保持し、POを通じて日本語の位置を対応させる。",
        "日本語の表示範囲が文・段落全体に広がっても、未対応部分を対応済みには変更しない。",
        "対応数は数学的な内容の再査読を意味しない。引用部分の対象範囲は英語の監査に従う。",
        "",
        *audit.reviewed_coverage_markdown(reviewed),
        "",
        "## 現行指定によるリンク集計",
        "",
        "| 単位 | 対象内対応 | 部分対応 | 未対応 | 除外指定あり |",
        "|---|---:|---:|---:|---:|",
    ]
    for kind, counts in summary.items():
        lines.append(
            f"| {kind} | "
            + " | ".join(str(counts.get(k, 0)) for k in ("covered", "partial", "uncovered", "exempt"))
            + " |"
        )
    lines += [
        "",
        f"独立した証明環境の対応: {result['proofEnvironments']}件。結合・境界の不整合: {issues}件。",
        "",
        "未対応・部分対応はJSONの各単位とその `gaps` に英語の原文範囲・日本語の位置を残す。",
        "表示位置が粗い場合も集計単位と未対応の判定を統合しない。",
        "",
        "再現: `python3 tools/audit_translation_coverage.py`",
        "",
    ]
    for c in reports:
        for u in c["units"]:
            if u["status"] in {"partial", "uncovered"}:
                lines.append(f"- {c['translation']}:{u['translation']['startLine']} — {u['kind']}: {u['status']}")
        for issue in c["alignmentIssues"]:
            lines.append(f"- {c['translation']}:{issue['translation']['startLine']} — {issue['reason']}")
    (args.out / "report.md").write_text("\n".join(lines), encoding="utf-8")
    print(
        json.dumps(
            {"summary": summary, "proofEnvironments": result["proofEnvironments"], "alignmentIssues": issues},
            ensure_ascii=False,
            indent=2,
        )
    )
    return int(args.strict and bool(gaps or issues))


if __name__ == "__main__":
    raise SystemExit(main())
