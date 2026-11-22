#!/usr/bin/env python3
"""Triage link gaps before writing new Lean proofs.

Scan every chapter in the manifest, including chapters with no booklinks.
Count exact links of every target kind in statements, proofs, and ordinary prose.
This measures existing links, NOT mathematical correspondence. A link on
the preceding theorem is only a search lead, never evidence that its proof's
paragraphs are implemented. Human decisions live in a separate JSON file and
expire when the passage or any cited evidence file changes.

Example:
    python3 tools/booklink_audit.py --out build/coverage-audit
"""

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import asdict
from pathlib import Path

import booklink_coverage as cov
import booklink_sourcemap as bk
from book_manifest import read_manifest


class AuditInputError(ValueError):
    """An audit input has an invalid external data schema."""


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def proof_ranges(text):
    stack, result = [], []
    # Comments can contain illustrative delimiters. Preserve offsets.
    visible = re.sub(r"<!--.*?-->", lambda m: " " * len(m[0]), text, flags=re.DOTALL)
    for m in re.finditer(r"\\(begin|end)\{proof\}", visible):
        if m[1] == "begin":
            stack.append(m.start())
        elif not stack:
            raise ValueError("unmatched proof end")
        else:
            result.append((stack.pop(), m.end()))
    if stack:
        raise ValueError("unmatched proof begin")
    return result


def resolved(entries):
    return [
        e
        for e in entries
        if e["match"].get("status") in {"matched", "weak"} and e["match"].get("startOffset") is not None
    ]


def intervals(entries):
    return cov.merge_intervals([(e["match"]["startOffset"], e["match"]["endOffset"]) for e in entries])


def overlaps(unit, entry):
    m = entry["match"]
    return m["startOffset"] < unit.end_offset and unit.start_offset < m["endOffset"]


def evidence(entry, root):
    return {
        **entry["lean"],
        "source": str(Path(entry["lean"]["source"]).relative_to(root)),
        "target": entry["booklink"].get("target"),
        "match": entry["match"]["status"],
    }


def scan_source(path, root, entries, exemptions=None, *, document=None):
    document = document if document is not None else bk.SourceDocument(path, path.read_text(encoding="utf-8"))
    text = document.text
    entries = resolved(entries)
    all_spans = intervals([e for e in entries if e["match"]["status"] == "matched"])
    units = cov.units_for_source(path, all_spans, document=document)
    ranges = proof_ranges(text)
    visible = re.sub(r"<!--.*?-->", lambda m: " " * len(m[0]), text, flags=re.DOTALL)
    counts, gaps = defaultdict(Counter), []
    for unit in units:
        if unit.structural:
            continue
        # A scope comment can share the paragraph block with the proof opener.
        # Classify by the first visible token, not by that preceding comment.
        token = re.search(r"\S", visible[unit.start_offset : unit.end_offset])
        content_start = unit.start_offset + token.start() if token else unit.start_offset
        containing = [(a, b) for a, b in ranges if a <= content_start < b]
        if unit.kind == "statement":
            kind, baseline, parent = "statement", unit, unit
        elif containing:
            kind = "proof"
            baseline = unit
            start, _ = min(containing, key=lambda pair: pair[1] - pair[0])
            previous = [u for u in units if u.kind == "statement" and u.end_offset <= start]
            parent = previous[-1] if previous else None
        else:
            kind, baseline, parent = "prose", unit, None
        counts[kind][baseline.status] += 1
        if baseline.status == "exempt" and exemptions is not None:
            exemptions.append(
                {
                    "id": f"{path.stem}:{unit.start_line}:{kind}",
                    "source": str(path.relative_to(root)),
                    "kind": kind,
                    "line": unit.start_line,
                    "endLine": unit.end_line,
                    "passageSha256": digest(text[unit.start_offset : unit.end_offset]),
                    "sourceSha256": digest(text),
                    "originalReason": unit.exempt_reason,
                }
            )
        if baseline.status not in {"partial", "uncovered"}:
            continue
        direct = [e for e in entries if overlaps(unit, e)]
        context = [e for e in entries if parent and overlaps(parent, e)]
        passage = text[unit.start_offset : unit.end_offset]
        gaps.append(
            {
                "id": f"{path.stem}:{unit.start_line}:{kind}",
                "source": str(path.relative_to(root)),
                "kind": kind,
                "line": unit.start_line,
                "endLine": unit.end_line,
                "passageSha256": digest(passage),
                "text": passage,
                "baseline": baseline.status,
                "anyLink": unit.status,
                "status": "unreviewed",
                "statement": parent.label if parent else None,
                "direct": [evidence(e, root) for e in direct],
                "context": [evidence(e, root) for e in context],
                "gaps": [asdict(g) for g in unit.gaps],
            }
        )
    return dict(counts), gaps


DECISIONS = {"link_only", "proof_alignment", "formalization_required", "external_scope", "deferred_astra", "unreviewed"}


def apply_reviews(items, reviews, root):
    by_id = {item["id"]: item for item in items}
    used, stale = set(), []
    for review in reviews:
        ident = review["id"]
        if ident in used:
            raise ValueError(f"duplicate review: {ident}")
        used.add(ident)
        if review["status"] not in DECISIONS or not review.get("reason"):
            raise ValueError(f"invalid review: {ident}")
        if review["status"] in {"link_only", "proof_alignment", "formalization_required"} and not review.get(
            "evidence"
        ):
            raise ValueError(f"missing evidence: {ident}")
        if review["status"] == "deferred_astra":
            todo_item = review.get("todoItem")
            if not todo_item or not review.get("evidence"):
                raise ValueError(f"missing Astra handoff evidence/TODO: {ident}")
        item = by_id.get(ident)
        valid = item is not None and item["passageSha256"] == review["passageSha256"]
        for ev in review.get("evidence", []):
            file = root / ev["source"]
            valid = valid and file.is_file() and digest(file.read_text(encoding="utf-8")) == ev["sha256"]
        if review["status"] == "deferred_astra":
            todo = root / "todo.md"
            valid = valid and todo.is_file() and review["todoItem"] in todo.read_text(encoding="utf-8")
        if not valid:
            stale.append(ident)
            continue
        item.update(status=review["status"], reason=review["reason"], reviewedEvidence=review.get("evidence", []))
    return stale


def review_scope(exemptions, reviews):
    """Audit scope without silently changing the source's skip annotations.

    Include all current exemptions. A missing/stale decision remains unreviewed;
    source hashes cover the surrounding proof/citation on which the review rests.
    """
    by_id = {item["id"]: dict(item, decision="unreviewed") for item in exemptions}
    seen, stale = set(), []
    for review in reviews:
        ident = review["id"]
        if ident in seen:
            raise ValueError(f"duplicate scope review: {ident}")
        seen.add(ident)
        if review.get("decision") not in {"exempt", "in_scope", "structural"} or not review.get("reason"):
            raise ValueError(f"invalid scope review: {ident}")
        item = by_id.get(ident)
        if item is None or any(item[key] != review.get(key) for key in ("passageSha256", "sourceSha256")):
            stale.append(ident)
            continue
        item.update(decision=review["decision"], reason=review["reason"])
    return {
        "items": list(by_id.values()),
        "staleReviews": stale,
        "summary": {
            kind: dict(Counter(i["decision"] for i in by_id.values() if i["kind"] == kind))
            for kind in ("statement", "proof", "prose")
        },
    }


def scope_markdown(review):
    labels = {"exempt": "除外維持", "in_scope": "対象に戻す", "structural": "段落集計から除く", "unreviewed": "未判定"}
    out = [
        "# 形式化対象外の妥当性レビュー",
        "",
        f"現行の対象外指定に含まれる主張{sum(review['summary']['statement'].values())}件・証明段落{sum(review['summary']['proof'].values())}件・通常本文{sum(review['summary']['prose'].values())}件の確認状況。本文と前後の文脈に照らして判定する。",
        "未判定の通常本文も省略せず列挙する。引用部分と局所的な証明が混在する場合は引用部分だけを除外する。下表は全体が除外された集計単位を数える。",
        "",
        "| 判定 | 主張 | 証明段落 | 通常本文 |",
        "|---|---:|---:|---:|",
    ]
    for key, label in labels.items():
        out.append(
            f"| {label} | {review['summary']['statement'].get(key, 0)} | {review['summary']['proof'].get(key, 0)} | {review['summary']['prose'].get(key, 0)} |"
        )
    out += [
        "",
        "対象に戻す判定は、本文で証明・構成・使用している局所部分についてのもの。混在する外部入力の再証明までは要求しない。",
        "他章の結果の純粋な再掲と、既存結果から新たな帰結を導く本文証明を区別する。exampleやremarkという環境名だけでは判断しない。",
        "標準的な背景、明示的な引用結果、証明を展開しない紹介は除外を維持する。未形式化であること自体は除外理由にしない。",
        "",
        "## 箇所別の判定",
        "",
    ]
    chapter = None
    for item in review["items"]:
        name = Path(item["source"]).stem
        if name != chapter:
            out += [f"### {name}", ""]
            chapter = name
        out.append(
            f"- **{labels[item['decision']]}** — `{item['kind']}` L{item['line']}–{item['endLine']}: "
            + item.get("reason", "対応する有効な判定がない。")
        )
    out += [
        "",
        "## 再確認",
        "",
        "判定は `coverage-scope-review.json` に保持する。本文段落または前後の文脈を含む章ファイルが変われば判定を失効させる。",
        "`python3 tools/booklink_audit.py --out build/coverage-audit` が全件の取りこぼしと失効を確認し、同ディレクトリに `scope-review.md` を出力する。",
        f"失効した判定: {len(review['staleReviews'])} 件。",
        "",
    ]
    return "\n".join(out)


def summarize(chapters, items, scope=None):
    total = defaultdict(Counter)
    for row in chapters:
        for kind, counts in row["baseline"].items():
            total[kind].update(counts)
    classifications = {
        kind: dict(Counter(i["status"] for i in items if i["kind"] == kind)) for kind in ("statement", "proof", "prose")
    }
    working = {}
    for kind in ("statement", "proof", "prose"):
        counts = total[kind]
        reviewed = classifications[kind]
        covered = counts.get("covered", 0)
        external = reviewed.get("external_scope", 0)
        deferred = reviewed.get("deferred_astra", 0)
        remaining = counts.get("partial", 0) + counts.get("uncovered", 0) - external - deferred
        if scope is not None:
            decisions = scope["summary"][kind]
            remaining += decisions.get("in_scope", 0) + decisions.get("unreviewed", 0)
        working[kind] = {
            "covered": covered,
            "remaining": remaining,
            "externalScope": external,
            "deferredAstra": deferred,
            "sourceExempt": counts.get("exempt", 0),
            "percent": 100 * covered / (covered + remaining) if covered + remaining else None,
        }
    return {"baseline": dict(total), "triage": classifications, "workingCoverage": working}


def reviewed_coverage(summary, scope):
    """Partition all units without treating an unchecked exclusion as justified."""
    result = {}
    for kind in ("statement", "proof", "prose"):
        links = summary["baseline"].get(kind, {})
        gaps = summary["triage"][kind]
        exclusions = scope["summary"][kind]
        result[kind] = {
            "covered": links.get("covered", 0),
            "justifiedExclusion": gaps.get("external_scope", 0) + exclusions.get("exempt", 0),
            "needsWork": sum(gaps.get(k, 0) for k in ("link_only", "proof_alignment", "formalization_required"))
            + exclusions.get("in_scope", 0),
            "deferred": gaps.get("deferred_astra", 0),
            "unreviewed": gaps.get("unreviewed", 0) + exclusions.get("unreviewed", 0),
            "structural": exclusions.get("structural", 0),
        }
    return result


def reviewed_coverage_markdown(counts):
    lines = [
        "## 判定反映後の区分",
        "",
        "正当な除外対象は、未リンク部分を引用・背景説明・読書案内と確認した段落と、除外指定を妥当と確認した段落の合計。",
        "対象内対応は、本文の skip 指定を除いた対象範囲にリンクが揃う段落。段落全体を形式化したという意味ではない。",
        "skip 指定のない部分対応段落は、残る未リンク部分がすべて対象外と確認された場合に正当な除外対象へ入れる。",
        "未確認・失効した判定は未判定、対象に戻すと判定した箇所は要対応とする。見出し等は構造要素として分ける。",
        "各区分は重複せず、合計は下のリンク集計の総数に一致する。",
        "",
        "| 種類 | 対象内対応 | 正当な除外対象 | 要対応 | 保留 | 未判定 | 構造要素 |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    keys = ("covered", "justifiedExclusion", "needsWork", "deferred", "unreviewed", "structural")
    for kind, row in counts.items():
        lines.append(f"| {kind} | " + " | ".join(str(row[k]) for k in keys) + " |")
    return lines


def statement_selector_issues(entries, root):
    """Report statement selectors that still fail to resolve exactly."""
    return [
        evidence(e, root)
        | {
            "actualBookLine": e["match"].get("startLine"),
            "excerpt": e["booklink"].get("excerpt", e["booklink"].get("title", "")),
        }
        for e in entries
        if e["booklink"].get("target") == "statement" and e["match"].get("status") != "matched"
    ]


def markdown(report):
    labels = {
        "link_only": "リンク追加・範囲修正だけで解消と確認",
        "proof_alignment": "既存証明と本文の対応修正が必要",
        "formalization_required": "定義・構成・証明の補完が必要",
        "external_scope": "正当な除外対象（引用・背景説明・読書案内）",
        "deferred_astra": "難しい証明をAstraへ移譲（未解決・作業分母から分離）",
        "unreviewed": "未判定（未証明とは数えない）",
    }
    s = report["summary"]
    out = [
        "# Lean対応の事前監査",
        "",
        "現行ソースのスナップショット。未リンクを未証明とみなさず、証明追加前の照合に使う。",
        "主張には定義も含む。証明段落は proof 環境内、通常本文はその外の非構造段落で、いずれも全件を集計する。",
        "",
        *reviewed_coverage_markdown(report["reviewedCoverage"]),
        "",
        "## 現行指定によるリンク集計",
        "",
        "下表は本文の現行の対象外指定による集計。対象外指定の妥当性は後述の監査で区別する。リンクがあること自体は証明内容の精読完了を意味しない。",
        "",
        "| 現行指定によるリンク集計 | 対象内対応 | 部分対応 | 未対応 | 除外指定あり |",
        "|---|---:|---:|---:|---:|",
    ]
    for kind in ("statement", "proof", "prose"):
        c = s["baseline"].get(kind, {})
        out.append(
            f"| {kind} | " + " | ".join(str(c.get(k, 0)) for k in ("covered", "partial", "uncovered", "exempt")) + " |"
        )
    out += [
        "",
        "## 作業対象の対応率",
        "",
        "外部引用・背景として確認した未リンク部分と、Todoに根拠を残したAstra移譲分を作業分母から分離する。",
        "Astra移譲は未解決であり、対応済みには加算しない。除外指定の未判定・対象に戻す箇所は残りに含める。",
        "",
        "| 種類 | 対応済み | 残り | 外部・背景 | Astra移譲 | 作業対象の対応率 |",
        "|---|---:|---:|---:|---:|---:|",
    ]
    for kind, c in s["workingCoverage"].items():
        percent = f"{c['percent']:.2f}%" if c["percent"] is not None else "—"
        out.append(
            f"| {kind} | {c['covered']} | {c['remaining']} | {c['externalScope']} | {c['deferredAstra']} | {percent} |"
        )
    if "scopeReview" in report:
        scope = report["scopeReview"]
        out += [
            "",
            "対象外指定の確認状況は下表に示す。[箇所別の判定](coverage-scope-review.md)を参照。",
            "対象に戻す判定には部分的な局所証明・既存結果の再利用も含むため、件数を新規証明の必要数とはみなさない。",
            "",
            "| 対象外指定の判定 | 主張 | 証明段落 | 通常本文 |",
            "|---|---:|---:|---:|",
        ]
        for key, label in (
            ("exempt", "除外維持が妥当"),
            ("in_scope", "対象に戻す部分あり"),
            ("structural", "見出し・導入文として段落数から除く"),
            ("unreviewed", "未判定"),
        ):
            out.append(
                f"| {label} | {scope['summary']['statement'].get(key, 0)} | {scope['summary']['proof'].get(key, 0)} | {scope['summary']['prose'].get(key, 0)} |"
            )
    out += ["", "| 未対応・部分対応の内訳 | 主張 | 証明段落 | 通常本文 |", "|---|---:|---:|---:|"]
    for status, label in labels.items():
        out.append(
            f"| {label} | {s['triage']['statement'].get(status, 0)} | {s['triage']['proof'].get(status, 0)} | {s['triage']['prose'].get(status, 0)} |"
        )
    pending = [i for i in report["items"] if i["status"] == "unreviewed"]
    with_candidates = sum(bool(i["direct"] or i["context"] or i.get("reviewedEvidence")) for i in pending)
    out += [
        "",
        "## 章別のリンク集計",
        "",
        "| 章 | 種類 | 完全対応 | 部分対応 | 未対応 | 除外指定あり |",
        "|---|---|---:|---:|---:|---:|",
    ]
    for chapter in report["chapters"]:
        for kind in ("statement", "proof", "prose"):
            counts = chapter["baseline"].get(kind, {})
            if counts:
                out.append(
                    f"| {Path(chapter['source']).stem} | {kind} | "
                    + " | ".join(str(counts.get(k, 0)) for k in ("covered", "partial", "uncovered", "exempt"))
                    + " |"
                )
    out += [
        "",
        "証明段落は target:proof に限らず、厳密一致する既存リンクをすべて集計する。",
        "`link_only` は既存の構成・仮定・結論を確認したもの。新しい証明を書かずにリンクを整備できる。",
        "`unreviewed` の近接する主張リンクは探索候補にすぎず、対応済みには加算しない。",
        f"未判定 {len(pending)} 件のうち {with_candidates} 件には直接・近接・手動記録の候補宣言がある。",
        "これは検索の出発点があるという意味で、リンク修正だけで解決すると確認した件数ではない。",
        "補完には既存補題を接続する短い証明や一般形の定義も含む。新しい定理の数や作業量を表す件数ではない。",
        "",
        f"未解決または弱一致の statement リンク: {len(report['statementSelectorIssues'])} 件。",
        "抜粋指定は、その抜粋を含む主張が一意に定まる場合だけリンクする。",
        "",
        "## 章別の内訳",
        "",
        "| 章 | 種類 | リンクのみ | 対応修正 | 補完 | 正当な除外対象 | Astra移譲 | 未判定 |",
        "|---|---|---:|---:|---:|---:|---:|---:|",
    ]
    for row in report["chapters"]:
        for kind in ("statement", "proof", "prose"):
            c = Counter(i["status"] for i in report["items"] if i["source"] == row["source"] and i["kind"] == kind)
            if c:
                out.append(f"| {Path(row['source']).stem} | {kind} | " + " | ".join(str(c[k]) for k in labels) + " |")
    out += ["", "## 未対応・部分対応の箇所", ""]
    for item in report["items"]:
        out.append(f"- `{item['source']}:{item['line']}–{item['endLine']}` ({item['kind']}, {item['baseline']}):")
        snippets = [gap["text"] for gap in item["gaps"]] or [cov.snippet_of(item["text"])]
        for snippet in snippets:
            out.append("  > " + " ".join(snippet.split()))
    out.append("")
    out += ["", "## 手動照合の根拠", ""]
    for item in report["items"]:
        if "reason" not in item:
            continue
        refs = ", ".join(f"`{e['source']}:{e.get('declaration', '')}`" for e in item.get("reviewedEvidence", []))
        out.append(f"- `{item['id']}` — **{labels[item['status']]}**。{item['reason']} {refs}")
    out += [
        "",
        "## 再集計",
        "",
        "```sh",
        "python3 tools/booklink_audit.py --out build/coverage-audit",
        "```",
        "",
        "全件の位置・本文・候補Lean宣言は同ディレクトリの report.json に保存する。",
        "手動判断は polish-space/coverage-review.json に保持し、本文または根拠ファイルが変われば再確認対象に戻す。",
        f"今回の失効した判断: {len(report['staleReviews'])} 件。",
        f"ソース指紋: `{report['sourceFingerprint']}`。",
        "",
    ]
    return "\n".join(out)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--manifest", default="polish-space/src/polish-space-book.json")
    parser.add_argument("--lean-root", default="polish-space/lean")
    parser.add_argument("--reviews", default="polish-space/coverage-review.json")
    parser.add_argument("--scope-reviews", default="polish-space/coverage-scope-review.json")
    parser.add_argument("--out", type=Path, default=Path("build/coverage-audit"))
    args = parser.parse_args(argv)
    try:
        return run_audit(args)
    except (OSError, ValueError) as exc:
        print(f"booklink_audit.py: {exc}", file=sys.stderr)
        return 2


def read_reviews(path):
    if not path.exists():
        return []
    data = json.loads(path.read_text(encoding="utf-8"))
    if (
        not isinstance(data, dict)
        or not isinstance(data.get("reviews"), list)
        or not all(isinstance(review, dict) for review in data["reviews"])
    ):
        raise AuditInputError(f"{path}: expected a reviews array")
    return data["reviews"]


def run_audit(args):
    root = args.root.resolve()
    files = sorted((root / args.lean_root).rglob("*.lean"))
    cov.check_decl_target_multiplicity(files)
    cache = bk.SourceCache()
    sm = bk.build_combined_sourcemap(root, files, cache=cache) if files else {"entries": [], "counts": {}}
    by_source = defaultdict(list)
    for entry in sm["entries"]:
        by_source[entry["match"].get("source")].append(entry)
    chapters, items, fingerprints, exemptions = [], [], {}, []
    manifest = root / args.manifest
    _master, chapter_paths = read_manifest(manifest)
    paths = [root / p for p in chapter_paths]
    for path in paths:
        baseline, gaps = scan_source(path, root, by_source[str(path)], exemptions, document=cache.document(path))
        chapters.append({"source": str(path.relative_to(root)), "baseline": baseline})
        items.extend(gaps)
    reviews_path = root / args.reviews
    reviews = read_reviews(reviews_path)
    stale = apply_reviews(items, reviews, root)
    scope_path = root / args.scope_reviews
    scope = review_scope(exemptions, read_reviews(scope_path))
    if scope_path.exists():
        fingerprints[str(scope_path.relative_to(root))] = digest(scope_path.read_text(encoding="utf-8"))
    for path in [
        manifest,
        *([reviews_path] if reviews_path.exists() else []),
        root / "tools/booklink_audit.py",
        root / "tools/formalization_annotations.py",
        root / "tools/book_manifest.py",
        root / "tools/booklink_coverage.py",
        root / "tools/booklink_sourcemap.py",
        *paths,
        *files,
    ]:
        fingerprints[str(path.relative_to(root))] = digest(cache.document(path).text)
    report = {
        "sourceFingerprint": digest(json.dumps(fingerprints, sort_keys=True)),
        "files": fingerprints,
        "chapters": chapters,
        "items": items,
        "summary": summarize(chapters, items, scope),
        "staleReviews": stale,
        "scopeReview": scope,
        "linkMatches": sm["counts"],
        "statementSelectorIssues": statement_selector_issues(sm["entries"], root),
    }
    report["reviewedCoverage"] = reviewed_coverage(report["summary"], scope)
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "report.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    (args.out / "report.md").write_text(markdown(report), encoding="utf-8")
    (args.out / "scope-review.md").write_text(scope_markdown(scope), encoding="utf-8")
    print(json.dumps(report["summary"], ensure_ascii=False, indent=2))
    print("Scope review:", json.dumps(scope["summary"], ensure_ascii=False))
    print(f"Stale scope reviews: {len(scope['staleReviews'])}")
    print(f"Stale reviews: {len(stale)}; full report: {args.out / 'report.md'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
