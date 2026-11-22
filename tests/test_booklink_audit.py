"""Prevent link bookkeeping and search leads from becoming proof claims."""

import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import booklink_audit as audit


class AuditCliTest(unittest.TestCase):
    def test_missing_optional_reviews_and_no_lean_files_still_report_gaps(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            tools = root / "tools"
            tools.mkdir()
            for name in (
                "booklink_audit",
                "booklink_coverage",
                "booklink_sourcemap",
                "book_manifest",
                "formalization_annotations",
            ):
                shutil.copyfile(Path(audit.__file__).parent / f"{name}.py", tools / f"{name}.py")
            source = root / "book/src/chapter.md"
            source.parent.mkdir(parents=True)
            source.write_text(
                "\\begin{lemma*}[Claim]\nA mathematical claim.\n\\end{lemma*}\n\nOrdinary claim.\n", encoding="utf-8"
            )
            manifest = source.with_name("book.json")
            manifest.write_text(json.dumps({"source": "book/src/book.md", "chapters": ["book/src/chapter.md"]}))
            command = [
                sys.executable,
                str(tools / "booklink_audit.py"),
                "--root",
                str(root),
                "--manifest",
                "book/src/book.json",
                "--lean-root",
                "book/lean",
                "--reviews",
                "book/reviews.json",
                "--scope-reviews",
                "book/scope-reviews.json",
                "--out",
                str(root / "report"),
            ]
            result = subprocess.run(command, capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 0, result.stderr)
            report = json.loads((root / "report/report.json").read_text())
            self.assertEqual(len(report["items"]), 2)
            self.assertEqual(report["items"][0]["status"], "unreviewed")
            self.assertEqual(report["staleReviews"], [])
            self.assertEqual(report["summary"]["baseline"]["prose"]["uncovered"], 1)
            markdown = (root / "report/report.md").read_text()
            self.assertIn("Ordinary claim.", markdown)
            previous_columns = None
            for line in markdown.splitlines():
                if line.startswith("|"):
                    columns = line.count("|")
                    if previous_columns is not None:
                        self.assertEqual(columns, previous_columns)
                    previous_columns = columns
                else:
                    previous_columns = None
            manifest.write_text(json.dumps({"source": "book/src/book.md", "chapters": "invalid"}))
            result = subprocess.run(command, capture_output=True, text=True, check=False)
            self.assertEqual(result.returncode, 2)
            self.assertIn("chapters must be a list of strings", result.stderr)
            self.assertNotIn("Traceback", result.stderr)


class AuditTest(unittest.TestCase):
    def scan(self, text, specs=()):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "chapter.md"
            path.write_text(text)
            entries = []
            for excerpt, target, status in specs:
                start = text.index(excerpt)
                entries.append(
                    {
                        "booklink": {"target": target},
                        "match": {"status": status, "startOffset": start, "endOffset": start + len(excerpt)},
                        "lean": {"source": str(root / "proof.lean"), "declName": "existing"},
                    }
                )
            return audit.scan_source(path, root, entries)

    def test_part_heading_is_structural_but_following_prose_remains_in_scope(self):
        counts, gaps = self.scan("\\part{Part II}\\label{part-two}\n\nActual mathematical claim.\n")
        self.assertEqual(counts["prose"]["uncovered"], 1)
        self.assertEqual(len(gaps), 1)
        self.assertIn("Actual mathematical claim", gaps[0]["text"])

    def test_heading_without_blank_line_does_not_make_covered_prose_partial(self):
        text = "## Heading\nActual mathematical claim.\n"
        counts, gaps = self.scan(text, [("Actual mathematical claim.", "prose", "matched")])
        self.assertEqual(counts["prose"]["covered"], 1)
        self.assertFalse(gaps)
        counts, gaps = self.scan(text, [("Actual", "prose", "matched")])
        self.assertEqual(counts["prose"]["partial"], 1)
        self.assertIn("mathematical claim", gaps[0]["gaps"][0]["text"])

    def test_ordinary_prose_partial_and_unlinked_units_are_reported(self):
        text = "# Heading\n\nDefinition. Such f sends classes injectively.\n\nAnother claim.\n"
        counts, gaps = self.scan(text, [("Definition.", "prose", "matched")])
        self.assertEqual(counts["prose"]["partial"], 1)
        self.assertEqual(counts["prose"]["uncovered"], 1)
        self.assertEqual([gap["kind"] for gap in gaps], ["prose", "prose"])
        self.assertIn("Such f sends", gaps[0]["gaps"][0]["text"])
        self.assertEqual(gaps[1]["text"].strip(), "Another claim.")

    def test_prose_link_inside_proof_is_not_a_new_proof_gap(self):
        text = "\\begin{proof}\n\nA mathematical argument.\n\n\\end{proof}\n"
        counts, gaps = self.scan(text, [("A mathematical argument.", "prose", "matched")])
        self.assertEqual(counts["proof"]["covered"], 1)
        self.assertFalse(gaps)

    def test_preceding_theorem_only_supplies_a_candidate(self):
        statement = "\\begin{theorem*}[Claim]\nA statement.\n\\end{theorem*}"
        text = statement + "\n\n\\begin{proof}\nAn argument.\n\\end{proof}\n"
        _, gaps = self.scan(text, [(statement, "statement", "matched")])
        self.assertEqual(len(gaps), 1)
        self.assertEqual(gaps[0]["status"], "unreviewed")
        self.assertTrue(gaps[0]["context"])
        self.assertFalse(gaps[0]["direct"])

    def test_partial_prose_does_not_recover_whole_paragraph(self):
        text = "\\begin{proof}\nFirst fact. Second fact.\n\\end{proof}\n"
        _, gaps = self.scan(text, [("First fact.", "prose", "matched")])
        self.assertEqual(gaps[0]["status"], "unreviewed")
        self.assertEqual(gaps[0]["anyLink"], "partial")

    def test_weak_match_is_not_confirmed_recovery(self):
        text = "\\begin{proof}\nA fact.\n\\end{proof}\n"
        _, gaps = self.scan(text, [("A fact.", "prose", "weak")])
        self.assertEqual(gaps[0]["status"], "unreviewed")

    def test_mixed_targets_can_jointly_cover_a_paragraph(self):
        text = "\\begin{proof}\nFirst fact. Second fact.\n\\end{proof}\n"
        counts, gaps = self.scan(text, [("First fact.", "proof", "matched"), ("Second fact.", "prose", "matched")])
        self.assertEqual(counts["proof"]["covered"], 1)
        self.assertFalse(gaps)

    def test_unlinked_source_is_included(self):
        counts, gaps = self.scan("\\begin{lemma*}\nUnlinked.\n\\end{lemma*}\n")
        self.assertEqual(counts["statement"]["uncovered"], 1)
        self.assertEqual(len(gaps), 1)

    def test_nested_proofs_count_each_paragraph_once(self):
        text = "\\begin{proof}\n\nOuter.\n\n\\begin{proof}\n\nInner.\n\n\\end{proof}\n\nOuter again.\n\n\\end{proof}\n"
        counts, gaps = self.scan(text)
        self.assertEqual(counts["proof"]["uncovered"], 3)
        self.assertEqual(len(gaps), 3)
        self.assertEqual(len(audit.proof_ranges(text)), 2)
        with self.assertRaises(ValueError):
            audit.proof_ranges("\\begin{proof}")

    def test_stale_passage_or_evidence_is_not_promoted(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            p = root / "proof.lean"
            p.write_text("Original proof")
            review = {
                "id": "unit",
                "status": "link_only",
                "reason": "Reviewed",
                "passageSha256": audit.digest("passage"),
                "evidence": [{"source": "proof.lean", "sha256": audit.digest(p.read_text())}],
            }
            item = {"id": "unit", "status": "unreviewed", "passageSha256": audit.digest("passage")}
            self.assertFalse(audit.apply_reviews([item.copy()], [review], root))
            changed = item | {"passageSha256": audit.digest("changed")}
            self.assertEqual(audit.apply_reviews([changed], [review], root), ["unit"])
            self.assertEqual(changed["status"], "unreviewed")
            p.write_text("Changed proof")
            self.assertEqual(audit.apply_reviews([item], [review], root), ["unit"])
            self.assertEqual(item["status"], "unreviewed")

    def test_astra_handoff_requires_live_todo_and_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "proof.lean").write_text("candidate")
            (root / "todo.md").write_text("- ASTRA-001: missing construction")
            review = {
                "id": "unit",
                "status": "deferred_astra",
                "reason": "construction remains",
                "todoItem": "ASTRA-001: missing construction",
                "passageSha256": "p",
                "evidence": [{"source": "proof.lean", "sha256": audit.digest("candidate")}],
            }
            item = {"id": "unit", "status": "unreviewed", "passageSha256": "p"}
            active = item.copy()
            self.assertEqual(audit.apply_reviews([active], [review], root), [])
            self.assertEqual(active["status"], "deferred_astra")
            (root / "todo.md").write_text("Task removed")
            self.assertEqual(audit.apply_reviews([item.copy()], [review], root), ["unit"])
            with self.assertRaises(ValueError):
                audit.apply_reviews([item], [review | {"evidence": []}], root)

    def test_working_coverage_separates_deferred_without_counting_it_as_proved(self):
        chapters = [{"baseline": {"prose": {"covered": 3, "partial": 1, "uncovered": 3, "exempt": 2}}}]
        items = [
            {"kind": "prose", "status": status}
            for status in ["deferred_astra", "external_scope", "formalization_required", "unreviewed"]
        ]
        summary = audit.summarize(chapters, items)
        self.assertEqual(summary["baseline"]["prose"]["uncovered"], 3)
        self.assertEqual(
            summary["workingCoverage"]["prose"],
            {
                "covered": 3,
                "remaining": 2,
                "externalScope": 1,
                "deferredAstra": 1,
                "sourceExempt": 2,
                "percent": 60.0,
            },
        )

    def test_unresolved_statement_selector_is_reported(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            # Selector validation is lexical; this fixture deliberately has no proof file.
            entry = {
                "booklink": {"target": "statement", "excerpt": "The intended theorem"},
                "match": {"status": "unresolved", "startLine": 200},
                "lean": {"source": str(root / "proof.lean")},
            }
            issues = audit.statement_selector_issues([entry], root)
            self.assertEqual(len(issues), 1)
            self.assertEqual(issues[0]["actualBookLine"], 200)
            entry["match"]["status"] = "matched"
            self.assertFalse(audit.statement_selector_issues([entry], root))

    def test_reviewed_categories_partition_units_and_retain_unchecked_skips(self):
        chapters = [{"baseline": {"prose": {"covered": 3, "partial": 1, "uncovered": 3, "exempt": 5}}}]
        items = [
            {"kind": "prose", "status": status}
            for status in ["external_scope", "formalization_required", "deferred_astra", "unreviewed"]
        ]
        scope = {
            "summary": {
                "statement": {},
                "proof": {},
                "prose": {"exempt": 2, "in_scope": 1, "unreviewed": 1, "structural": 1},
            }
        }
        summary = audit.summarize(chapters, items, scope)
        counts = audit.reviewed_coverage(summary, scope)["prose"]
        self.assertEqual(
            counts,
            {"covered": 3, "justifiedExclusion": 3, "needsWork": 2, "deferred": 1, "unreviewed": 2, "structural": 1},
        )
        self.assertEqual(sum(counts.values()), 12)
        self.assertEqual(summary["workingCoverage"]["prose"]["remaining"], 4)


class ScopeReviewTest(unittest.TestCase):
    def entry(self, ident="unit"):
        return {"id": ident, "kind": "proof", "passageSha256": "passage", "sourceSha256": "context"}

    def decision(self, **changes):
        return self.entry() | {"decision": "in_scope", "reason": "A local proof"} | changes

    def test_scope_review_does_not_rewrite_original_coverage(self):
        item = self.entry() | {"originalReason": "skip"}
        result = audit.review_scope([item], [self.decision()])
        self.assertEqual(result["summary"]["proof"], {"in_scope": 1})
        self.assertEqual(result["items"][0]["originalReason"], "skip")
        self.assertNotIn("decision", item)
        self.assertFalse(result["staleReviews"])

    def test_unreviewed_entries_are_not_silently_retained(self):
        result = audit.review_scope([self.entry(), self.entry("other")], [self.decision()])
        self.assertEqual(result["summary"]["proof"], {"in_scope": 1, "unreviewed": 1})

    def test_changed_context_or_passage_expires_decision(self):
        for key in ("sourceSha256", "passageSha256"):
            result = audit.review_scope([self.entry() | {key: "changed"}], [self.decision()])
            self.assertEqual(result["staleReviews"], ["unit"])
            self.assertEqual(result["items"][0]["decision"], "unreviewed")

    def test_duplicate_invalid_and_removed_decisions(self):
        with self.assertRaises(ValueError):
            audit.review_scope([self.entry()], [self.decision(), self.decision()])
        with self.assertRaises(ValueError):
            audit.review_scope([self.entry()], [self.decision(decision="done")])
        self.assertEqual(audit.review_scope([], [self.decision()])["staleReviews"], ["unit"])

    def test_scan_collects_excluded_proof_paragraph(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            p = root / "chapter.md"
            p.write_text(
                "<!-- formalization: skip-begin (external) -->\n"
                "\\begin{proof}\nAn argument.\n\\end{proof}\n"
                "<!-- formalization: skip-end -->\n"
            )
            exclusions = []
            counts, gaps = audit.scan_source(p, root, [], exclusions)
            self.assertEqual(counts["proof"]["exempt"], 1)
            self.assertFalse(gaps)
            self.assertEqual(len(exclusions), 1)
            self.assertEqual(exclusions[0]["originalReason"], "external")
            self.assertEqual(exclusions[0]["sourceSha256"], audit.digest(p.read_text()))


if __name__ == "__main__":
    unittest.main()
