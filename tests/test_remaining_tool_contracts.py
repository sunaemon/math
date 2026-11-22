"""Real CLI/file contracts for the remaining infrastructure review findings."""

import contextlib
import io
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import booklink_coverage as coverage
import booklink_sourcemap as sourcemap
import check_translation_terms as terms
import check_translation_workflow as workflow
import po_diff
import prepare_pandoc_templates as templates
import project_translation_sourcemap as projection
import split_skip_blocks as split
import validate_afk_chart_limit as afk
from booklink_fixtures import lean_booklink

GETTEXT = all(shutil.which(name) for name in ("msgfmt", "msgcmp", "msgattrib", "msggrep"))
HEADER = "Project-Id-Version: tests\nPO-Revision-Date: 2026-01-01 00:00+0000\nLast-Translator: Test <test@example.invalid>\nLanguage-Team: tests\nLanguage: ja\nMIME-Version: 1.0\nContent-Type: text/plain; charset=UTF-8\nContent-Transfer-Encoding: 8bit\nPlural-Forms: nplurals=1; plural=0;\n"


def catalog(path, messages):
    path.parent.mkdir(parents=True, exist_ok=True)
    chunks = [f'msgid ""\nmsgstr {json.dumps(HEADER)}\n']
    for source, target, flags in messages:
        chunks.append(
            (f"#, {flags}\n" if flags else "")
            + f"msgid {json.dumps(source, ensure_ascii=False)}\nmsgstr {json.dumps(target, ensure_ascii=False)}\n"
        )
    path.write_text("\n".join(chunks), encoding="utf-8")


class RemainingToolContractTest(unittest.TestCase):
    def test_source_map_coverage_and_translation_projection_clis(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            source = root / "english/src/chapter.md"
            target = root / "japanese/src/chapter.md"
            text = "# Title {#sec:chapter}\n\nA fact.\n\n\\begin{lemma*}[Unlinked]\nMissing fact.\n\\end{lemma*}\n"
            for path, content in [(source, text), (target, text.replace("A fact.", "事実である．"))]:
                path.parent.mkdir(parents=True)
                path.write_text(content, encoding="utf-8")
                path.with_name("book.json").write_text(
                    json.dumps({"source": str(path.with_name("book.md")), "chapters": [str(path)]}), encoding="utf-8"
                )
            lean = root / "english/lean/Chapter.lean"
            lean.parent.mkdir()
            lean.write_text(
                lean_booklink("prose", source="chapter.md", excerpt="A fact.") + "\ntheorem fact : True := trivial\n",
                encoding="utf-8",
            )
            output = root / "output/map.json"
            with contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(
                    sourcemap.main(
                        ["sourcemap", "--root", str(root), "--out", "output/map.json", "english/lean/Chapter.lean"]
                    ),
                    0,
                )
            data = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(data["entryCount"], 1)
            self.assertEqual(data["entries"][0]["match"]["status"], "matched")
            with contextlib.redirect_stdout(io.StringIO()) as report:
                self.assertEqual(
                    coverage.main(["coverage", "--root", str(root), "--strict", "--json", "english/lean/Chapter.lean"]),
                    1,
                )
            self.assertEqual(json.loads(report.getvalue())[0]["statements"]["uncovered"], 1)
            po = root / "po/chapter.po"
            catalog(po, [("A fact.", "事実である．", "")])
            translated_map = root / "output/ja-map.json"
            args = [
                "--source-map",
                str(output),
                "--source-manifest",
                str(source.with_name("book.json")),
                "--translation-manifest",
                str(target.with_name("book.json")),
                "--po-dir",
                str(po.parent),
                "--out",
                str(translated_map),
            ]
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(projection.main(args), 0)
            match = json.loads(translated_map.read_text(encoding="utf-8"))["entries"][0]["match"]
            self.assertEqual(match["source"], str(target))
            self.assertEqual(
                target.read_text(encoding="utf-8")[match["startOffset"] : match["endOffset"]], "事実である．"
            )
            output.write_text("[]", encoding="utf-8")
            with contextlib.redirect_stderr(io.StringIO()) as errors:
                self.assertEqual(projection.main(args), 1)
            self.assertIn("source map root must be an object", errors.getvalue())

    @unittest.skipUnless(GETTEXT, "GNU gettext is required for catalog integration")
    def test_real_catalog_comparison_and_completeness_checks(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            po, pot, refreshed = [root / name for name in ("chapter.po", "chapter.pot", "refreshed.po")]
            messages = [("First.", "第一．", ""), ("Second.", "第二．", "")]
            catalog(po, messages)
            catalog(pot, [(source, "", "") for source, _, _ in messages])
            catalog(refreshed, list(reversed(messages)))
            workflow._compare_message_sets(root, po, refreshed)
            for changed in (messages[:1], messages + [("Extra.", "追加．", "")]):
                catalog(refreshed, changed)
                with self.assertRaises(workflow.TranslationCheckError):
                    workflow._compare_message_sets(root, po, refreshed)
            chapter = workflow.Chapter("chapter.md", root / "source.md", root / "ja.md", po, pot, "unused")
            workflow._check_catalogs(root, [chapter])
            for bad, message in [
                ([("First.", "第一．", "fuzzy")], "fuzzy"),
                ([("First.", "", "")], "empty 'msgstr'|untranslated"),
            ]:
                catalog(po, bad)
                with self.assertRaisesRegex(workflow.TranslationCheckError, message):
                    workflow._check_catalogs(root, [chapter])

    @unittest.skipUnless(
        GETTEXT and shutil.which("pandoc"), "GNU gettext and Pandoc are required for workflow integration"
    )
    def test_workflow_and_terminology_clis_use_real_checks(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            source = root / "english/chapter.md"
            source.parent.mkdir()
            source.write_text("A fact.\n", encoding="utf-8")
            l10n = root / "l10n"
            po, pot = l10n / "ja/chapter.po", l10n / "pot/chapter.pot"
            catalog(po, [("A fact.", "事実である．", "")])
            catalog(pot, [("A fact.", "", "")])
            glossary = l10n / "glossary-ja.yaml"
            glossary.write_text(
                json.dumps(
                    {
                        "version": 1,
                        "language": "ja",
                        "terms": [
                            {
                                "id": "fact",
                                "english": "fact",
                                "japanese": "事実",
                                "status": "approved",
                                "avoid": ["誤記"],
                            }
                        ],
                    },
                    ensure_ascii=False,
                ),
                encoding="utf-8",
            )
            status = l10n / "status.json"
            status.write_text(
                json.dumps(
                    {
                        "language": "ja",
                        "chapters": {
                            "chapter.md": {"source": "english/chapter.md", "sourceBlob": workflow.git_blob_hash(source)}
                        },
                    }
                ),
                encoding="utf-8",
            )
            config = root / "po4a.cfg"
            config.write_text(
                "[type: book-markdown] $(source)/chapter.md $lang:$(output)/chapter.md\n", encoding="utf-8"
            )
            # The external renderer is a bounded contract fake. All catalog,
            # glossary, structure and CLI checks here run their real code/tools;
            # the repository lint separately exercises the installed po4a.
            renderer = root / "render-po4a"
            renderer.write_text(
                f"#!{sys.executable}\nimport pathlib, shutil, sys\nvalues=dict(arg.split('=',1) for arg in sys.argv if arg.startswith(('l10n=','output=')))\nshutil.copyfile({str(pot)!r}, pathlib.Path(values['l10n'])/'pot/chapter.pot')\n(pathlib.Path(values['output'])/'chapter.md').write_text('事実である．\\n',encoding='utf-8')\n",
                encoding="utf-8",
            )
            renderer.chmod(0o755)
            translated = root / "translated"
            args = [
                "--repo-root",
                str(root),
                "--po4a",
                str(renderer),
                "--config",
                str(config),
                "--l10n-dir",
                str(l10n),
                "--translated-dir",
                str(translated),
                "--status",
                str(status),
            ]
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(workflow.main([*args, "--write-generated"]), 0)
                self.assertEqual(workflow.main(args), 0)
                self.assertEqual(terms.main(["--glossary", str(glossary), str(po)]), 0)
            self.assertEqual((translated / "chapter.md").read_text(encoding="utf-8"), "事実である．\n")
            catalog(po, [("A fact.", "誤記", "")])
            with contextlib.redirect_stderr(io.StringIO()) as errors:
                self.assertEqual(terms.main(["--glossary", str(glossary), str(po)]), 1)
                self.assertEqual(workflow.main(args), 1)
            self.assertIn("avoid", errors.getvalue())

    def test_skip_narrowing_and_po_textconv_use_real_input(self):
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "chapter.md"
            marker = "<!-- formalization: skip (external context) -->"
            lead = "External context before the linked passage is deliberately long."
            body = "Covered fact."
            trail = "Trailing external context after the linked passage is also long."
            text = f"{marker}\n{lead}\n{body}\n{trail}\n"
            path.write_text(text, encoding="utf-8")
            start = text.index(body)
            output, notes = split.process_source(path, [(start, start + len(body))])
            self.assertEqual(output, marker + "\n" + lead + "\n\n" + body + "\n\n" + marker + "\n" + trail + "\n")
            self.assertTrue(any("lead-skip+in-scope+trail-skip" in note for note in notes))
            path.write_text('#: source.md:12 other.md:34\nmsgid "section:56"\n', encoding="utf-8")
            with contextlib.redirect_stdout(io.StringIO()) as converted:
                self.assertEqual(po_diff.main([str(path)]), 0)
            self.assertEqual(converted.getvalue(), '#: source.md other.md\nmsgid "section:56"\n')

    @unittest.skipUnless(shutil.which("pandoc"), "Pandoc is required for template preparation")
    def test_template_preparation_cli_copies_reviewed_overrides(self):
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary)
            with patch.object(sys, "argv", ["prepare", "--output", str(out), "--pandoc", shutil.which("pandoc")]):
                templates.main()
            self.assertIn("$if(native-captions)$", (out / "templates/common.latex").read_text(encoding="utf-8"))
            for name in ("font-settings.latex", "fonts.latex"):
                original = ROOT / "tools/pandoc/templates" / name
                if original.exists():
                    self.assertEqual((out / "templates" / name).read_bytes(), original.read_bytes())

    def test_afk_prepare_validates_pins_and_stages_adapter_without_network(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "afk"
            source.mkdir()
            (source / "lean-toolchain").write_text(afk.TOOLCHAIN, encoding="utf-8")
            (source / "lake-manifest.json").write_text('{"packages": []}', encoding="utf-8")
            original = 'name = "Fixture"\n'
            (source / "lakefile.toml").write_text(original, encoding="utf-8")
            for rel in (
                "polish-space/lean/PolishSpaceBook/ChartAmalgamation.lean",
                "polish-space/vendor/afk-validation/ChartClass.lean",
            ):
                path = root / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("-- fixture " + path.name, encoding="utf-8")
            with (
                patch.object(afk, "ROOT", root),
                patch.object(sys, "argv", ["afk", "--source-dir", str(source), "--prepare-only"]),
                patch.object(afk, "run", return_value=afk.REVISION),
                patch.object(afk.subprocess, "check_output", return_value=original),
            ):
                afk.main()
            self.assertEqual(
                (source / "BookAFK/ChartClass.lean").read_text(encoding="utf-8"), "-- fixture ChartClass.lean"
            )
            expected = (
                original
                + '\n[[lean_lib]]\nname = "BookAFK"\nglobs = ["BookAFK.*"]\nleanOptions = { warningAsError = true }\n'
            )
            self.assertEqual((source / "lakefile.toml").read_text(encoding="utf-8"), expected)
            with (
                patch.object(sys, "argv", ["afk", "--source-dir", str(source), "--prepare-only"]),
                patch.object(afk, "run", return_value="wrong-revision"),
                self.assertRaisesRegex(SystemExit, "pinned revision"),
            ):
                afk.main()
