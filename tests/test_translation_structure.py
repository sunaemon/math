"""Tests for the Markdown translation-structure checker.

Run with ``python -m unittest``.  The checker itself uses only the standard
library and is intended to run before translated chapters enter a book build.
"""

from __future__ import annotations

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "tools"))

import check_translation_structure as checker

SOURCE = r"""# Source {#sec:source .unnumbered}

<!-- formalization: skip (source prose) -->
English text cites [@Reference2024] and uses $X \IncludedIn Y$.

\begin{mathmeta}
  \forward{ExampleNotation}
\end{mathmeta}

## Result {#sec:result}

\begin{theorem*}[\termdefineas{canonical theorem}{English title}]
The display is
$$
f(x)=x.
$$
\end{theorem*}

Later use \termuse{canonical theorem}.
\label{raw-result}
\part{English part title}
\printindex
"""


TRANSLATION = r"""# 翻訳 {#sec:source .unnumbered}

<!-- formalization: skip (日本語の説明) -->
日本語の本文では $X \IncludedIn Y$ を用い、[@Reference2024] を参照する。

\begin{mathmeta}
  \forward{ExampleNotation}
\end{mathmeta}

## 結果 {#sec:result}

\begin{theorem*}[\termdefineas{canonical theorem}{日本語の定理名}]
次の式を考える。
$$
f(x)=x.
$$
\end{theorem*}

後で \termuseas{canonical theorem}{この定理} を使う。
\label{raw-result}
\part{日本語の部題}
\printindex
"""


class ComparisonTest(unittest.TestCase):
    def test_identical_file_passes(self):
        self.assertEqual(checker.compare_texts(SOURCE, SOURCE), [])

    def test_translated_prose_and_display_arguments_pass(self):
        self.assertEqual(checker.compare_texts(SOURCE, TRANSLATION), [])

    def test_raw_tex_fences_preserve_checks(self):
        source = r"\begin{proof} $x=y$ \label{p} \termuse{term} \end{proof}"
        for language in ("latex", "tex"):
            for fence in ("```", "~~~~"):
                with self.subTest(language=language, fence=fence):
                    wrapped = f"{fence}{{={language}}}\n{source}\n{fence}\n"
                    self.assertEqual(checker.compare_texts(source, wrapped), [])
                    self.assertTrue(checker.compare_texts(source, wrapped.replace("x=y", "x=z")))
                    self.assertTrue(checker.compare_texts(source, wrapped.replace(r"\label{p}", "")))

    def test_ordinary_code_fences_still_ignore_tex_examples(self):
        example = "```latex\n" + r"\begin{proof} $x=y$ \end{proof}" + "\n```\n"
        self.assertEqual(checker.compare_texts("", example), [])

    def test_every_structural_category_reports_its_first_difference(self):
        # Public diagnostics distinguish which invariant failed; a different
        # detector reporting an unrelated error must not satisfy this test.
        replacements = {
            "headings": ("# 翻訳 {#sec:source .unnumbered}", "### 翻訳 {#sec:changed .unnumbered}"),
            "LaTeX labels": (r"\label{raw-result}", r"\label{changed-result}"),
            "citations": ("@Reference2024", "@DifferentReference"),
            "mathmeta directives": (r"\forward{ExampleNotation}", r"\define{ExampleNotation}"),
            "LaTeX environments": (r"\begin{theorem*}", r"\begin{lemma*}"),
            "formalization markers": ("formalization: skip", "formalization: require"),
            "part/index controls": (r"\printindex", ""),
            "mathematics": ("f(x)=x.", "f(x)=0."),
            "term identities": ("canonical theorem", "changed theorem"),
        }
        for category, (old, new) in replacements.items():
            with self.subTest(category=category):
                changed = TRANSLATION.replace(old, new, 1)
                diagnostics = checker.compare_texts(SOURCE, changed)
                self.assertTrue(any(item.startswith(category) for item in diagnostics), diagnostics)

    def test_as_variants_have_the_same_canonical_identity(self):
        source = r"\termdefine{alpha} \termforward{beta} \termref{gamma}"
        translation = (
            r"\termdefineas{alpha}{アルファ} "
            r"\termforwardas{beta}{ベータ} "
            r"\termref{gamma}"
        )
        self.assertEqual(checker.compare_texts(source, translation), [])

    def test_marker_movement_across_an_environment_is_reported(self):
        source = "<!-- formalization: skip -->\n\\begin{proof}\n\\end{proof}\n"
        translation = "\\begin{proof}\n\\end{proof}\n<!-- formalization: skip -->\n"
        diagnostics = checker.compare_texts(source, translation)
        self.assertTrue(any(item.startswith("structural ordering") for item in diagnostics), diagnostics)

    def test_math_in_term_aliases_checks_display_and_identity_separately(self):
        for operation in ("define", "use", "forward"):
            with self.subTest(operation=operation):
                source = rf"\term{operation}{{$a_{{n}}$-property}}"
                target = rf"\term{operation}as{{$a_{{n}}$-property}}{{$a_{{n}}$の性質}}"
                self.assertEqual(checker.compare_texts(source, target), [])
                changed_display = target.replace("{$a_{n}$の性質}", "{$a_{m}$の性質}")
                diagnostics = checker.compare_texts(source, changed_display)
                self.assertTrue(any(item.startswith("mathematics") for item in diagnostics), diagnostics)
                changed_key = target.replace("$a_{n}$-property", "$a_{m}$-property")
                diagnostics = checker.compare_texts(source, changed_key)
                self.assertTrue(any(item.startswith("term identities") for item in diagnostics), diagnostics)

    def test_hidden_term_math_preserves_display_locations(self):
        text = "\\termdefineas{\n$a_{n}$-property\n}{\n$a_{n}$の性質}\n$y$"
        formulas = checker.snapshot(text).mathematics
        self.assertEqual([item.line for item in formulas], [4, 5])
        self.assertEqual([text[item.offset] for item in formulas], ["$", "$"])
        self.assertEqual(checker.snapshot(r"\termref{$a_n$-property}").mathematics, [])

    def test_math_added_to_plain_term_display_is_still_rejected(self):
        source = r"\termdefine{property}"
        target = r"\termdefineas{property}{$x$の性質}"
        diagnostics = checker.compare_texts(source, target)
        self.assertTrue(any(item.startswith("mathematics") for item in diagnostics), diagnostics)

    def test_code_and_ordinary_comments_are_ignored(self):
        source = """```tex
# Fake {#wrong}
\\label{wrong}
$wrong$
```
`@InlineCitation` <!-- $hidden$ \\label{hidden} -->
"""
        translation = """```tex
arbitrary translated example
```
`別の例` <!-- arbitrary translated note -->
"""
        self.assertEqual(checker.compare_texts(source, translation), [])

    def test_standalone_equation_environment_payload_is_checked(self):
        source = "\\begin{equation*}\nx+y=z\n\\end{equation*}\n"
        translation = "\\begin{equation*}\nx-y=z\n\\end{equation*}\n"
        diagnostics = checker.compare_texts(source, translation)
        self.assertTrue(any(item.startswith("mathematics") for item in diagnostics), diagnostics)

    def test_math_source_wrapping_is_ignored(self):
        source = "$x +\n  y = z$\n"
        translation = "$x + y = z$\n"
        self.assertEqual(checker.compare_texts(source, translation), [])

    def test_math_prose_can_be_translated_and_moved(self):
        source = r"$$h(b)=\text{the unique point of }\bigcap_n U_n.$$"
        target = r"$$h(b)=\bigcap_n U_n\text{ の唯一の点}.$$"
        self.assertEqual(checker.compare_texts(source, target), [])
        self.assertTrue(checker.compare_texts(source, target.replace(r"\bigcap", r"\bigcup")))

    def test_math_prose_does_not_hide_symbols_or_embedded_math(self):
        for before, after in [
            (r"\text{I}", r"\text{E}"),
            (r"\text{Borel}", r"\text{Suslin}"),
            (r"\text{(i)}", r"\text{(ii)}"),
            (r"\text{n=1}", r"\text{n=2}"),
            (r"\text{case $x=1$}", r"\text{case $x=2$}"),
            (r"\text{\emph{label}}", r"\text{\emph{other}}"),
            (r"\operatorname{ind}", r"\operatorname{Ind}"),
            (r"\in X", r"\inX"),
        ]:
            with self.subTest(before=before):
                self.assertNotEqual(checker.normalize_math(before), checker.normalize_math(after))

    def test_prose_may_reorder_math_terms_and_citations(self):
        source = r"Use \termuse{alpha} at $x$ before [@First; @Second] and $y$."
        translation = (
            r"$y$ と [@Second; @First] を先に述べ、$x$ で "
            r"\termuseas{alpha}{アルファ} を用いる。"
        )
        self.assertEqual(checker.compare_texts(source, translation), [])


class CommandLineTest(unittest.TestCase):
    def test_cli_returns_nonzero_with_concise_diagnostic(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source.md"
            translation = root / "translation.md"
            source.write_text("# A {#sec:a}\n", encoding="utf-8")
            translation.write_text("# A {#sec:b}\n", encoding="utf-8")
            error = io.StringIO()
            with contextlib.redirect_stderr(error):
                result = checker.main([str(source), str(translation)])
        self.assertEqual(result, 1)
        self.assertIn("headings item 1", error.getvalue())
        self.assertIn("source line 1", error.getvalue())
        self.assertIn("translation line 1", error.getvalue())


class StructureBoundaryTest(unittest.TestCase):
    def test_optional_citation_arguments_and_sentence_punctuation(self):
        source = r"See \cite[Chapter 2]{knuth84} and \citep[see][p. 5]{lamport94}. @key.part. @other:"
        translated = r"\cite{knuth84}、\cite{lamport94}、@key.part。@other。"
        self.assertEqual(checker.compare_texts(source, translated), [])
        self.assertTrue(checker.compare_texts(source, translated.replace("knuth84", "missing")))

    def test_code_spans_close_only_on_a_complete_equal_length_run(self):
        text = "`before `` @hidden `` after` @visible."
        snapshot = checker.snapshot(text)
        self.assertEqual([item.value for item in snapshot.citations], ["visible"])

    def test_unclosed_yaml_is_a_parse_error(self):
        with self.assertRaisesRegex(checker.StructureParseError, "YAML"):
            checker.snapshot("---\ntitle: broken\n# not a heading\n")


if __name__ == "__main__":
    unittest.main()
