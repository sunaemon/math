"""Citations inside raw theorem/proof TeX must reach the ordinary citeproc pass."""

from __future__ import annotations

import json
import re
import shutil
import subprocess
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FILTER = ROOT / "build" / "book-filter"


@unittest.skipUnless(shutil.which("pandoc") and FILTER.is_file(), "Pandoc and book-filter are required")
class RawCitationRenderingTest(unittest.TestCase):
    def render(self, source: str, *, citeproc: bool = False) -> str:
        args = ["pandoc", "-f", "markdown", "--filter", str(FILTER)]
        if citeproc:
            args += [
                "--citeproc",
                "-M",
                "link-citations:true",
                "--bibliography",
                str(ROOT / "tests/fixtures/citation-pipeline.bib"),
                "--csl",
                str(ROOT / "polish-space/tex/ams-numeric.csl"),
                "-t",
                "latex",
            ]
        else:
            args += ["-t", "json"]
        result = subprocess.run(args, input=source, text=True, capture_output=True, check=True, cwd=ROOT)
        self.assertNotIn("not found", result.stderr)
        return result.stdout

    def test_raw_proof_preserves_tex_and_ignores_literals(self):
        source = r"""\begin{proof}[Proof]
\emph{The result [@Kechris1995,
Theorem 12.6] applies.} See [see @Martin1985; @BeckerKechris1996, pp. 5-7].
% [@CommentOnly]
\verb|[@VerbatimOnly]|
\verb*+[@StarVerbatimOnly]+
\begin{verbatim}
[@EnvironmentOnly]
\end{verbatim}
$[@MathOnly]$ and \([@ParenMathOnly]\) and \[ [@DisplayMathOnly] \].
An escaped percent \% still permits [@Kechris1995, §4.F].
\texttt{[@TextttOnly]} and \url{https://example.org/[@UrlOnly]}.
\begin{equation*}
[@EquationOnly]
\end{equation*}
Ordinary [square brackets] and an email [reader@example.org] remain.
\end{proof}"""
        doc = json.loads(self.render(source))
        ids = []

        # Pandoc's pinned public JSON AST is part of this test boundary. This
        # only joins raw TeX leaves around Cite placeholders; it does not parse
        # citations or emulate rendering. Byte preservation outside citations is
        # a separate invariant from the final citeproc/LaTeX checks below.
        def reconstruct(value):
            if isinstance(value, list):
                return "".join(reconstruct(v) for v in value)
            if not isinstance(value, dict):
                return ""
            if value.get("t") == "Cite":
                ids.extend(c["citationId"] for c in value["c"][0])
                return "<CITE>"
            if value.get("t") in ("RawInline", "RawBlock"):
                return value["c"][1]
            return reconstruct(value.get("c", []))

        actual = reconstruct(doc["blocks"])
        expected = source.replace("[@Kechris1995,\nTheorem 12.6]", "<CITE>")
        expected = expected.replace("[see @Martin1985; @BeckerKechris1996, pp. 5-7]", "<CITE>")
        expected = expected.replace("[@Kechris1995, §4.F]", "<CITE>")
        self.assertEqual(actual, expected)
        self.assertEqual(ids, ["Kechris1995", "Martin1985", "BeckerKechris1996", "Kechris1995"])

    def test_raw_inline_and_nested_optional_heading(self):
        source = r"""`\emph{Inline [@Kechris1995, §18].}`{=latex}

\begin{theorem*}[A result [@Martin1985]]
A statement.
\end{theorem*}
"""
        rendered = self.render(source, citeproc=True)
        self.assertNotIn("[@", rendered)
        self.assertIn(r"\emph{Inline {[}\citeproc", rendered)
        self.assertIn(r"\begin{theorem*}[A result {[}\citeproc", rendered)
        self.assertIn("ref-Kechris1995", rendered)
        self.assertIn("ref-Martin1985", rendered)
        self.assertEqual(rendered.count(r"\begin{theorem*}"), 1)
        self.assertEqual(rendered.count(r"\end{theorem*}"), 1)

    def test_ams_bibliography_is_identical_in_both_languages(self):
        bibliographies = []
        for lang in ("en-US", "ja-JP"):
            source = (
                f"---\nlang: {lang}\n---\n" + "References [@Kechris1995; @HarringtonKechrisLouveau1990; @Martin1985]."
            )
            rendered = self.render(source, citeproc=True)
            bibliography = rendered[rendered.index(r"\begin{CSLReferences}") :]
            bibliographies.append(bibliography)
            self.assertIn(r"Test Journal \textbf{3} (1990), no. 4, 903--928", " ".join(bibliography.split()))
            self.assertIn("Test Book Series, vol. 7", " ".join(bibliography.split()))
            self.assertIn("eds.", bibliography)
            self.assertIn("pp. 303--308", " ".join(bibliography.split()))
            keys = re.findall(r"\\bibitem.*?\{ref-([^}]+)\}", bibliography)
            self.assertEqual(keys, ["HarringtonKechrisLouveau1990", "Kechris1995", "Martin1985"])
        self.assertEqual(*bibliographies)

    def test_report_number_and_institution_survive_citeproc(self):
        for lang in ("en-US", "ja-JP"):
            with self.subTest(lang=lang):
                source = f"---\nlang: {lang}\n---\nReference [@Kashima2000]."
                rendered = self.render(source, citeproc=True)
                bibliography = " ".join(rendered[rendered.index(r"\begin{CSLReferences}") :].split())
                self.assertIn("Technical Reports R-42", bibliography)
                self.assertIn("Test Institute", bibliography)

    def test_both_locales_share_prose_and_raw_citation_numbers(self):
        for lang in ("en-US", "ja-JP"):
            with self.subTest(lang=lang):
                source = (
                    f"---\nlang: {lang}\n---\n"
                    + r"""
Prose [@Kechris1995, Theorem 12.6].

\begin{theorem*}
主張 [@Kechris1995, Theorem 12.6].
\end{theorem*}
"""
                )
                rendered = self.render(source, citeproc=True)
                self.assertNotIn("[@", rendered)
                cites = re.findall(r"\\citeproc\{ref-Kechris1995\}\{([^}]*)\}", rendered)
                self.assertEqual(len(cites), 2)
                self.assertEqual(cites[0], cites[1])
                self.assertEqual(rendered.count(r"\bibitem"), 1)


if __name__ == "__main__":
    unittest.main()
