"""Compile real debug-anchor macros at paragraph and list-item starts."""

import argparse
import shlex
import subprocess
import tempfile
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lualatex", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    document = (
        r"\documentclass{book}\usepackage{amssymb,fontspec,unicode-math,hyperref,makeidx}\makeindex"
        + "\\input{"
        + (root / "polish-space/tex/macros.tex").as_posix()
        + "}\n"
        + r"""
\usepackage{caption}
\captionsetup[table]{skip=6pt}
\let\OriginalAnchor\hypertarget
\renewcommand{\hypertarget}[2]{%
  \OriginalAnchor{#1}{#2}%
  \ifhmode\typeout{anchor-hmode:#1}\else\errmessage{Anchor outside horizontal mode}\fi}
\begin{document}
\booklinkhighlighttrue
\SkipStart{paragraph} Paragraph text.\SkipEnd{paragraph}\par
\begin{itemize}
\SkipStart{list}\item List text.\SkipEnd{list}
\end{itemize}
\SkipStart{whitespace} \ifnum\lastnodetype=11\errmessage{Leading space after paragraph anchor}\fi
Trimmed paragraph.\SkipEnd{whitespace}\par
Inline\SkipStart{inline} \ifnum\lastnodetype=11\else\errmessage{Lost inline space}\fi
text.\SkipEnd{inline}\par
\BooklinkStart[entry=1]{name}Booklink text.\BooklinkEnd[entry=1]{name}\par
\booklinkhighlightfalse
\SkipStart{release}Release text.\SkipEnd{release}
\end{document}
"""
    )
    with tempfile.TemporaryDirectory(prefix="debug-anchors-") as directory:
        source = Path(directory) / "anchors.tex"
        source.write_text(document, encoding="utf-8")
        result = subprocess.run(
            shlex.split(args.lualatex) + ["-interaction=nonstopmode", "-halt-on-error", str(source)],
            cwd=directory,
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        markers = [
            line.strip()
            for line in source.with_suffix(".log").read_text(encoding="utf-8").splitlines()
            if line.startswith("anchor-hmode:") and not line.strip().endswith("-end")
        ]
        expected = [
            "anchor-hmode:skip-paragraph-start",
            "anchor-hmode:skip-list-start",
            "anchor-hmode:skip-whitespace-start",
            "anchor-hmode:skip-inline-start",
            "anchor-hmode:booklink-entry-1",
        ]
        if markers != expected:
            raise RuntimeError(f"Unexpected start anchors: {markers!r}")
    print("PASS: debug anchors start in horizontal mode, handle list items, and omit release skips")


if __name__ == "__main__":
    main()
