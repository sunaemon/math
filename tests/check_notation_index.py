"""Check real TeX index keys across normal and pre-tokenized contexts."""

import argparse
import shlex
import subprocess
import tempfile
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lualatex", required=True)
    parser.add_argument("--makeindex", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    entry = r"\BookNotationIndex{0Notation@Notation!lSigma@$\protect\lSigma$!referenced by}"
    document = (
        r"\documentclass{article}\usepackage{amssymb,fontspec,unicode-math,hyperref,makeidx}\makeindex"
        + "\\input{"
        + (root / "polish-space/tex/macros.tex").as_posix()
        + "}\n"
        + r"\newtheorem{claim}{Claim}"
        + r"\begin{document}Normal "
        + entry
        + r"\emph{Emphasis "
        + entry
        + r"}\begin{claim}[Title "
        + entry
        + r"]Text\end{claim}\end{document}"
    )
    with tempfile.TemporaryDirectory(prefix="notation-index-") as directory:
        source = Path(directory) / "index.tex"
        source.write_text(document, encoding="utf-8")
        for command in (
            shlex.split(args.lualatex)
            + ["-interaction=nonstopmode", "-halt-on-error", "-output-directory=" + directory, str(source)],
            shlex.split(args.makeindex) + ["index.idx"],
        ):
            result = subprocess.run(command, check=False, capture_output=True, text=True, cwd=directory)
            if result.returncode:
                raise RuntimeError(result.stdout + result.stderr)
        entries = source.with_suffix(".idx").read_text(encoding="utf-8").splitlines()
        if len(entries) != 3 or len(set(entries)) != 1:
            raise RuntimeError(f"Expected three identical notation-index entries: {entries!r}")
        index = source.with_suffix(".ind").read_text(encoding="utf-8")
        if index.count(r"\subsubitem") != 1:
            raise RuntimeError(f"Expected one merged notation-index item: {index!r}")
    print("PASS: notation index merges normal text, emphasis, and theorem titles")


if __name__ == "__main__":
    main()
