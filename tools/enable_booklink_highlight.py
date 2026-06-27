#!/usr/bin/env python3
"""Enable visible Booklink span coloring in a generated TeX file."""

import re
import sys
from pathlib import Path


# The macros \input line is emitted per book, so its directory varies
# (polish-space/tex/macros.tex, polish-space-ch1/tex/macros.tex, ...).
MACROS_INPUT = re.compile(r"\\input\{[^}]*/tex/macros\.tex\}")
ENABLE = "\\booklinkhighlighttrue"


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: enable_booklink_highlight.py GENERATED.tex", file=sys.stderr)
        return 2

    path = Path(argv[1])
    if not path.is_file():
        print(f"enable_booklink_highlight.py: no such file: {path}", file=sys.stderr)
        return 1
    text = path.read_text(encoding="utf-8")
    if ENABLE in text:
        return 0
    match = MACROS_INPUT.search(text)
    if match is None:
        print(
            f"enable_booklink_highlight.py: no \\input{{.../tex/macros.tex}} in {path}",
            file=sys.stderr,
        )
        return 1

    marker = match.group(0)
    path.write_text(text.replace(marker, marker + "\n" + ENABLE, 1), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
