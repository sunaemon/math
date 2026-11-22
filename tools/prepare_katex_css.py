#!/usr/bin/env python3
"""Keep only woff2 font sources in official KaTeX CSS, preserving rule boundaries."""

import argparse
import re
from pathlib import Path


def woff2_only(css: str) -> str:
    def trim(match: re.Match[str]) -> str:
        source = re.search(r'url\([^)]*\.woff2\)\s*format\(["\']woff2["\']\)', match[0])
        if not source:
            raise ValueError("KaTeX font source has no woff2 alternative")
        return "src:" + source[0]

    # A source descriptor cannot cross a declaration or rule boundary.
    return re.sub(r"src:[^;}]+", trim, css)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    args.destination.write_text(woff2_only(args.source.read_text(encoding="utf-8")), encoding="utf-8")


if __name__ == "__main__":
    main()
