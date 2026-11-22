#!/usr/bin/env python3
"""Derive a viewer-only TeX layout without changing content or booklink IDs."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

# B sizes use JIS dimensions, as labelled in the viewer menu.
PAPERS = {"a4": (210, 297), "a5": (148, 210), "b5": (182, 257), "b6": (128, 182)}
FONTS = ("default", "10", "11", "12")


def layout_tex(text: str, paper: str, font: str) -> str:
    if paper not in ("default", *PAPERS) or font not in FONTS:
        raise ValueError("unsupported viewer layout")
    preamble, separator, body = text.partition(r"\begin{document}")
    if not separator:
        raise ValueError("missing document body")
    if font != "default":

        def class_options(match: re.Match[str]) -> str:
            options = [item.strip() for item in match[1].split(",") if item.strip()]
            options = [item for item in options if not re.fullmatch(r"\d+(?:\.\d+)?pt", item)]
            return "\\documentclass[" + ",".join([f"{font}pt", *options]) + "]"

        preamble, count = re.subn(r"\\documentclass\[([^]]*)\]", class_options, preamble, count=1)
        if count != 1:
            raise ValueError("expected document class options")
    if paper != "default":
        width, height = PAPERS[paper]

        def geometry_options(match: re.Match[str]) -> str:
            options = [item.strip() for item in match[1].split(",") if item.strip()]
            options = [
                item
                for item in options
                if not re.match(r"(?:paper(?:size|width|height)?\s*=|[ab]\dpaper$|letterpaper$|legalpaper$)", item)
            ]
            options.extend([f"paperwidth={width}mm", f"paperheight={height}mm"])
            return "\\usepackage[" + ",".join(options) + "]{geometry}"

        preamble, count = re.subn(r"\\usepackage\[([^]]*)\]\{geometry\}", geometry_options, preamble, count=1)
        if count != 1:
            raise ValueError("expected geometry package options")
    return preamble + separator + body


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--paper", choices=("default", *PAPERS), required=True)
    parser.add_argument("--font", choices=FONTS, required=True)
    args = parser.parse_args()
    result = layout_tex(args.source.read_text(encoding="utf-8"), args.paper, args.font)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(result, encoding="utf-8")


if __name__ == "__main__":
    main()
