#!/usr/bin/env python3
"""Derive local template partials from the selected Pandoc installation.

Inputs are Pandoc's common.latex and tools/pandoc/templates/*.latex. Outputs
live in the supplied data directory. Keep the Japanese class's native caption
layout instead of loading an unsupported caption package. Reject a changed
upstream table-caption block so future upgrades require an explicit review.
"""

import argparse
import subprocess
from pathlib import Path


def write_changed(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists() or path.read_text(encoding="utf-8") != text:
        path.write_text(text, encoding="utf-8")


def adapt_captions(common: str) -> str:
    block = "\\usepackage{caption}\n\\captionsetup[table]{skip=6pt}\n"
    if "\\usepackage{caption}" not in common and "\\captionsetup[table]" not in common:
        return common
    if common.count(block) != 1:
        raise ValueError("Review the updated Pandoc table-caption partial")
    return common.replace(
        block,
        "$if(native-captions)$\n"
        "% The Japanese document class supplies its own caption layout.\n"
        "$else$\n" + block + "$endif$\n",
        1,
    )


def verify_font_override(upstream: str, local: str) -> None:
    header = (
        "$-- Based on the bundled Pandoc font-settings.latex partial.\n"
        "$-- Only the conditional around microtype is local; Japanese books opt out.\n"
    )
    wrapper = (
        "$if(disable-microtype)$\n"
        "% LuaTeX-ja provides the Japanese typography; do not load incompatible microtype.\n"
        "$else$\n"
    )
    if not local.startswith(header) or local.count(wrapper) != 1 or not local.endswith("$endif$\n"):
        raise ValueError("Review the local Pandoc font-settings override")
    restored = local.removeprefix(header).replace(wrapper, "", 1).removesuffix("$endif$\n")
    if restored != upstream:
        raise ValueError("Review the updated Pandoc font-settings partial; local differences exceed microtype")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pandoc", nargs=argparse.REMAINDER, required=True)
    args = parser.parse_args()

    def upstream_partial(name: str) -> str:
        return subprocess.run(
            [*args.pandoc, "--print-default-data-file", f"templates/{name}"],
            check=True,
            capture_output=True,
            encoding="utf-8",
        ).stdout

    common = adapt_captions(upstream_partial("common.latex"))
    source_dir = Path(__file__).resolve().parent / "pandoc/templates"
    local_fonts = (source_dir / "font-settings.latex").read_text(encoding="utf-8")
    verify_font_override(upstream_partial("font-settings.latex"), local_fonts)
    templates = args.output / "templates"
    for source in source_dir.glob("*.latex"):
        write_changed(templates / source.name, source.read_text(encoding="utf-8"))
    write_changed(templates / "common.latex", common)


if __name__ == "__main__":
    main()
