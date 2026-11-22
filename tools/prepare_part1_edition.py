#!/usr/bin/env python3
"""Generate the Japanese Part I booklet's source, metadata and provenance.

Read synchronized translations; never edit their canonical Markdown. Retain the
mathematical text, local labels and citations. Convert out-of-volume references
to readable titles and external term uses to forward mentions without links.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "polish-space-ja/src/polish-space-book-ja.json"
MASTER = ROOT / "polish-space-ja/src/polish-space-book-ja.md"
OUT = ROOT / "polish-space-part1-ja/build/source"
HEADER = re.compile(r"^#{1,6}\s+(.*?)\s+\{#([^}]+)\}", re.MULTILINE)
TERM = re.compile(r"\\term(define|use|forward)(as)?\{([^{}]+)\}")


def write_if_changed(path: Path, text: str) -> None:
    if not path.exists() or path.read_text() != text:
        path.write_text(text)


def prepare() -> None:
    manifest = json.loads(MANIFEST.read_text())
    chapters = [(ROOT / name, (ROOT / name).read_text()) for name in manifest["chapters"]]
    if "\\label{part-topological-core}" not in chapters[0][1]:
        raise ValueError("The expected Part I boundary is missing")
    chosen: list[tuple[Path, str]] = []
    for path, text in chapters[1:]:
        boundary = re.search(r"\\part\{[^\n]+\}\\label\{([^}]+)\}", text)
        if boundary:
            if boundary.group(1) != "part-definability-classification":
                raise ValueError("Unexpected end boundary for Part I")
            chosen.append((path, text[: boundary.start()]))
            break
        chosen.append((path, text))
    else:
        raise ValueError("The end of Part I was not found")

    separator = "\n\n<!-- PART1-CHAPTER-BREAK -->\n\n"
    body = separator.join(re.sub(r"<!--.*?-->", "", text, flags=re.DOTALL) for _, text in chosen)
    titles: dict[str, str] = {}
    for _, text in chapters:
        headings = list(HEADER.finditer(text))
        chapter_title = headings[0][1] if headings else ""
        for heading in headings:
            title, label = heading.groups()
            titles[label] = f"{chapter_title}：{title}" if title in {"証明", "定義", "例"} else title
    local = set(re.findall(r"\{#([^}]+)\}", body)) | set(re.findall(r"\\label\{([^}]+)\}", body))
    external_refs = sorted(set(re.findall(r"§\{([^}]+)\}", body)) - local)
    for label in external_refs:
        if label not in titles:
            raise ValueError(f"Unknown external section: {label}")
    body = re.sub(
        r"§\{([^}]+)\}",
        lambda m: m[0] if m[1] in local else f"本編「{titles[m[1]]}」",
        body,
    )
    defined = {m[3] for m in TERM.finditer(body) if m[1] == "define"}
    external_terms = sorted({m[3] for m in TERM.finditer(body) if m[1] != "define"} - defined)
    body = TERM.sub(
        lambda m: f"\\termforward{m[2] or ''}{{{m[3]}}}" if m[1] == "use" and m[3] in external_terms else m[0],
        body,
    )
    watch_match = re.search(r"^notation-watch:\n((?:  - .+\n)+)", MASTER.read_text(), re.MULTILINE)
    if not watch_match:
        raise ValueError("Missing canonical notation watch list")
    watched = [line[4:] for line in watch_match[1].splitlines()]
    watched = [name for name in watched if re.search(r"\\" + re.escape(name) + r"(?![A-Za-z])", body)]

    def defined_notations(text: str) -> set[str]:
        return {name.strip() for group in re.findall(r"\\define\{([^}]+)\}", text) for name in group.split(",")}

    imported = sorted(set(watched) & (defined_notations(chapters[0][1]) - defined_notations(body)))
    # A symbol whose actual definition is in a later volume remains a plain
    # forward mention. Do not manufacture a definition or a dangling index link.
    external_notations = sorted(set(watched) - defined_notations(body) - set(imported))
    watched = [name for name in watched if name not in external_notations]
    prelude = "\\mainmatter\n\n"
    if imported:
        prelude += "\\begin{mathmeta}\n"
        prelude += "".join(f"  \\define{{{name}}}\n" for name in imported)
        prelude += "\\end{mathmeta}\n\n"
    prelude += "\\part{ポーランド空間とBorel構造}\\label{part-topological-core}\n\n"
    OUT.mkdir(parents=True, exist_ok=True)
    pieces = body.split(separator)
    if len(pieces) != len(chosen):
        raise ValueError("Chapter boundaries changed during edition preparation")
    for i, ((path, _), piece) in enumerate(zip(chosen, pieces, strict=True)):
        # Changing an external term use to a forward mention can lengthen an
        # otherwise already wrapped source line. Break only at Japanese stops.
        piece = "\n".join(
            re.sub(r"([。．])(?=\S)", r"\1\n", line) if len(line) > 120 else line for line in piece.splitlines()
        )
        write_if_changed(OUT / path.name, (prelude if i == 0 else "") + piece.strip() + "\n")
    write_if_changed(OUT / "body.md", prelude + "\n\n".join(pieces).strip() + "\n")
    write_if_changed(
        OUT / "metadata.json",
        json.dumps({"notation-watch": watched, "term-forward-external": external_terms}, ensure_ascii=False, indent=2)
        + "\n",
    )
    art = ["% Generated Cantor construction: each row removes the middle third."]
    intervals = [(0.0, 1.0)]
    for level in range(6):
        y = 112 - level * 8
        width = 2.4 - level * 0.28
        for left, right in intervals:
            art.append(
                f"\\draw[draw=CoverInk,line width={width:.2f}pt,line cap=round] "
                f"({18 + 112 * left:.4f},{y})--({18 + 112 * right:.4f},{y});"
            )
        intervals = [
            piece
            for left, right in intervals
            for piece in ((left, left + (right - left) / 3), (right - (right - left) / 3, right))
        ]
    write_if_changed(OUT / "cover-art.tex", "\n".join(art) + "\n")
    provenance = {
        "edition": "日本語版・第I部抜粋",
        "circle": "ふりふり企画",
        "chapters": [
            {"source": str(path.relative_to(ROOT)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            for path, _ in chosen
        ],
        "externalSections": {label: titles[label] for label in external_refs},
        "externalTerms": external_terms,
        "externalNotations": external_notations,
    }
    write_if_changed(OUT / "provenance.json", json.dumps(provenance, ensure_ascii=False, indent=2) + "\n")
    print(f"Prepared Part I: {len(chosen)} chapters; {len(external_refs)} out-of-volume sections")


if __name__ == "__main__":
    argparse.ArgumentParser(description=__doc__).parse_args()
    prepare()
