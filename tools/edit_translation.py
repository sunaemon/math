#!/usr/bin/env python3
"""Preview/apply literal notation edits, then finish a reviewed translation batch."""

from __future__ import annotations

import argparse
import ast
import difflib
import fcntl
import json
import re
import subprocess
from pathlib import Path

from check_translation_workflow import git_blob_hash
from project_translation_sourcemap import ProjectionError, read_po

ROOT = Path(__file__).resolve().parents[1]
STATUS = Path("polish-space-ja/l10n/translation-status.json")


def replace_po(text: str, old: str, new: str) -> str:
    """Replace decoded singular fields; preserve comments, flags and other fields."""
    if re.search(r"^msgid_plural |^msgstr\[", text, re.MULTILINE):
        raise ValueError("plural PO messages are not supported")
    pattern = r'^(msgid|msgstr) ("[^\n]*")(?:\n"[^\n]*")*'

    def replace(match: re.Match[str]) -> str:
        field, first = match.group(0).split(" ", 1)
        value = "".join(ast.literal_eval(line) for line in first.splitlines())
        changed = value.replace(old, new)
        if field == "msgstr" and value and any(len(line) > 120 for line in changed.splitlines()):
            raise ValueError("translated message exceeds 120 columns; adjust PO line breaks first")
        if changed == value:
            return match.group(0)
        lines = changed.splitlines(keepends=True)
        return field + ' ""\n' + "\n".join(json.dumps(line, ensure_ascii=False) for line in lines)

    return re.sub(pattern, replace, text, flags=re.MULTILINE)


def selected_chapters(root: Path, names: list[str]) -> tuple[dict, list[str]]:
    data = json.loads((root / STATUS).read_text())
    selected = list(dict.fromkeys(name if name.endswith(".md") else name + ".md" for name in names))
    for name in selected:
        if name not in data["chapters"]:
            raise ValueError(f"unknown chapter: {name}")
    return data, selected


def run_make(root: Path, *arguments: str) -> None:
    print("+ make " + " ".join(arguments), flush=True)
    subprocess.run(["make", *arguments], cwd=root, check=True)


def check_reviewed_po(path: Path) -> None:
    if any(not message.msgstr for message in read_po(path)):
        raise ValueError(f"{path}: untranslated messages remain")


def replace_chapters(root: Path, names: list[str], old: str, new: str, apply: bool) -> None:
    if not old or old == new:
        raise ValueError("old must be nonempty and different from new")
    data, selected = selected_chapters(root, names)
    changes: list[tuple[Path, str]] = []
    long_lines = []
    for name in selected:
        source = root / data["chapters"][name]["source"]
        po = root / "polish-space-ja/l10n/ja" / (Path(name).stem + ".po")
        # Refuse fuzzy/incomplete catalogs before editing their message identities.
        check_reviewed_po(po)
        original = source.read_text()
        if old not in original:
            raise ValueError(f"{name}: old text does not occur in English source")
        for path, before, after in [
            (source, original, original.replace(old, new)),
            (po, po.read_text(), replace_po(po.read_text(), old, new)),
        ]:
            print(
                "".join(
                    difflib.unified_diff(
                        before.splitlines(True),
                        after.splitlines(True),
                        fromfile=str(path.relative_to(root)),
                        tofile=str(path.relative_to(root)),
                    )
                ),
                end="",
            )
            changes.append((path, after))
        long_lines.extend(
            f"{name}:{i}: {len(line)} > 120" for i, line in enumerate(changes[-2][1].splitlines(), 1) if len(line) > 120
        )
    if long_lines:
        raise ValueError("adjust line breaks before applying:\n" + "\n".join(long_lines))
    if apply:
        for path, content in changes:
            path.write_text(content)
        run_make(root, "translation-ja-update-catalogs")
    else:
        print("Preview only; use --apply to write and refresh catalogs.")


def finish(root: Path, names: list[str], books: list[str]) -> None:
    run_make(root, "translation-ja-update-catalogs")
    data, selected = selected_chapters(root, names)
    for name in selected:
        check_reviewed_po(root / "polish-space-ja/l10n/ja" / (Path(name).stem + ".po"))
        entry = data["chapters"][name]
        entry["sourceBlob"] = git_blob_hash(root / entry["source"])
    # Only the explicitly reviewed chapters receive new provenance; preserve flags.
    if selected:
        (root / STATUS).write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    run_make(root, "translation-ja-generate")
    run_make(root, "lint-book")
    run_make(root, "validate-tex", "BOOKS=" + " ".join(books))
    run_make(root, "lint")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    replace = sub.add_parser("replace", help="preview a literal edit in English and PO; never edit generated Markdown")
    replace.add_argument("--chapter", action="append", required=True)
    replace.add_argument("--old", required=True)
    replace.add_argument("--new", required=True)
    replace.add_argument("--apply", action="store_true")
    check = sub.add_parser("finish", help="refresh, record explicit review, generate, lint and validate sequentially")
    check.add_argument(
        "--reviewed",
        action="append",
        default=[],
        metavar="CHAPTER",
        help="affirm that this chapter translation was reviewed against the current English",
    )
    check.add_argument("--book", action="append", default=None)
    args = parser.parse_args()
    try:
        (ROOT / "build").mkdir(exist_ok=True)
        with (ROOT / "build/translation-edit.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            if args.command == "replace":
                replace_chapters(ROOT, args.chapter, args.old, args.new, args.apply)
            else:
                finish(ROOT, args.reviewed, args.book or ["polish-space-book", "polish-space-book-ja"])
    except (ValueError, OSError, ProjectionError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
