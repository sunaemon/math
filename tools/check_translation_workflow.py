#!/usr/bin/env python3
"""Validate a po4a-managed book translation using one temporary render.

The check validates catalog syntax and completeness, verifies that every PO
and POT still describes the current English source, renders into a temporary
directory, compares that render with the committed translated Markdown, and
then checks source structure.  ``--catalogs-only`` skips the render comparison
so the command can safely gate regeneration of a missing output file.
``--write-generated`` installs that render only after every chapter passes
validation, preserving unchanged files and their modification times.

Exit codes: 0 success, 1 validation or execution failure, 2 command-line usage error.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import check_translation_structure
import check_translation_terms
from project_translation_sourcemap import ProjectionError
from translation_validation_cache import RenderCache, fingerprint, toolchain_fingerprint


class TranslationCheckError(RuntimeError):
    """A concise, user-facing translation-workflow failure."""


@dataclass(frozen=True)
class Chapter:
    filename: str
    source: Path
    translated: Path
    po: Path
    pot: Path
    source_blob: str


def git_blob_hash(path: Path) -> str:
    """Return the Git blob ID for the current bytes of ``path``."""
    content = path.read_bytes()
    header = f"blob {len(content)}\0".encode()
    return hashlib.sha1(header + content).hexdigest()


def _run(
    command: list[str],
    *,
    cwd: Path,
    input_text: str | None = None,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        command,
        cwd=cwd,
        input=input_text,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        rendered = " ".join(command)
        raise TranslationCheckError(f"command failed ({rendered}): {detail}")
    return result


def _load_status(
    repo_root: Path,
    l10n_dir: Path,
    translated_dir: Path,
    status_path: Path,
) -> list[Chapter]:
    try:
        data: dict[str, Any] = json.loads(status_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise TranslationCheckError(f"cannot read {status_path}: {error}") from error
    if data.get("language") != "ja":
        raise TranslationCheckError(f"{status_path}: expected language 'ja'")
    entries = data.get("chapters")
    if not isinstance(entries, dict) or not entries:
        raise TranslationCheckError(f"{status_path}: chapters must be a nonempty object")

    chapters: list[Chapter] = []
    for filename, entry in entries.items():
        if not isinstance(filename, str) or not isinstance(entry, dict):
            raise TranslationCheckError(f"{status_path}: invalid chapter entry")
        source_value = entry.get("source")
        source_blob = entry.get("sourceBlob")
        if not isinstance(source_value, str) or not isinstance(source_blob, str):
            raise TranslationCheckError(f"{status_path}: {filename} lacks source/sourceBlob")
        source = repo_root / source_value
        if not source.is_file():
            raise TranslationCheckError(f"missing English source: {source}")
        actual_blob = git_blob_hash(source)
        if actual_blob != source_blob:
            raise TranslationCheckError(
                f"{filename}: English source changed ({source_blob} -> {actual_blob}); "
                "refresh the catalog, review the translation, then record the new sourceBlob"
            )
        stem = Path(filename).stem
        chapters.append(
            Chapter(
                filename=filename,
                source=source,
                translated=translated_dir / filename,
                po=l10n_dir / "ja" / f"{stem}.po",
                pot=l10n_dir / "pot" / f"{stem}.pot",
                source_blob=source_blob,
            )
        )
    return chapters


def _check_config(config: Path, chapters: list[Chapter], source_dir: Path, output_dir: Path) -> None:
    """Require po4a's configured source/output pairs to match the status ledger."""
    text = re.sub(r"\\\n", " ", config.read_text(encoding="utf-8"))
    expected = {(chapter.source.resolve(), (output_dir / chapter.filename).resolve()) for chapter in chapters}
    configured = set()
    for line in text.splitlines():
        match = re.match(r"\s*\[type:[^\]]+\]\s*(.*)", line)
        if not match:
            continue
        try:
            fields = shlex.split(match[1], comments=True)
        except ValueError as error:
            raise TranslationCheckError(f"{config}: invalid type entry: {error}") from error
        if not fields:
            raise TranslationCheckError(f"{config}: missing source in type entry")

        def expand(value: str) -> Path:
            value = value.replace("$(source)", str(source_dir)).replace("$(output)", str(output_dir))
            if "$" in value:
                raise TranslationCheckError(f"{config}: unsupported path variable: {value}")
            path = Path(value)
            return (config.parent / path).resolve() if not path.is_absolute() else path.resolve()

        outputs = [field.split(":", 1)[1] for field in fields[1:] if field.startswith(("$lang:", "ja:"))]
        if len(outputs) != 1:
            raise TranslationCheckError(f"{config}: expected one Japanese output for {fields[0]}")
        pair = (expand(fields[0]), expand(outputs[0]))
        if pair in configured:
            raise TranslationCheckError(f"{config}: duplicate chapter {pair[0]}")
        configured.add(pair)
    if configured != expected:
        missing = sorted(str(source) for source, _ in expected - configured)
        extra = sorted(str(source) for source, _ in configured - expected)
        raise TranslationCheckError(f"{config}: chapter set differs from status; missing={missing}, extra={extra}")


def _atomic_write(path: Path, content: bytes) -> None:
    """Publish a complete generated file using a sibling temporary file."""
    descriptor, name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(content)
        # mkstemp defaults to 0600; generated book sources have ordinary read permissions.
        temporary.chmod(path.stat().st_mode & 0o777 if path.exists() else 0o644)
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def _selected_catalog_messages(repo_root: Path, po: Path, selector: str) -> bool:
    selected = _run(
        ["msgattrib", selector, "--no-obsolete", str(po)],
        cwd=repo_root,
    )
    messages = _run(
        ["msggrep", "--msgid", "--extended-regexp", "--regexp=.+$"],
        cwd=repo_root,
        input_text=selected.stdout,
    )
    return bool(messages.stdout.strip())


def _compare_message_sets(repo_root: Path, current: Path, refreshed: Path) -> None:
    common = ["msgcmp", "--no-fuzzy-matching", "--use-fuzzy", "--use-untranslated"]
    _run([*common, str(current), str(refreshed)], cwd=repo_root)
    _run([*common, str(refreshed), str(current)], cwd=repo_root)


def _check_catalogs(repo_root: Path, chapters: list[Chapter]) -> None:
    for chapter in chapters:
        for catalog in (chapter.po, chapter.pot):
            if not catalog.is_file():
                raise TranslationCheckError(f"missing catalog: {catalog}")
        _run(
            [
                "msgfmt",
                "--check",
                "--check-compatibility",
                "-o",
                "/dev/null",
                str(chapter.po),
            ],
            cwd=repo_root,
        )
        if _selected_catalog_messages(repo_root, chapter.po, "--only-fuzzy"):
            raise TranslationCheckError(f"{chapter.po}: fuzzy translations remain")
        if _selected_catalog_messages(repo_root, chapter.po, "--untranslated"):
            raise TranslationCheckError(f"{chapter.po}: untranslated messages remain")


def _check_terminology(chapters: list[Chapter], glossary_path: Path) -> None:
    try:
        glossary = check_translation_terms.load_glossary(glossary_path)
        diagnostics = check_translation_terms.check_catalogs([chapter.po for chapter in chapters], glossary)
    except (
        check_translation_terms.TerminologyError,
        ProjectionError,
        check_translation_structure.StructureParseError,
    ) as error:
        raise TranslationCheckError(f"terminology: {error}") from error
    if diagnostics:
        raise TranslationCheckError("terminology differs from glossary:\n" + "\n".join(diagnostics))


def check_workflow(
    *,
    repo_root: Path,
    po4a: str,
    config: Path,
    l10n_dir: Path,
    translated_dir: Path,
    status_path: Path,
    catalogs_only: bool,
    write_generated: bool = False,
    cache_dir: Path | None = None,
) -> None:
    if catalogs_only and write_generated:
        raise TranslationCheckError("catalogs-only and write-generated are mutually exclusive")
    chapters = _load_status(repo_root, l10n_dir, translated_dir, status_path)
    source_directories = {chapter.source.parent.resolve() for chapter in chapters}
    if len(source_directories) != 1:
        raise TranslationCheckError("all pilot sources must share one source directory")
    source_dir = source_directories.pop()
    _check_config(config, chapters, source_dir, translated_dir)
    cache = None
    keys = {}
    contents = {}
    pending = chapters

    def common_fingerprint() -> str:
        return fingerprint([config, l10n_dir / "glossary-ja.yaml"], toolchain_fingerprint(po4a))

    if cache_dir is not None:
        common = common_fingerprint()
        cache = RenderCache(cache_dir, common)
        for chapter in chapters:
            keys[chapter.filename] = cache.key(
                [chapter.source, chapter.po, chapter.pot],
                str(chapter.source.resolve()) + chapter.source_blob,
            )
            content = cache.read(keys[chapter.filename])
            if content is not None:
                contents[chapter.filename] = content
        pending = [chapter for chapter in chapters if chapter.filename not in contents]
    if pending:
        _check_catalogs(repo_root, pending)
        _check_terminology(pending, l10n_dir / "glossary-ja.yaml")

    with tempfile.TemporaryDirectory(prefix="book-translation-check-") as temporary:
        root = Path(temporary)
        temporary_l10n = root / "l10n"
        temporary_ja = temporary_l10n / "ja"
        temporary_pot = temporary_l10n / "pot"
        temporary_output = root / "output"
        temporary_ja.mkdir(parents=True)
        temporary_pot.mkdir(parents=True)
        temporary_output.mkdir(parents=True)
        for chapter in pending:
            shutil.copy2(chapter.po, temporary_ja / chapter.po.name)

        render_config = config
        if cache is not None and pending:
            # Keep global options verbatim; retain only the selected type entries.
            # The configured source/output pairs were validated above.
            selected = {chapter.source.resolve() for chapter in pending}
            lines = []
            for line in re.sub(r"\\\n", " ", config.read_text()).splitlines():
                match = re.match(r"\s*\[type:[^\]]+\]\s*(.*)", line)
                if match:
                    source = shlex.split(match[1], comments=True)[0].replace("$(source)", str(source_dir))
                    if (config.parent / source).resolve() not in selected:
                        continue
                lines.append(line)
            render_config = root / "po4a.cfg"
            render_config.write_text("\n".join(lines) + "\n")
        if pending:
            _run(
                [
                    po4a,
                    "--force",
                    "--variable",
                    f"l10n={temporary_l10n}",
                    "--variable",
                    f"source={source_dir}",
                    "--variable",
                    f"output={temporary_output}",
                    str(render_config),
                ],
                cwd=repo_root,
            )

        for chapter in pending:
            refreshed_po = temporary_ja / chapter.po.name
            refreshed_pot = temporary_pot / chapter.pot.name
            _compare_message_sets(repo_root, chapter.po, refreshed_po)
            _compare_message_sets(repo_root, chapter.pot, refreshed_pot)
            if catalogs_only:
                continue

            rendered = temporary_output / chapter.filename
            diagnostics = check_translation_structure.compare_files(chapter.source, rendered)
            if diagnostics:
                detail = "\n  - ".join(diagnostics)
                raise TranslationCheckError(
                    f"{chapter.translated}: structure differs from {chapter.source}\n  - {detail}"
                )

            contents[chapter.filename] = rendered.read_bytes()

        if cache is not None and common_fingerprint() != cache.common:
            raise TranslationCheckError("translation configuration or tools changed during validation; retry")
        for chapter in chapters:
            if cache is not None:
                current_key = cache.key(
                    [chapter.source, chapter.po, chapter.pot], str(chapter.source.resolve()) + chapter.source_blob
                )
                if current_key != keys[chapter.filename]:
                    raise TranslationCheckError(f"{chapter.filename}: inputs changed during validation; retry")
            if catalogs_only:
                continue
            if write_generated:
                if chapter.translated.is_symlink():
                    raise TranslationCheckError(f"refusing to overwrite symlink: {chapter.translated}")
            elif not chapter.translated.is_file():
                raise TranslationCheckError(f"missing generated Markdown: {chapter.translated}")
            elif contents[chapter.filename] != chapter.translated.read_bytes():
                raise TranslationCheckError(
                    f"{chapter.translated}: generated Markdown is stale; run make translation-ja-sync"
                )

        # Cache only complete structure-checked renders after the entire batch passes.
        if cache is not None and not catalogs_only:
            for chapter in pending:
                cache.write(keys[chapter.filename], contents[chapter.filename])
        if cache is not None:
            print(f"Translation cache: {len(chapters) - len(pending)} reused; {len(pending)} checked")

        # Do not change any output if a later chapter fails validation.
        if write_generated:
            for chapter in chapters:
                content = contents[chapter.filename]
                if chapter.translated.is_file() and chapter.translated.read_bytes() == content:
                    continue
                chapter.translated.parent.mkdir(parents=True, exist_ok=True)
                _atomic_write(chapter.translated, content)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--po4a", required=True)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--l10n-dir", type=Path, required=True)
    parser.add_argument("--translated-dir", type=Path, required=True)
    parser.add_argument("--status", type=Path, required=True)
    parser.add_argument("--cache-dir", type=Path, help="reuse fully validated chapter renders by input hash")
    parser.add_argument("--no-cache", action="store_true", help="force every chapter through all checks")
    mode_group = parser.add_mutually_exclusive_group()
    mode_group.add_argument("--catalogs-only", action="store_true")
    mode_group.add_argument("--write-generated", action="store_true")
    args = parser.parse_args(argv)

    repo_root = args.repo_root.resolve()
    try:
        check_workflow(
            repo_root=repo_root,
            po4a=args.po4a,
            config=args.config.resolve(),
            l10n_dir=args.l10n_dir.resolve(),
            translated_dir=args.translated_dir.resolve(),
            status_path=args.status.resolve(),
            catalogs_only=args.catalogs_only,
            write_generated=args.write_generated,
            cache_dir=None if args.no_cache else args.cache_dir,
        )
    except (OSError, UnicodeError, TranslationCheckError, check_translation_structure.StructureParseError) as error:
        print(f"translation workflow check failed: {error}", file=sys.stderr)
        return 1
    mode = "catalogs" if args.catalogs_only else "catalogs and generated Markdown"
    print(f"translation workflow OK: {mode}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
