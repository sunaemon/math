"""Library for reading a chaptered book document manifest."""

import json
import re
from pathlib import Path
from typing import Any

STEM_PATTERN = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_-]*$")


class ManifestError(ValueError):
    """The contents of a book manifest are invalid."""


def require_string(value: Any, field: str) -> str:
    if not isinstance(value, str):
        raise ManifestError(f"{field} must be a string")
    return value


def require_string_list(value: Any, field: str) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ManifestError(f"{field} must be a list of strings")
    return value


def read_manifest(path: Path) -> tuple[str, list[str]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ManifestError(f"manifest does not exist: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ManifestError(f"invalid JSON in {path}: {exc}") from exc

    if not isinstance(data, dict):
        raise ManifestError("manifest root must be an object")
    source = require_string(data.get("source"), "source")
    chapters = require_string_list(data.get("chapters"), "chapters")
    return source, chapters


def book_stem(path: Path) -> str:
    """Return the shared Make-safe artifact stem, rejecting invalid names."""
    if not STEM_PATTERN.fullmatch(path.stem):
        raise ManifestError(f"book stem must match {STEM_PATTERN.pattern}: {path}")
    return path.stem


def read_book_manifest(path: Path) -> tuple[str, str, list[str]]:
    """Read an artifact-bearing book and validate its master source identity."""
    stem = book_stem(path)
    source, chapters = read_manifest(path)
    if Path(source).stem != stem:
        raise ManifestError(f"{path}: source file must be named {stem}.md, got {source}")
    return stem, source, chapters
