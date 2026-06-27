"""Library for reading a chaptered book document manifest."""

import json
from pathlib import Path
from typing import Any


def require_string(value: Any, field: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{field} must be a string")
    return value


def require_string_list(value: Any, field: str) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise ValueError(f"{field} must be a list of strings")
    return value


def read_manifest(path: Path) -> tuple[str, list[str]]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise ValueError(f"manifest does not exist: {path}") from exc
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid JSON in {path}: {exc}") from exc

    if not isinstance(data, dict):
        raise ValueError("manifest root must be an object")
    source = require_string(data.get("source"), "source")
    chapters = require_string_list(data.get("chapters"), "chapters")
    return source, chapters
