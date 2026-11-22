"""Git textconv: ignore source line numbers in gettext reference comments."""

import argparse
import re
import sys
from pathlib import Path


def normalize_references(text: str) -> str:
    return "".join(
        re.sub(r"(?<=\S):[0-9]+(?=\s|$)", "", line) if line.startswith("#:") else line
        for line in text.splitlines(keepends=True)
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path)
    args = parser.parse_args(argv)
    try:
        sys.stdout.write(normalize_references(args.path.read_text(encoding="utf-8")))
    except (OSError, UnicodeError) as error:
        print(f"po_diff: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
