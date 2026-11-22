#!/usr/bin/env python3
"""Select a discovered book and run the repository's TeX validation workflow."""

import argparse
import subprocess
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, help="discovered book master .md source")
    parser.add_argument("--tex-only", action="store_true", help="compatibility flag; TeX-only is the default")
    args = parser.parse_args()
    if not Path("Makefile").is_file():
        parser.error("run from the repository root containing Makefile")
    listing = subprocess.run(
        ["make", "--no-print-directory", "list-books"], capture_output=True, text=True, check=False
    )
    if listing.returncode:
        parser.exit(listing.returncode, listing.stderr)
    books = {}
    for line in listing.stdout.splitlines():
        fields = line.split()
        if len(fields) == 3:
            stem, _directory, source = fields
            books[stem] = Path(source)
    if not books:
        parser.error("no book manifests discovered")
    if args.source:
        matches = [stem for stem, source in books.items() if source.resolve() == args.source.resolve()]
        if len(matches) != 1:
            parser.error(f"source is not a discovered book master: {args.source}")
        stem = matches[0]
    else:
        stem = "polish-space-book" if "polish-space-book" in books else next(iter(books))
    return subprocess.run(["make", "validate-tex", f"BOOKS={stem}"], check=False).returncode


if __name__ == "__main__":
    raise SystemExit(main())
