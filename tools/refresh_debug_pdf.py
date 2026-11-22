#!/usr/bin/env python3
"""Refresh a debug PDF, rebuilding its index and references when they change."""

import argparse
import hashlib
import shlex
import subprocess
from pathlib import Path


def read(path: Path) -> bytes:
    return path.read_bytes() if path.exists() else b""


def refresh(stem: Path, latex: list[str], indexer: list[str], max_passes: int = 5) -> None:
    auxiliaries = [stem.with_suffix(suffix) for suffix in (".aux", ".out", ".toc")]
    idx = stem.with_suffix(".idx")
    ind = stem.with_suffix(".ind")
    stamp = stem.with_suffix(".index-sha256")
    for attempt in range(1, max_passes + 1):
        before = [read(path) for path in auxiliaries]
        print(f"  lualatex {stem.name} (incremental pass {attempt})", flush=True)
        subprocess.run(latex, check=True)
        indexed = False
        if idx.exists():
            digest = hashlib.sha256(idx.read_bytes()).hexdigest().encode()
            if not ind.exists() or read(stamp) != digest:
                print(f"  index {stem.name}", flush=True)
                subprocess.run([*indexer, str(idx)], check=True)
                stamp.write_bytes(digest)
                indexed = True
        if not indexed and before == [read(path) for path in auxiliaries]:
            return
    raise RuntimeError(f"{stem.name}: index or references did not settle after {max_passes} passes")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stem", type=Path, required=True)
    parser.add_argument("--indexer", required=True)
    parser.add_argument("latex", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.latex[1:] if args.latex[:1] == ["--"] else args.latex
    if not command:
        parser.error("a LaTeX command is required after --")
    refresh(args.stem, command, shlex.split(args.indexer))


if __name__ == "__main__":
    main()
