#!/usr/bin/env python3
"""Build selected books and report diagnostics from this invocation's targets only.

Use `make validate-tex` during editing and `make validate-debug` after a commit.
BOOKS="stem ..." limits either target to particular discovered books. Reports
and log snapshots live in a unique build/validation/ directory for each run.

Exit codes: 0 validation passed, 1 build or diagnostic failure, 2 invalid arguments or book selection.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import tempfile
import time
from pathlib import Path

import latex_lock
from book_manifest import read_book_manifest


def discover_books(root: Path) -> dict[str, Path]:
    books = {}
    for manifest in sorted(root.glob("*/src/*.json")):
        stem, _, _ = read_book_manifest(manifest)
        if stem in books:
            raise ValueError(f"invalid or duplicate book stem: {manifest}")
        books[stem] = manifest.parent.parent / "build" / stem
    return books


def diagnostics(text: str, *, generation_only: bool = False) -> list[dict]:
    findings = []
    for number, line in enumerate(text.splitlines(), 1):
        # infwarerr describes a loaded package, not a warning. Index summaries
        # can contain both zero warnings and nonzero rejected entries.
        if line.startswith("Package: infwarerr "):
            continue
        checked = re.sub(r"\b0 (?:warnings?|rejected)\b", "", line, flags=re.IGNORECASE)
        pattern = r"\[WARNING\]|^!|\bError:|^make.*\*\*\*|Undefined control sequence|Emergency stop|Fatal error"
        if not generation_only:
            pattern += r"|\bwarnings?\b|\brejected\b|^Overfull|^Underfull|^Missing character"
        if re.search(pattern, checked, re.IGNORECASE):
            findings.append({"line": number, "text": line})
    return findings


def inspect_log(path: Path, snapshot: Path, *, generation_only: bool = False) -> list[dict]:
    if not path.is_file():
        return [{"file": str(path), "text": "required log is missing"}]
    content = path.read_bytes()
    snapshot.write_bytes(content)
    return [
        {"file": str(path), **finding}
        for finding in diagnostics(content.decode("utf-8", errors="replace"), generation_only=generation_only)
    ]


def check_debug(stem: Path, report_dir: Path) -> list[dict]:
    """Inspect final-pass diagnostics; intermediate rerun warnings are irrelevant."""
    debug = stem.with_name(stem.name + "-debug")
    log = debug.with_suffix(".log")
    issues = inspect_log(log, report_dir / log.name)
    if log.is_file() and "Output written on" not in log.read_text(errors="replace"):
        issues.append({"file": str(log), "text": "PDF completion marker is missing"})
    tex = debug.with_suffix(".tex")
    for artifact in (debug.with_suffix(".pdf"), log):
        if not tex.is_file() or not artifact.is_file():
            issues.append({"file": str(artifact), "text": "required artifact or debug TeX is missing"})
        elif artifact.stat().st_mtime_ns < tex.stat().st_mtime_ns:
            issues.append({"file": str(artifact), "text": "artifact predates debug TeX"})
    idx = debug.with_suffix(".idx")
    if idx.is_file():
        index_log = debug.with_suffix(".ilg")
        issues.extend(inspect_log(index_log, report_dir / index_log.name))
        stamp = debug.with_suffix(".index-sha256")
        if (
            not debug.with_suffix(".ind").is_file()
            or not stamp.is_file()
            or stamp.read_text().strip() != hashlib.sha256(idx.read_bytes()).hexdigest()
        ):
            issues.append({"file": str(idx), "text": "index output is missing or stale"})
    return issues


def run_make(targets: list[Path], log: Path) -> dict:
    command = ["make", "--no-print-directory", *map(str, targets)]
    print("Building " + ", ".join(map(str, targets)), flush=True)
    started = time.monotonic()
    with log.open("w") as output:
        result = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT, check=False)
    return {
        "command": command,
        "exit_code": result.returncode,
        "seconds": round(time.monotonic() - started, 2),
        "log": str(log),
    }


def validate(phase: str, books: dict[str, Path], report_dir: Path) -> dict:
    report = {"phase": phase, "books": list(books), "commands": [], "issues": [], "passed": False}
    issues = report["issues"]
    if phase == "tex":
        # One Make process shares dependency work across the selected books.
        log = report_dir / "tex-build.log"
        result = run_make([stem.with_suffix(".tex") for stem in books.values()], log)
        report["commands"].append(result)
        findings = diagnostics(log.read_text(errors="replace"))
        issues.extend({"file": str(log), **finding} for finding in findings)
        for stem in books.values():
            # Preserve the existing book-build skill's familiar log location.
            stem.parent.mkdir(parents=True, exist_ok=True)
            stem.with_suffix(".tex-build.log").write_bytes(log.read_bytes())
            if not stem.with_suffix(".tex").is_file():
                issues.append({"file": str(stem.with_suffix(".tex")), "text": "TeX output is missing"})
            elif findings:
                # A warning can leave a successful Make target behind. Remove
                # that generated TeX so a no-op retry cannot conceal it.
                stem.with_suffix(".tex").unlink()
    else:
        log = report_dir / "debug-build.log"
        result = run_make([stem.with_name(stem.name + "-debug.pdf") for stem in books.values()], log)
        report["commands"].append(result)
        # Pandoc diagnostics are not repeated in the final LaTeX log. Ignore
        # transient LaTeX warnings here, and inspect each final pass below.
        generation_issues = [
            {"file": str(log), **finding}
            for finding in diagnostics(log.read_text(errors="replace"), generation_only=True)
        ]
        issues.extend(generation_issues)
        if result["exit_code"] == 0:
            latex_lock.acquire_lock(latex_lock.LOCK_DIR, ["validate-book-logs"])
            try:
                for stem in books.values():
                    issues.extend(check_debug(stem, report_dir))
                if generation_issues:
                    for stem in books.values():
                        stem.with_name(stem.name + "-debug.tex").unlink(missing_ok=True)
            finally:
                latex_lock.release_lock(latex_lock.LOCK_DIR)
    report["passed"] = not issues and all(result["exit_code"] == 0 for result in report["commands"])
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("tex", "debug"))
    parser.add_argument("--book", action="append", required=True)
    args = parser.parse_args(argv)
    try:
        available = discover_books(Path("."))
        unknown = set(args.book) - available.keys()
        if unknown:
            raise ValueError(f"unknown books: {', '.join(sorted(unknown))}; available: {', '.join(available)}")
        books = {name: available[name] for name in args.book}
    except (OSError, ValueError) as error:
        parser.error(str(error))
    lock = Path("build/.book-validation.lock")
    latex_lock.acquire_lock(lock, ["validate-book-build", args.phase])
    try:
        root = Path("build/validation")
        root.mkdir(parents=True, exist_ok=True)
        report_dir = Path(tempfile.mkdtemp(prefix=args.phase + "-", dir=root))
        try:
            report = validate(args.phase, books, report_dir)
        except (OSError, ValueError) as error:
            report = {"phase": args.phase, "passed": False, "issues": [{"text": str(error)}], "commands": []}
        report_path = report_dir / "report.json"
        report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
        status = "PASS" if report["passed"] else "FAIL"
        seconds = sum(command["seconds"] for command in report["commands"])
        print(f"{status}: {args.phase}; {len(books)} book(s); {seconds:.2f}s; {len(report['issues'])} diagnostic(s)")
        for issue in report["issues"][:12]:
            print(f"  {issue.get('file', '')}:{issue.get('line', '')}: {issue['text']}")
        if not report["passed"]:
            for command in report["commands"]:
                if command["exit_code"]:
                    print(f"  make exited {command['exit_code']}: {command['log']}")
                    print("\n".join(Path(command["log"]).read_text(errors="replace").splitlines()[-12:]))
        print(f"Report: {report_path}")
        return 0 if report["passed"] else 1
    finally:
        latex_lock.release_lock(lock)


if __name__ == "__main__":
    raise SystemExit(main())
