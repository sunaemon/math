#!/usr/bin/env python3
"""Run incremental Lake builds and summarize only this invocation's diagnostics.

Use make validate-lean LEAN_PROJECTS=polish-space
LEAN_MODULES=PolishSpaceBook.Module for an iteration, omitting LEAN_MODULES
for the complete project's default targets. No cache download is requested.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import tempfile
import time
import tomllib
from pathlib import Path

import latex_lock


def select_projects(root: Path, names: list[str], modules: list[str]) -> list[Path]:
    available = {path.parent.name: path.parent for path in root.glob("*/lakefile.toml")}
    unknown = set(names) - available.keys()
    if unknown:
        raise ValueError(f"unknown Lean projects: {', '.join(sorted(unknown))}")
    projects = [available[name] for name in dict.fromkeys(names)] if names else list(available.values())
    if not projects:
        raise ValueError("no Lean projects found")
    if modules and len(projects) != 1:
        raise ValueError("module checks require exactly one LEAN_PROJECTS entry")
    for module in modules:
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", module):
            raise ValueError(f"invalid module name: {module}")
        project = projects[0]
        config = tomllib.loads((project / "lakefile.toml").read_text())
        source = Path(*module.split(".")).with_suffix(".lean")
        if not any((project / lib.get("srcDir", ".") / source).is_file() for lib in config.get("lean_lib", [])):
            raise ValueError(f"module source not found in {project}: {module}")
    return projects


def run_build(project: Path, modules: list[str], directory: Path) -> dict:
    log = directory / f"{project.name}.lean-build.log"
    command = ["lake", "build", *dict.fromkeys(modules)]
    print(f"Checking {project}: {', '.join(modules) if modules else 'default targets'}", flush=True)
    started = time.monotonic()
    with log.open("w") as output:
        result = subprocess.run(command, cwd=project, stdout=output, stderr=subprocess.STDOUT, check=False)
    issues = []
    for number, line in enumerate(log.read_text(errors="replace").splitlines(), 1):
        # Lake replays cached Lean warnings as well as reporting new ones.
        if re.search(r"\b(?:warning|error):|^⚠", line, re.IGNORECASE):
            issues.append({"file": str(log), "line": number, "text": line})
    return {
        "command": command,
        "cwd": str(project),
        "exit_code": result.returncode,
        "seconds": round(time.monotonic() - started, 2),
        "log": str(log),
        "issues": issues,
        "passed": result.returncode == 0 and not issues,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", action="append", default=[])
    parser.add_argument("--module", action="append", default=[])
    args = parser.parse_args(argv)
    try:
        projects = select_projects(Path("."), args.project, args.module)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    lock = Path("build/.lean-validation.lock")
    latex_lock.acquire_lock(lock, ["validate-lean"])
    try:
        output = Path("build/validation")
        output.mkdir(parents=True, exist_ok=True)
        directory = Path(tempfile.mkdtemp(prefix="lean-", dir=output))
        report = {"phase": "lean", "passed": False, "commands": [], "issues": []}
        try:
            for project in projects:
                result = run_build(project, args.module, directory)
                report["commands"].append(result)
                report["issues"].extend(result["issues"])
            report["passed"] = all(result["passed"] for result in report["commands"])
        except OSError as error:
            report["issues"].append({"text": str(error)})
        path = directory / "report.json"
        path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
        seconds = sum(result["seconds"] for result in report["commands"])
        print(f"{'PASS' if report['passed'] else 'FAIL'}: lean; {seconds:.2f}s; {len(report['issues'])} diagnostic(s)")
        for issue in report["issues"][:12]:
            print(f"  {issue.get('file', '')}:{issue.get('line', '')}: {issue['text']}")
        for result in report["commands"]:
            if result["exit_code"]:
                print(f"  lake exited {result['exit_code']}: {result['log']}")
                print("\n".join(Path(result["log"]).read_text(errors="replace").splitlines()[-12:]))
        print(f"Report: {path}")
        return 0 if report["passed"] else 1
    finally:
        latex_lock.release_lock(lock)


if __name__ == "__main__":
    raise SystemExit(main())
