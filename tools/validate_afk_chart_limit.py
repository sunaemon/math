#!/usr/bin/env python3
"""Check the book's chart adapter using AFK's pinned, separate toolchain."""

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

REVISION = "348f38d92c3cd67968ccfb79102f0c7a96d0be33"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc3"
REPOSITORY = "https://github.com/cameronfreer/vaught-conjecture-counterexample.git"
ROOT = Path(__file__).resolve().parents[1]


def run(*args: str, cwd: Path) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, default=ROOT / "build/afk-validation")
    parser.add_argument("--prepare-only", action="store_true")
    args = parser.parse_args()
    source = args.source_dir.resolve()
    if not source.exists():
        source.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "clone", "--filter=blob:none", "--no-checkout", REPOSITORY, str(source)], check=True)
        subprocess.run(["git", "checkout", "--detach", REVISION], cwd=source, check=True)
    if run("git", "rev-parse", "HEAD", cwd=source) != REVISION:
        raise SystemExit("AFK checkout does not match the pinned revision")
    if (source / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise SystemExit("AFK toolchain does not match the pinned version")
    run(
        "git",
        "diff",
        "--exit-code",
        "HEAD",
        "--",
        "VaughtConjecture",
        "lean-toolchain",
        "lake-manifest.json",
        cwd=source,
    )
    for package in json.loads((source / "lake-manifest.json").read_text())["packages"]:
        dependency = source / ".lake/packages" / package["name"]
        if dependency.exists():
            if run("git", "rev-parse", "HEAD", cwd=dependency) != package["rev"]:
                raise SystemExit(f"Dependency revision differs: {package['name']}")
            run("git", "diff", "--exit-code", "HEAD", cwd=dependency)
    destination = source / "BookAFK"
    destination.mkdir(exist_ok=True)
    shutil.copyfile(
        ROOT / "polish-space/lean/PolishSpaceBook/ChartAmalgamation.lean", destination / "ChartAmalgamation.lean"
    )
    shutil.copyfile(ROOT / "polish-space/vendor/afk-validation/ChartClass.lean", destination / "ChartClass.lean")
    lakefile = source / "lakefile.toml"
    config = lakefile.read_text()
    original = subprocess.check_output(["git", "show", "HEAD:lakefile.toml"], cwd=source, text=True)
    expected = (
        original + '\n[[lean_lib]]\nname = "BookAFK"\nglobs = ["BookAFK.*"]\nleanOptions = { warningAsError = true }\n'
    )
    if config not in (original, expected):
        raise SystemExit("Unexpected changes to AFK's Lake configuration")
    lakefile.write_text(expected)
    if args.prepare_only:
        return
    elan = shutil.which("elan") or str(Path.home() / ".elan/bin/elan")
    command = [elan, "run", TOOLCHAIN, "lake", "build", "BookAFK.ChartClass"]
    reports = ROOT / "build/validation"
    reports.mkdir(parents=True, exist_ok=True)
    report_dir = Path(tempfile.mkdtemp(prefix="afk-", dir=reports))
    log = report_dir / "lean-build.log"
    print(f"Checking pinned AFK chart limit; log: {log}", flush=True)
    started = time.monotonic()
    with log.open("w") as stream:
        result = subprocess.run(command, cwd=source, stdout=stream, stderr=subprocess.STDOUT, check=False)
        axioms = None
        axiom_exit = None
        if result.returncode == 0:
            probe = source / "BookAFKEndpointCheck.lean"
            probe.write_text("import BookAFK.ChartClass\n#print axioms BookAFK.exists_stage_chart_limit\n")
            checked = subprocess.run(
                [elan, "run", TOOLCHAIN, "lake", "env", "lean", probe.name],
                cwd=source,
                capture_output=True,
                text=True,
                check=False,
            )
            stream.write(checked.stdout + checked.stderr)
            axiom_exit = checked.returncode
            found = re.search(r"depends on axioms: \[([^\]]*)\]", checked.stdout)
            if found:
                axioms = [name.strip() for name in found[1].split(",") if name.strip()]
    elapsed = time.monotonic() - started
    report = {
        "revision": REVISION,
        "toolchain": TOOLCHAIN,
        "source_directory": str(source),
        "command": command,
        "exit_code": result.returncode,
        "seconds": elapsed,
        "axiom_check_exit_code": axiom_exit,
        "axioms": axioms,
        "passed": result.returncode == 0
        and axiom_exit == 0
        and axioms is not None
        and set(axioms) <= {"propext", "Classical.choice", "Quot.sound"},
        "log": str(log),
        "sources": {
            path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in (destination / "ChartAmalgamation.lean", destination / "ChartClass.lean")
        },
    }
    report_path = report_dir / "report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{'PASS' if report['passed'] else 'FAIL'}: AFK; {elapsed:.2f}s; report: {report_path}")
    if not report["passed"]:
        raise SystemExit(result.returncode or 1)


if __name__ == "__main__":
    main()
