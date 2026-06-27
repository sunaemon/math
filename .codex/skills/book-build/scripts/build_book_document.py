#!/usr/bin/env python3
import argparse
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path


DEFAULT_SOURCE = Path("polish-space/src/polish-space-book.md")
MALFORMED_LOCK_GRACE_SECONDS = 30


def source_to_stem(source):
    if source.suffix != ".md":
        sys.exit(f"error: source must be a .md file: {source}")
    return source.stem


def paths(source):
    stem = source_to_stem(source)
    build = source.parent.parent / "build"
    return {
        "source": source,
        "stem": stem,
        "tex_target": build / f"{stem}.tex",
        "pdf_target": build / f"{stem}.pdf",
        "tex_build_log": build / f"{stem}.tex-build.log",
        "pdf_build_log": build / f"{stem}.pdf-build.log",
        "latex_log": build / f"{stem}.log",
        "pdf_errors": build / f"{stem}.pdf-errors.txt",
        "pdf_status": build / f"{stem}.pdf-build.status",
        "lock_dir": build / f".{stem}-pdf-build.lock",
    }


def require_repo_root(source):
    if not Path("Makefile").is_file():
        sys.exit("error: run from the repository root containing Makefile")
    if not source.is_file():
        sys.exit(f"error: source file does not exist: {source}")
    if not shutil.which("make"):
        sys.exit("error: make is not available on PATH")


def run_make(target, log_path):
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("w", encoding="utf-8", errors="replace") as log:
        log.write(f"$ make {target}\n")
        log.write(f"started: {time.strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        log.flush()
        proc = subprocess.run(
            ["make", str(target)],
            stdout=log,
            stderr=subprocess.STDOUT,
            text=True,
        )
        log.write(f"\nfinished: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        log.write(f"exit-code: {proc.returncode}\n")
    return proc.returncode


def read_lines(path):
    if not path.is_file():
        return []
    return path.read_text(encoding="utf-8", errors="replace").splitlines()


def extract_diagnostics(lines):
    chunks = []
    markers = (
        "error:",
        "Error:",
        "LaTeX Error:",
        "Undefined control sequence",
        "Emergency stop",
        "Fatal error",
        "Runaway argument",
        "Missing ",
        "Extra ",
    )
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        is_diagnostic = (
            stripped.startswith("!")
            or any(marker in line for marker in markers)
            or ("Package " in line and " Error:" in line)
            or stripped.startswith("l.")
            or "make:" in line
            and ("Error" in line or "***" in line)
        )
        if not is_diagnostic:
            i += 1
            continue
        start = max(0, i - 2)
        end = min(len(lines), i + 12)
        chunk_lines = lines[start:end]
        chunks.append("\n".join(chunk_lines).rstrip())
        i = end

    unique = []
    seen = set()
    for chunk in chunks:
        if chunk and chunk not in seen:
            seen.add(chunk)
            unique.append(chunk)
    return unique


def write_diagnostics(path, diagnostics):
    if diagnostics:
        path.write_text("\n\n---\n\n".join(diagnostics) + "\n", encoding="utf-8")
    else:
        path.write_text("No TeX errors extracted.\n", encoding="utf-8")


def timestamp():
    return time.strftime("%Y-%m-%d %H:%M:%S")


def write_pdf_status(p, status, **fields):
    p["pdf_status"].parent.mkdir(parents=True, exist_ok=True)
    if status in {"not-started", "starting", "running", "failed-to-start"}:
        p["pdf_errors"].parent.mkdir(parents=True, exist_ok=True)
        p["pdf_errors"].write_text(
            f"{status}: PDF error extraction is not available for this invocation.\n",
            encoding="utf-8",
        )
    lines = [status, f"updated: {timestamp()}"]
    for key, value in fields.items():
        if value is not None:
            lines.append(f"{key}: {value}")
    p["pdf_status"].write_text("\n".join(lines) + "\n", encoding="utf-8")


def print_diagnostics(label, diagnostics, source):
    if not diagnostics:
        print(f"{label}: no diagnostics extracted from {source}")
        return
    print(f"{label}: extracted {len(diagnostics)} diagnostic block(s) from {source}")
    for block in diagnostics[:5]:
        print()
        print(block)
    if len(diagnostics) > 5:
        print(f"\n... {len(diagnostics) - 5} more block(s) omitted")


def pid_alive(pid):
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def lock_pid(lock_dir):
    try:
        return int((lock_dir / "pid").read_text(encoding="utf-8").strip())
    except Exception:
        return None


def lock_age_seconds(lock_dir):
    try:
        return max(0, time.time() - lock_dir.stat().st_mtime)
    except FileNotFoundError:
        return 0


def remove_lock(lock_dir, reason):
    try:
        shutil.rmtree(lock_dir)
        print(f"pdf: removed stale lock {lock_dir} ({reason})", file=sys.stderr)
    except FileNotFoundError:
        pass


def wait_for_existing(lock_dir):
    waited = False
    while lock_dir.exists():
        waited = True
        pid = lock_pid(lock_dir)
        if pid is None:
            age = lock_age_seconds(lock_dir)
            if age >= MALFORMED_LOCK_GRACE_SECONDS:
                remove_lock(
                    lock_dir,
                    f"missing or unreadable pid after {int(age)} seconds",
                )
                continue
        elif not pid_alive(pid):
            remove_lock(lock_dir, f"pid {pid} is no longer running")
            continue
        time.sleep(2)
    return waited


def acquire_lock(lock_dir):
    lock_dir.parent.mkdir(parents=True, exist_ok=True)
    while True:
        try:
            lock_dir.mkdir()
            (lock_dir / "pid").write_text(f"{os.getpid()}\n", encoding="utf-8")
            (lock_dir / "started").write_text(f"{time.strftime('%Y-%m-%d %H:%M:%S')}\n", encoding="utf-8")
            return
        except FileExistsError:
            wait_for_existing(lock_dir)


def release_lock(lock_dir):
    try:
        shutil.rmtree(lock_dir)
    except FileNotFoundError:
        pass


def pdf_worker(source):
    p = paths(source)
    acquire_lock(p["lock_dir"])
    try:
        write_pdf_status(
            p,
            "running",
            pid=os.getpid(),
            source=p["source"],
            target=p["pdf_target"],
            log=p["pdf_build_log"],
            errors=p["pdf_errors"],
        )
        code = run_make(p["pdf_target"], p["pdf_build_log"])
        diagnostics = extract_diagnostics(read_lines(p["pdf_build_log"]) + read_lines(p["latex_log"]))
        write_diagnostics(p["pdf_errors"], diagnostics)
        status = "passed" if code == 0 else "failed"
        write_pdf_status(
            p,
            status,
            exit_code=code,
            source=p["source"],
            target=p["pdf_target"],
            log=p["pdf_build_log"],
            errors=p["pdf_errors"],
        )
        return code
    finally:
        release_lock(p["lock_dir"])


def start_pdf_worker(source):
    script = Path(__file__).resolve()
    proc = subprocess.Popen(
        [sys.executable, str(script), "--source", str(source), "--pdf-worker"],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        start_new_session=True,
    )
    return proc.pid


def main():
    parser = argparse.ArgumentParser(
        description="Build a repository .md document's TeX target, then serialize and start its PDF target in the background."
    )
    parser.add_argument(
        "--source",
        default=str(DEFAULT_SOURCE),
        help=f".md source file to build; default: {DEFAULT_SOURCE}",
    )
    parser.add_argument("--tex-only", action="store_true")
    parser.add_argument("--wait-pdf", action="store_true")
    parser.add_argument("--pdf-worker", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()

    source = Path(args.source)
    if source.is_absolute():
        try:
            source = source.relative_to(Path.cwd())
        except ValueError:
            sys.exit(f"error: source must live under the repository root: {source}")
    require_repo_root(source)
    p = paths(source)

    if args.pdf_worker:
        return pdf_worker(source)

    write_pdf_status(
        p,
        "not-started",
        reason="TeX target has not completed for this invocation",
        source=p["source"],
        target=p["pdf_target"],
        log=p["pdf_build_log"],
        errors=p["pdf_errors"],
    )
    tex_code = run_make(p["tex_target"], p["tex_build_log"])
    print(f"source: {p['source']}")
    tex_diagnostics = extract_diagnostics(read_lines(p["tex_build_log"]))
    print(f"tex target: {p['tex_target']}")
    print(f"tex status: {'passed' if tex_code == 0 else 'failed'}")
    print(f"tex log: {p['tex_build_log']}")
    print_diagnostics("tex", tex_diagnostics, p["tex_build_log"])
    if tex_code != 0:
        write_pdf_status(
            p,
            "not-started",
            reason=f"TeX target failed with exit code {tex_code}",
            source=p["source"],
            target=p["pdf_target"],
            log=p["pdf_build_log"],
            errors=p["pdf_errors"],
        )
        return tex_code
    if args.tex_only:
        write_pdf_status(
            p,
            "not-started",
            reason="--tex-only was requested",
            source=p["source"],
            target=p["pdf_target"],
            log=p["pdf_build_log"],
            errors=p["pdf_errors"],
        )
        return 0

    waited = wait_for_existing(p["lock_dir"])
    if waited:
        print(f"pdf: waited for previous skill-started {p['stem']} PDF build")

    if args.wait_pdf:
        code = pdf_worker(source)
        print(f"pdf status: {'passed' if code == 0 else 'failed'}")
        print(f"pdf log: {p['pdf_build_log']}")
        print(f"pdf errors: {p['pdf_errors']}")
        if p["pdf_errors"].is_file():
            print(p["pdf_errors"].read_text(encoding="utf-8", errors="replace"))
        return code

    write_pdf_status(
        p,
        "starting",
        source=p["source"],
        target=p["pdf_target"],
        log=p["pdf_build_log"],
        errors=p["pdf_errors"],
    )
    try:
        pid = start_pdf_worker(source)
    except Exception as exc:
        write_pdf_status(
            p,
            "failed-to-start",
            reason=exc,
            source=p["source"],
            target=p["pdf_target"],
            log=p["pdf_build_log"],
            errors=p["pdf_errors"],
        )
        raise
    print(f"pdf: started background build with pid {pid}")
    print(f"pdf log: {p['pdf_build_log']}")
    print(f"pdf status: {p['pdf_status']}")
    print(f"pdf errors: {p['pdf_errors']}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        signal.signal(signal.SIGINT, signal.SIG_DFL)
        raise
