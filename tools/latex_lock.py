#!/usr/bin/env python3
"""Run a build command under a repository-local LaTeX lock.

Several PDF targets write auxiliary files under build/ and invoke LuaLaTeX
for long enough that overlapping runs can produce misleading failures.  The
lock is intentionally simple and filesystem based so it works anywhere the
Makefile runs.
"""

import argparse
import os
import secrets
import shutil
import subprocess
import sys
import time
from pathlib import Path


LOCK_DIR = Path("build/.latex-build.lock")
MALFORMED_LOCK_GRACE_SECONDS = 30


def _max_lock_age() -> int:
    raw = os.environ.get("LATEX_LOCK_MAX_AGE_SECONDS")
    try:
        value = int(raw) if raw else 0
    except ValueError:
        value = 0
    return value if value > 0 else 3600


# Backstop for a lock whose recorded pid still appears alive but never clears.
# After PID recycling a crashed holder's pid can be reused by an unrelated live
# process, so liveness alone would wedge every future build. The lock only ever
# wraps a single LuaLaTeX/makeindex invocation, so an hour is far longer than any
# real holder; override with LATEX_LOCK_MAX_AGE_SECONDS for unusual setups.
MAX_LOCK_AGE_SECONDS = _max_lock_age()


def timestamp() -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S")


def pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def lock_pid(lock_dir: Path) -> int | None:
    try:
        return int((lock_dir / "pid").read_text(encoding="utf-8").strip())
    except Exception:
        return None


def lock_age_seconds(lock_dir: Path) -> float:
    try:
        return max(0.0, time.time() - lock_dir.stat().st_mtime)
    except FileNotFoundError:
        return 0.0


def remove_lock(lock_dir: Path, expected_pid: int | None, reason: str) -> None:
    # Atomically claim the (apparently stale) lock by renaming it aside before
    # removing it. A directory rename has a single winner, so two waiters that
    # both observe the same dead holder cannot both delete the lock and then
    # both recreate it (which would break mutual exclusion). The destination is
    # unique per claimer to avoid any rename-target collision.
    staged = lock_dir.with_name(f"{lock_dir.name}.stale.{os.getpid()}.{secrets.token_hex(4)}")
    try:
        os.rename(lock_dir, staged)
    except (FileNotFoundError, OSError):
        return  # already claimed/removed by another waiter, or recreated
    # Guard against having claimed a lock that a live owner recreated between our
    # staleness check and this rename: if the directory we grabbed now belongs to
    # a different, live pid, put it back instead of deleting someone else's lock.
    grabbed = lock_pid(staged)
    if grabbed is not None and grabbed != expected_pid and pid_alive(grabbed):
        try:
            os.rename(staged, lock_dir)
            return
        except OSError:
            pass  # slot already retaken; discard our copy below
    shutil.rmtree(staged, ignore_errors=True)
    print(f"latex-lock: removed stale lock {lock_dir} ({reason})", file=sys.stderr)


def wait_for_existing(lock_dir: Path) -> None:
    while lock_dir.exists():
        pid = lock_pid(lock_dir)
        if pid is None:
            age = lock_age_seconds(lock_dir)
            if age >= MALFORMED_LOCK_GRACE_SECONDS:
                remove_lock(
                    lock_dir,
                    None,
                    f"missing or unreadable pid after {int(age)} seconds",
                )
                continue
        elif not pid_alive(pid):
            remove_lock(lock_dir, pid, f"pid {pid} is no longer running")
            continue
        else:
            age = lock_age_seconds(lock_dir)
            if age >= MAX_LOCK_AGE_SECONDS:
                # Passing expected_pid=pid lets remove_lock delete a lock the
                # apparently-live holder is still on: its restore guard only
                # protects a *different* live pid, so a recycled-pid holder is
                # reclaimed while a genuine new holder is left intact.
                remove_lock(
                    lock_dir,
                    pid,
                    f"held by pid {pid} for {int(age)} seconds (exceeds max age)",
                )
                continue
        time.sleep(1)


def acquire_lock(lock_dir: Path, command: list[str]) -> None:
    lock_dir.parent.mkdir(parents=True, exist_ok=True)
    while True:
        try:
            lock_dir.mkdir()
            (lock_dir / "pid").write_text(f"{os.getpid()}\n", encoding="utf-8")
            (lock_dir / "started").write_text(f"{timestamp()}\n", encoding="utf-8")
            (lock_dir / "command").write_text(" ".join(command) + "\n", encoding="utf-8")
            return
        except FileExistsError:
            wait_for_existing(lock_dir)


def release_lock(lock_dir: Path) -> None:
    # Only remove the lock if we still own it. If our lock was reclaimed as stale
    # and recreated by another process — for instance our pid file went briefly
    # unreadable past the grace window — the directory now belongs to that
    # process and must not be deleted here. Stage it aside with an atomic rename
    # and re-check ownership before removing, so a concurrent reclaim/recreate
    # cannot make us delete a different holder's lock.
    if lock_pid(lock_dir) != os.getpid():
        return
    staged = lock_dir.with_name(f"{lock_dir.name}.release.{os.getpid()}.{secrets.token_hex(4)}")
    try:
        os.rename(lock_dir, staged)
    except (FileNotFoundError, OSError):
        return  # already removed, or reclaimed by another waiter
    if lock_pid(staged) == os.getpid():
        shutil.rmtree(staged, ignore_errors=True)
        return
    # The directory we grabbed is no longer ours; restore it for its owner.
    try:
        os.rename(staged, lock_dir)
    except OSError:
        shutil.rmtree(staged, ignore_errors=True)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Serialize LuaLaTeX/makeindex commands that share the build directory."
    )
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()

    command = args.command
    if command[:1] == ["--"]:
        command = command[1:]
    if not command:
        parser.error("missing command to run")

    acquire_lock(LOCK_DIR, command)
    try:
        proc = subprocess.run(command)
        return proc.returncode
    finally:
        release_lock(LOCK_DIR)


if __name__ == "__main__":
    raise SystemExit(main())
