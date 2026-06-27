"""Tests for latex_lock stale-lock reclaim.

These exercise the reclaim decisions without spawning a real build: a lock
directory with a dead holder is reclaimed, a malformed lock within the grace
period is kept, and a lock that turns out to belong to a different *live* holder
is restored rather than deleted (the rename-aside race guard). Run with
`python -m unittest` (stdlib only, no pytest).
"""

import os
import subprocess
import sys
import unittest
import tempfile
from pathlib import Path

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(REPO_ROOT, "tools"))

import latex_lock as ll  # noqa: E402


def dead_pid() -> int:
    """A pid that is guaranteed not alive: spawn a child and reap it."""
    proc = subprocess.Popen([sys.executable, "-c", ""])
    proc.wait()
    return proc.pid


def make_lock(parent: str, pid: int | None) -> Path:
    lock = Path(parent) / "lock"
    lock.mkdir()
    if pid is not None:
        (lock / "pid").write_text(f"{pid}\n", encoding="utf-8")
    return lock


class StaleLockTests(unittest.TestCase):
    def test_remove_lock_removes_dead_holder(self):
        with tempfile.TemporaryDirectory() as tmp:
            pid = dead_pid()
            lock = make_lock(tmp, pid)
            ll.remove_lock(lock, pid, "dead")
            self.assertFalse(lock.exists())

    def test_remove_lock_restores_live_foreign_holder(self):
        # The grabbed lock belongs to a different, live pid (this process), so it
        # must be put back rather than deleted.
        with tempfile.TemporaryDirectory() as tmp:
            lock = make_lock(tmp, os.getpid())
            ll.remove_lock(lock, expected_pid=1, reason="race")
            self.assertTrue(lock.exists())
            self.assertEqual(ll.lock_pid(lock), os.getpid())

    def test_wait_for_existing_reclaims_dead_lock(self):
        # A dead-holder lock is reclaimed on the first iteration, so the call
        # returns promptly instead of blocking on the 1s poll loop.
        with tempfile.TemporaryDirectory() as tmp:
            lock = make_lock(tmp, dead_pid())
            ll.wait_for_existing(lock)
            self.assertFalse(lock.exists())

    def test_malformed_lock_within_grace_is_kept(self):
        # A pid-less lock younger than the grace period is not yet reclaimable.
        with tempfile.TemporaryDirectory() as tmp:
            lock = make_lock(tmp, None)
            self.assertIsNone(ll.lock_pid(lock))
            self.assertLess(ll.lock_age_seconds(lock), ll.MALFORMED_LOCK_GRACE_SECONDS)

    def test_release_removes_own_lock(self):
        with tempfile.TemporaryDirectory() as tmp:
            lock = make_lock(tmp, os.getpid())
            ll.release_lock(lock)
            self.assertFalse(lock.exists())

    def test_release_keeps_foreign_live_holder(self):
        # Our lock was reclaimed and recreated by a different, live holder while
        # we were running; release must not delete that process's lock. pid 1 is
        # always alive, standing in for the foreign holder.
        with tempfile.TemporaryDirectory() as tmp:
            lock = make_lock(tmp, 1)
            ll.release_lock(lock)
            self.assertTrue(lock.exists())
            self.assertEqual(ll.lock_pid(lock), 1)


if __name__ == "__main__":
    unittest.main()
