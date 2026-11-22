#!/usr/bin/env python3
"""Execute a command under a kernel file lock on macOS/Linux.

The descriptor survives exec so the lock lasts as long as the actual command,
with no stale-PID cleanup or check/delete window. The lock file stays in place;
removing it could let a new caller lock a different inode concurrently.
"""

import fcntl
import os
import sys


def main():
    if len(sys.argv) < 3:
        sys.exit("usage: with_file_lock.py LOCK_PATH COMMAND [ARG...]")
    fd = os.open(sys.argv[1], os.O_CREAT | os.O_RDWR, 0o600)
    fcntl.flock(fd, fcntl.LOCK_EX)
    os.set_inheritable(fd, True)
    os.execvp(sys.argv[2], sys.argv[2:])


if __name__ == "__main__":
    main()
