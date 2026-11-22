#!/usr/bin/env python3
"""Extract locked Debian support packages for an unprivileged Codex container.

This supplements the image's system TeX and Perl; it is not a TeX Live installer
and never changes apt sources or the system package database.
"""

import hashlib
import json
import os
import platform
import subprocess
import sys
from pathlib import Path


def main():
    release = platform.freedesktop_os_release()
    if release.get("ID") != "debian" or release.get("VERSION_ID") != "13":
        sys.exit("Rootless support packages require Debian 13; install system dependencies with apt on other images.")
    if platform.machine() != "x86_64":
        sys.exit("Rootless support packages currently require x86_64.")
    root = Path(__file__).resolve().parents[1]
    lock_path = root / "tools/codex-debian-packages.json"
    lock = json.loads(lock_path.read_text())
    prefix = root / "build/codex/system"
    downloads = root / "build/codex/downloads"
    downloads.mkdir(parents=True, exist_ok=True)
    prefix.mkdir(parents=True, exist_ok=True)
    stamp = prefix / ".packages-sha256"
    fingerprint = hashlib.sha256(lock_path.read_bytes()).hexdigest()
    if stamp.exists() and stamp.read_text().strip() == fingerprint:
        return
    for package in lock["packages"]:
        archive = downloads / Path(package["Filename"]).name
        if not archive.exists():
            temporary = archive.with_suffix(".tmp")
            subprocess.run(
                [
                    "curl",
                    "-fsSL",
                    "--retry",
                    "3",
                    "--max-time",
                    "300",
                    lock["source"] + package["Filename"],
                    "-o",
                    str(temporary),
                ],
                check=True,
            )
            temporary.replace(archive)
        with archive.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        if digest != package["SHA256"]:
            sys.exit(f"Checksum mismatch: {archive}; remove this archive and retry.")
        print(f"Extracting {package['Package']} {package['Version']}", flush=True)
        subprocess.run(["dpkg-deb", "--extract", str(archive), str(prefix)], check=True)
    # Debian's /usr/bin links normally depend on package post-install scripts.
    # Point these wrappers at their extracted scripts without modifying /usr.
    scripts = {
        "texfot": "usr/share/texlive/texmf-dist/scripts/texfot/texfot.pl",
        "luaotfload-tool": "usr/share/texlive/texmf-dist/scripts/luaotfload/luaotfload-tool.lua",
    }
    for name, target in scripts.items():
        link = prefix / "usr/bin" / name
        link.unlink(missing_ok=True)
        link.symlink_to(os.path.relpath(prefix / target, link.parent))
    stamp.write_text(fingerprint + "\n")


if __name__ == "__main__":
    main()
