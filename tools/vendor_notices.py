#!/usr/bin/env python3
"""Maintain the third-party components vendored under
``tools/formalization-viewer/vendor/``.

``vendor/manifest.json`` is the single source of truth: each component's pinned
version, SPDX id, upstream project, vendored file list, and the path to its
vendored license file. This script derives everything else from it:

  generate                  (re)write THIRD-PARTY-NOTICES.md from the manifest
  check                     exit non-zero if THIRD-PARTY-NOTICES.md is stale
  set-version <id> <ver>    pin a component's version in the manifest
  fetch-license <id|--all>  download a component's upstream LICENSE (for its
                            pinned version) into its vendored license file

The formalization viewer's About panel reads the same manifest (via the server,
see tools/formalization-viewer/server/repo-version.ts), so the on-page notices
and THIRD-PARTY-NOTICES.md are generated from one source and never drift.

To re-pin a component:

  python tools/vendor_notices.py set-version <id> <version>
  python tools/vendor_notices.py fetch-license <id>
  python tools/vendor_notices.py generate

then refresh the vendored asset files themselves (e.g.
tools/fetch_treesitter_assets.sh for the tree-sitter components).
"""

from __future__ import annotations

import argparse
import json
import sys
import urllib.error
import urllib.request
from pathlib import Path

VENDOR_DIR = Path(__file__).resolve().parent / "formalization-viewer" / "vendor"
MANIFEST = VENDOR_DIR / "manifest.json"
NOTICES = VENDOR_DIR / "THIRD-PARTY-NOTICES.md"

INTRO = (
    "The files in this `vendor/` directory are redistributed third-party\n"
    "components. They are NOT covered by the repository's MIT / CC BY 4.0\n"
    "licenses; each is governed by its own upstream license, reproduced below.\n"
    "\n"
    "This file is generated from `manifest.json` by `tools/vendor_notices.py`;\n"
    "do not edit it by hand. Run `python tools/vendor_notices.py generate` after\n"
    "changing the manifest, and `python tools/vendor_notices.py check` verifies\n"
    "it is up to date."
)


def load_manifest() -> dict:
    return json.loads(MANIFEST.read_text(encoding="utf-8"))


def license_url(component: dict) -> str | None:
    template = component.get("licenseUrl")
    if not template:
        return None
    return template.replace("{version}", str(component["version"]))


def read_license_text(component: dict) -> str:
    rel = component.get("licenseFile")
    if not rel:
        return ""
    path = VENDOR_DIR / rel
    try:
        return path.read_text(encoding="utf-8").strip("\n")
    except OSError:
        return ""


def render_notices(manifest: dict) -> str:
    lines: list[str] = ["# Third-Party Notices", "", INTRO]
    for component in manifest["components"]:
        files = ", ".join(f"`{f}`" for f in component.get("files", []))
        lines += ["", "---", "", f"## {component['name']}", ""]
        lines.append(f"- Version: {component['version']}")
        lines.append(f"- Project: {component['homepage']}")
        lines.append(f"- License: {component['spdx']}")
        if files:
            lines.append(f"- Files: {files}")
        for copyright_line in component.get("copyright", []):
            lines.append(f"- {copyright_line}")
        if component.get("description"):
            lines += ["", component["description"]]
        if component.get("note"):
            lines += ["", component["note"]]
        rel = component.get("licenseFile")
        if component.get("licenseInline", True):
            text = read_license_text(component)
            if text:
                lines += ["", "```", text, "```"]
        elif rel:
            lines += ["", f"License text: see [{rel}]({rel})."]
    return "\n".join(lines) + "\n"


def cmd_generate(_args: argparse.Namespace) -> int:
    NOTICES.write_text(render_notices(load_manifest()), encoding="utf-8")
    print(f"wrote {NOTICES.relative_to(VENDOR_DIR.parent.parent.parent)}")
    return 0


def cmd_check(_args: argparse.Namespace) -> int:
    expected = render_notices(load_manifest())
    actual = NOTICES.read_text(encoding="utf-8") if NOTICES.exists() else ""
    if expected == actual:
        return 0
    print(
        "THIRD-PARTY-NOTICES.md is out of date; run `python tools/vendor_notices.py generate`.",
        file=sys.stderr,
    )
    return 1


def find_component(manifest: dict, component_id: str) -> dict:
    for component in manifest["components"]:
        if component["id"] == component_id:
            return component
    sys.exit(f"unknown component id: {component_id}")


def cmd_set_version(args: argparse.Namespace) -> int:
    manifest = load_manifest()
    find_component(manifest, args.id)["version"] = args.version
    MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"set {args.id} version = {args.version}")
    return 0


def fetch_one(component: dict) -> bool:
    url = license_url(component)
    rel = component.get("licenseFile")
    if not url or not rel:
        print(f"  {component['id']}: no licenseUrl/licenseFile; skipping")
        return False
    if not url.startswith("https://"):
        print(f"  {component['id']}: licenseUrl must be https; skipping")
        return False
    try:
        with urllib.request.urlopen(url, timeout=30) as response:  # noqa: S310
            text = response.read().decode("utf-8")
    except (urllib.error.URLError, TimeoutError) as error:
        print(f"  {component['id']}: fetch failed ({error}); leaving {rel} unchanged")
        return False
    (VENDOR_DIR / rel).write_text(text, encoding="utf-8")
    print(f"  {component['id']}: {len(text)} bytes -> {rel}")
    return True


def cmd_fetch_license(args: argparse.Namespace) -> int:
    manifest = load_manifest()
    components = manifest["components"] if args.all else [find_component(manifest, args.id)]
    for component in components:
        fetch_one(component)
    return 0


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("generate", help="regenerate THIRD-PARTY-NOTICES.md from the manifest")
    sub.add_parser("check", help="exit non-zero if THIRD-PARTY-NOTICES.md is stale")

    set_version = sub.add_parser("set-version", help="pin a component's version")
    set_version.add_argument("id")
    set_version.add_argument("version")

    fetch = sub.add_parser("fetch-license", help="download a component's upstream LICENSE")
    group = fetch.add_mutually_exclusive_group(required=True)
    group.add_argument("id", nargs="?")
    group.add_argument("--all", action="store_true", help="fetch every component's license")

    args = parser.parse_args(argv)
    return {
        "generate": cmd_generate,
        "check": cmd_check,
        "set-version": cmd_set_version,
        "fetch-license": cmd_fetch_license,
    }[args.command](args)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
