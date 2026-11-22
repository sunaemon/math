#!/usr/bin/env bash
# Build only the two public English mounts, upload them, and trigger lightweight CD.
set -euo pipefail
cd "$(dirname "$0")/.."
tag="${1:?Usage: tools/publish_pages_local.sh RELEASE_TAG [--without-hover]}"
flags=
case "${2:-}" in
"") ;;
--without-hover) flags=--skip-lsp-cache ;;
*)
  echo "Unknown option: $2" >&2
  exit 2
  ;;
esac
make chapter-pdfs BOOKS="polish-space-book polish-space-ch1"
site=build/pages-local
full=build/pages-local-full
make dist BOOKLINK_PROJECT=polish-space-ch1 BOOKLINK_DIST_DIR="$site" BOOKLINK_DIST_FLAGS="$flags"
make dist BOOKLINK_PROJECT=polish-space BOOKLINK_DIST_DIR="$full" BOOKLINK_DIST_FLAGS="$flags"
mv "$full/polish-space" "$site/polish-space"
# The canonical checkout points at the private source repo; public links use its export.
python3 - "$site" "$flags" <<'PY'
import json
import shutil
from pathlib import Path
import sys
for book in ("polish-space", "polish-space-ch1"):
    path = Path(sys.argv[1]) / book / "manifest.json"
    data = json.loads(path.read_text())
    data["repository"] = "https://github.com/sunaemon/math"
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")
    if sys.argv[2] == "--skip-lsp-cache":
        shutil.rmtree(path.parent / "lsp-cache", ignore_errors=True)
PY
COPYFILE_DISABLE=1 tar -czf build/pages.tar.gz -C "$site" .
digest="$(shasum -a 256 build/pages.tar.gz | cut -d ' ' -f 1)"
gh release create "$tag" build/pages.tar.gz --repo sunaemon/math --target main \
  --title "Web viewer assets: $tag" --notes "Locally built English viewer. SHA-256: $digest" --prerelease
gh workflow run deploy-pages.yml --repo sunaemon/math \
  -f "artifact_tag=$tag" -f "sha256=$digest"
printf 'Deployment requested: %s (%s)\n' "$tag" "$digest"
