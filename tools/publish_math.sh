#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: tools/publish_math.sh DEST BOOK [BOOK...]

Copy a public subset of this repository to DEST, containing only the named book
projects (for example polish-space-ch1) plus the shared build and tooling files.
Every other book project is omitted.

Each published book keeps its symlinks into the omitted books verbatim. The files
those symlinks resolve to, and the Lean chapter modules the book formalizes, are
copied as real files at their original paths, so the published tree is
self-contained and builds with no on-the-fly file rewriting. BOOK names are
book-project directories; run `make list-books` to see them.
EOF
}

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  usage
  exit 0
fi
if [[ $# -lt 2 ]]; then
  usage
  exit 2
fi

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
script_abs="$script_dir/$(basename "${BASH_SOURCE[0]}")"
src_root="$(cd "$script_dir/.." && git rev-parse --show-toplevel)"
cd "$src_root"

dest="$1"
shift
books=("$@")

mkdir -p "$dest"
dest_abs="$(cd "$dest" && pwd -P)"
src_abs="$(pwd -P)"
if [[ "$dest_abs" == "$src_abs" ]]; then
  echo "publish_math.sh: destination must differ from source: $dest_abs" >&2
  exit 2
fi

# Every book-project directory is the top-level dir of a src/<stem>.json manifest.
all_books="$(for m in */src/*.json; do [[ -e "$m" ]] && printf '%s\n' "${m%%/*}"; done | sort -u)"
for b in "${books[@]}"; do
  printf '%s\n' "$all_books" | grep -qx -- "$b" || {
    echo "publish_math.sh: not a book project: $b (run 'make list-books')" >&2
    exit 2
  }
done
requested="$(printf '%s\n' "${books[@]}" | sort -u)"
omitted="$(comm -23 <(printf '%s\n' "$all_books") <(printf '%s\n' "$requested"))"

tmpdir="$(mktemp -d "${TMPDIR:-/tmp}/publish-math.XXXXXX")"
trap 'rm -rf "$tmpdir"' EXIT

file_list="$tmpdir/files.txt"
script_rel="${script_abs#"$src_root"/}"

# Stage every tracked file except todo.md and the omitted book directories.
# Symlinks are copied verbatim (rsync -a); their referents are materialized below.
{
  git ls-files
  printf '%s\n' "$script_rel"
} | awk -v omitted="$omitted" '
    BEGIN { n = split(omitted, a, "\n"); for (i = 1; i <= n; i++) if (a[i] != "") omit[a[i]] = 1 }
    $0 == "todo.md" { next }
    { top = $0; sub(/\/.*/, "", top); if (top in omit) next }
    !seen[$0]++
  ' >"$file_list"

rsync -a --files-from="$file_list" "$src_root"/ "$tmpdir/stage"/

# The private source README should open the full private repo in Codespaces, but
# the public mirror should open itself.
python3 - "$tmpdir/stage/README.md" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
text = text.replace(
    "https://codespaces.new/sunaemon/math-private",
    "https://codespaces.new/sunaemon/math",
)
path.write_text(text, encoding="utf-8")
PY

# Materialize the omitted-book files each published book reaches into, so the
# published tree is self-contained.
python3 - "$src_root" "$tmpdir/stage" "${books[@]}" <<'PY'
import shutil
import subprocess
import sys
from pathlib import Path

repo = Path(sys.argv[1])
stage = Path(sys.argv[2])
books = set(sys.argv[3:])


def copy_real(src: Path, rel: str) -> None:
    dst = stage / rel
    dst.parent.mkdir(parents=True, exist_ok=True)
    if src.is_dir():
        shutil.copytree(src, dst, dirs_exist_ok=True)
    else:
        shutil.copy2(src, dst)


# Resolve every tracked symlink that points into an omitted book: copy the real
# referent to the same path in the stage, so the preserved symlink resolves
# there too. A published book reaches all the omitted-book files it needs (TeX
# support, chapter sources, chapter Lean modules) through such symlinks, so this
# is the only materialization required.
tracked = subprocess.run(
    ["git", "-C", str(repo), "ls-files", "-z"],
    capture_output=True, text=True, check=True,
).stdout.split("\0")
for rel in filter(None, tracked):
    path = repo / rel
    if not path.is_symlink():
        continue
    target = path.resolve()
    try:
        target_rel = target.relative_to(repo)
    except ValueError:
        continue  # points outside the repo; leave the symlink as authored
    if target_rel.parts[0] in books:
        continue  # target lives in a published book and is already staged
    copy_real(target, str(target_rel))
PY

rsync -a --delete --filter='P /.git/***' --filter='P /.texlive/***' "$tmpdir/stage"/ "$dest_abs"/

echo "Published ${books[*]} to $dest_abs"
