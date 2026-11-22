#!/usr/bin/env bash
#
# Clone the gitignored build caches from the main checkout into the current
# linked git worktree, using copy-on-write file clones where the filesystem
# supports them (APFS on macOS via clonefile(2), xfs/btrfs on Linux via
# reflink). A fresh worktree starts without .texlive/, .perllib/, */.lake/, or
# build/, and recreating them from scratch costs a TeX Live install plus a full
# mathlib fetch/build; a CoW clone of the same ~15 GB takes seconds and
# shares disk blocks until files diverge.
#
# The source checkout is derived from git itself (--git-common-dir), so this
# works no matter how the worktree was created (git worktree add, agent
# tooling, ...). Each cache directory is copied only when it exists in the
# main checkout and is absent here — the script never merges into or
# overwrites an existing cache, so it is safe to re-run at any time.
#
# CP_COW is the recursive, mtime-preserving copy command. Preserving mtimes
# matters: without them make would consider every cloned artifact stale.
# Override via the environment (the Makefile exports a matching default);
# when the CoW copy fails, the script falls back to a plain cp -Rp.

set -euo pipefail

DRY_RUN=0
FRESH=0
for arg in "$@"; do
  case "${arg}" in
  --dry-run)
    DRY_RUN=1
    ;;
  --fresh)
    # The caller vouches that this worktree was checked out just now (the
    # make-worktree target and the Claude WorktreeCreate hook pass this).
    FRESH=1
    ;;
  *)
    echo "usage: $0 [--dry-run] [--fresh]" >&2
    exit 1
    ;;
  esac
done

log() {
  echo "$*" >&2
}

if ! command -v git >/dev/null 2>&1; then
  log "worktree-caches: git not found; skipping cache clone."
  exit 0
fi

if [[ -z "${CP_COW:-}" ]]; then
  case "$(uname -s)" in
  Darwin)
    # APFS: clonefile(2); cp falls back to copyfile(2) on other filesystems.
    CP_COW="cp -Rpc"
    ;;
  *)
    # xfs/btrfs: reflink clones; --reflink=auto degrades to a plain copy on
    # filesystems without reflink support (e.g. ext4).
    CP_COW="cp -Rp --reflink=auto"
    ;;
  esac
fi
read -r -a cp_cow_cmd <<<"${CP_COW}"

worktree_root="$(git rev-parse --show-toplevel)"
git_dir="$(git rev-parse --path-format=absolute --git-dir)"
common_dir="$(git rev-parse --path-format=absolute --git-common-dir)"

if [[ "${git_dir}" == "${common_dir}" ]]; then
  log "worktree-caches: this is the main checkout; nothing to clone."
  exit 0
fi

# Serialize the existence check and clone, including the fallback deletion.
# The kernel lock is per worktree and is released even after a crashed copier.
# Dry runs remain read-only. A fresh host without Python can provision caches
# later instead of risking concurrent copies during bootstrap.
if [[ "${DRY_RUN}" -eq 0 && "${WORKTREE_CACHES_LOCKED:-0}" != 1 ]]; then
  if ! command -v python3 >/dev/null 2>&1; then
    log "worktree-caches: python3 unavailable; skipping cache clone until setup completes."
    exit 0
  fi
  tool_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  exec python3 "${tool_dir}/with_file_lock.py" "${git_dir}/cache-clone.lock" \
    env WORKTREE_CACHES_LOCKED=1 bash "${tool_dir}/worktree_caches.sh" "$@"
fi

main_root="$(dirname "${common_dir}")"
if [[ ! -d "${main_root}" || "${main_root}" == "${worktree_root}" ]]; then
  log "worktree-caches: cannot locate the main checkout; skipping."
  exit 0
fi

# Gitignored cache roots worth carrying into a worktree, in two classes.
#
# Content-addressed caches are safe to clone into any worktree: the repo-local
# TeX Live tree and the repo-local .perllib (po4a's CPAN modules) are
# source-independent, and Lake validates .lake artifacts by content hash, so a
# clone into a diverged branch just rebuilds what differs.
#
# Derived build outputs (the shared toolchain build/ dir, cabal's
# dist-newstyle, the viewer's esbuild output, each book's build/) are
# governed by make's mtime rules. Cloning them with preserved mtimes into a
# worktree whose sources are OLDER than the clone (an already-existing
# worktree, healed after the main checkout rebuilt) would make stale
# artifacts look fresh and skip regeneration. So they are cloned only when
#
#   - the caller passed --fresh: the worktree was checked out just now, so
#     every tracked source is newer than any cloned artifact and make
#     re-derives whatever is source-dependent, even from a dirty main
#     checkout; or
#   - both checkouts are clean at the same HEAD, so their source states are
#     identical and the artifacts describe exactly the worktree's sources.
#
# Top-level roots come first so nested candidates discovered by the loop
# (e.g. build/build) are already present and skipped.
safe_candidates=(.texlive .perllib)
derived_candidates=(
  build
  dist-newstyle
  tools/formalization-viewer/build
)
for dir in "${main_root}"/*/; do
  name="$(basename "${dir}")"
  case "${name}" in
  build | dist-newstyle | tools)
    continue
    ;;
  esac
  safe_candidates+=("${name}/.lake")
  derived_candidates+=("${name}/build")
done

candidates=("${safe_candidates[@]}")
if [[ "${FRESH}" -eq 1 ]] ||
  { [[ "$(git -C "${worktree_root}" rev-parse HEAD)" == "$(git -C "${main_root}" rev-parse HEAD)" ]] &&
    [[ -z "$(git -C "${worktree_root}" status --porcelain)" ]] &&
    [[ -z "$(git -C "${main_root}" status --porcelain)" ]]; }; then
  candidates+=("${derived_candidates[@]}")
else
  log "worktree-caches: checkouts are not clean at the same HEAD; cloning only" \
    "content-addressed caches (.texlive, .lake), not derived build outputs."
fi

cloned=0
for rel in "${candidates[@]}"; do
  src="${main_root}/${rel}"
  dst="${worktree_root}/${rel}"
  [[ -d "${src}" ]] || continue
  [[ -e "${dst}" ]] && continue
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    log "worktree-caches: would clone ${rel} (${CP_COW})"
    cloned=$((cloned + 1))
    continue
  fi
  mkdir -p "$(dirname "${dst}")"
  log "worktree-caches: cloning ${rel} ..."
  if ! "${cp_cow_cmd[@]}" "${src}" "${dst}"; then
    log "worktree-caches: '${CP_COW}' failed for ${rel}; retrying with plain cp -Rp."
    rm -rf "${dst}"
    cp -Rp "${src}" "${dst}"
  fi
  cloned=$((cloned + 1))
done

if [[ "${cloned}" -eq 0 ]]; then
  log "worktree-caches: caches already present; nothing to do."
elif [[ "${DRY_RUN}" -eq 1 ]]; then
  log "worktree-caches: would clone ${cloned} cache directory(ies) from ${main_root}."
else
  log "worktree-caches: ${cloned} cache directory(ies) cloned from ${main_root}."
fi
