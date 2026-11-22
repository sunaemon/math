#!/usr/bin/env bash
#
# Claude Code WorktreeCreate hook: create a linked git worktree and CoW-clone
# the build caches into it via tools/worktree_caches.sh.
#
# Configuring a WorktreeCreate hook replaces Claude Code's default worktree
# creation, so this script owns the whole job. Contract (see
# https://code.claude.com/docs/en/hooks#worktreecreate): the hook receives
# JSON on stdin ({cwd, name, ...} where cwd is the main checkout), must print
# the new worktree's absolute path as the last non-empty line of stdout, and
# a non-zero exit fails the creation. All other output goes to stderr.
#
# Worktrees are created as siblings of the main checkout under
# <main>-worktrees/<branch>, branching from the current HEAD. The cache clone
# is best-effort: a fresh worktree without caches is slow but correct, so its
# failure never fails worktree creation.

set -euo pipefail

log() {
  echo "$*" >&2
}

payload="$(cat 2>/dev/null || true)"

json_field() {
  if command -v jq >/dev/null 2>&1; then
    printf '%s' "${payload}" | jq -r --arg key "$1" '.[$key] // empty' 2>/dev/null || true
  elif command -v python3 >/dev/null 2>&1; then
    printf '%s' "${payload}" | python3 -c '
import json, sys
try:
    value = json.load(sys.stdin).get(sys.argv[1], "")
except Exception:
    value = ""
print(value if isinstance(value, str) else "")
' "$1" 2>/dev/null || true
  fi
}

main_root="$(json_field cwd)"
[[ -n "${main_root}" && -d "${main_root}" ]] || main_root="${PWD}"
main_root="$(git -C "${main_root}" rev-parse --show-toplevel)"

# Reduce the supplied name to branch-safe characters, then let git validate
# the result as a whole ref: dots, slashes, and dashes survive the character
# filter but can still form invalid branch names (foo.lock, a..b, a trailing
# slash or dot, a leading dash). Anything invalid falls back to a generated
# name instead of failing the worktree creation.
name="$(json_field name)"
name="${name//[^A-Za-z0-9._\/-]/-}"
if [[ -z "${name}" ]] || ! git check-ref-format --branch "${name}" >/dev/null 2>&1; then
  name="wt-$(date +%Y%m%d-%H%M%S)"
fi

# Probe branch creation instead of pre-checking refs: an exact-ref check
# misses ref-namespace conflicts (an existing branch `feat` blocks creating
# `feat/nested` and vice versa), which would fail the hook outright. Try the
# requested name, a few -N variants, then a generated slash-free name that
# can only collide exactly.
worktrees_root="${main_root}-worktrees"
mkdir -p "${worktrees_root}"
dir=""
for branch in "${name}" "${name}-2" "${name}-3" "wt-$(date +%Y%m%d-%H%M%S)-$$"; do
  candidate="${worktrees_root}/${branch}"
  [[ -e "${candidate}" ]] && continue
  if git -C "${main_root}" worktree add -b "${branch}" "${candidate}" >&2; then
    dir="${candidate}"
    break
  fi
done
if [[ -z "${dir}" ]]; then
  log "claude-worktree-create: could not create a worktree branch for '${name}'."
  exit 1
fi

if [[ -x "${main_root}/tools/worktree_caches.sh" ]]; then
  if ! (cd "${dir}" && "${main_root}/tools/worktree_caches.sh" --fresh >&2); then
    log "claude-worktree-create: cache clone failed; continuing with a cold worktree."
  fi
fi

printf '%s\n' "${dir}"
